-- Prove2me | solution 1 for OAI.OneWayLiveness.deterministic_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:12:26.466784+00:00
-- url     : https://prove2.me/submissions/3e1cb994-eb29-46ea-8118-f14b6d8591fa

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Recognition.lean:L78-L95
-- (upload_full_project.md Phase 4): solution for node OAI.OneWayLiveness.deterministic_lower_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization
import Definitions.Def_OAI_Combinatorics_Automata_Network
import Definitions.Def_OAI_Combinatorics_Automata_Rank
import Definitions.Def_OAI_Combinatorics_Automata_Diagram
import Definitions.Def_OAI_Combinatorics_Automata_Diagrams
import Definitions.Def_OAI_Combinatorics_Automata_Corners
import Definitions.Def_OAI_Combinatorics_Automata_Relations
import Definitions.Def_OAI_Combinatorics_Automata_RankLoss
import Definitions.Def_OAI_Combinatorics_Automata_Recognition
import Theorems.Thm_OAI_OneWayLiveness_CellNetwork_diagram_compatible
import Theorems.Thm_OAI_OneWayLiveness_CellNetwork_graph_reach_state
import Theorems.Thm_OAI_OneWayLiveness_CellNetwork_graph_step_from_state
import Theorems.Thm_OAI_OneWayLiveness_FunctionalEdges_Rotation_edge_sameCycle
import Theorems.Thm_OAI_OneWayLiveness_Machine_positiveCopy_accepts
import Theorems.Thm_OAI_OneWayLiveness_matching_recognition_degree
import Theorems.Thm_OAI_OneWayLiveness_scanned_list

-- ---- from OAI.Combinatorics.Automata.Tours ----
namespace OAI

namespace OneWayLiveness

namespace FunctionalEdges
variable {V E : Type*} (G : FunctionalEdges V E)
lemma deterministic {v w z : V} (h : G.Step v w) (h' : G.Step v z) : w = z := by
  obtain ⟨e, hs, hd⟩ := h
  obtain ⟨e', hs', hd'⟩ := h'
  have he : e = e' := G.src_injective (hs.trans hs'.symm)
  exact hd.symm.trans (he ▸ hd')

lemma successor_reaches {t v w : V} (ht : ∀ e, G.src e ≠ t)
    (hv : G.Reach v t) (hvw : G.Step v w) : G.Reach w t := by
  rcases hv.cases_head with rfl | ⟨z, hvz, hzt⟩
  · obtain ⟨e, he, _⟩ := hvw
    exact (ht e he).elim
  · exact G.deterministic hvw hvz ▸ hzt

namespace Rotation
variable {G} (R : G.Rotation)
lemma flip_sameCycle [Finite E] {t : V} (ht : ∀ e, G.src e ≠ t) (d : E × Bool)
    (hd : G.Reach (G.vertex d) t) : R.tour.SameCycle d (G.flip d) := by
  rcases d with ⟨e, b⟩
  cases b with
  | false => exact R.edge_sameCycle ht e hd
  | true => exact (R.edge_sameCycle ht e (hd.head ⟨e, rfl, rfl⟩)).symm

lemma perm_sameCycle [Finite E] {t : V} (ht : ∀ e, G.src e ≠ t) (d : E × Bool)
    (hd : G.Reach (G.vertex d) t) : R.tour.SameCycle d (R.perm d) := by
  simpa only [tour_flip] using (R.flip_sameCycle ht d hd).apply_right

lemma vertex_pow (n : ℕ) (d : E × Bool) : G.vertex ((R.perm ^ n) d) = G.vertex d := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [pow_succ', Equiv.Perm.mul_apply, R.vertex_eq] using ih

lemma vertex_sameCycle [Finite E] {t : V} (ht : ∀ e, G.src e ≠ t) (d d' : E × Bool)
    (hd : G.Reach (G.vertex d) t) (he : G.vertex d = G.vertex d') :
    R.tour.SameCycle d d' := by
  obtain ⟨n, rfl⟩ := (R.cyclic d d' he).exists_nat_pow_eq
  clear he
  induction n with
  | zero => exact .refl _ _
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans (R.perm_sameCycle ht _ (by simpa only [R.vertex_pow] using hd))

lemma reach_sameCycle [Finite E] {t : V} (ht : ∀ e, G.src e ≠ t) (d d' : E × Bool)
    (h : G.Reach (G.vertex d) (G.vertex d')) (ht' : G.Reach (G.vertex d') t) :
    R.tour.SameCycle d d' := by
  have aux : ∀ v, G.Reach v (G.vertex d') → ∀ u : E × Bool,
      G.vertex u = v → R.tour.SameCycle u d' := by
    intro v hv
    induction hv using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro u hu
      exact R.vertex_sameCycle ht u d' (hu ▸ ht') hu
    | @head a b hab hbe ih =>
      intro u hu
      obtain ⟨e, hs, he⟩ := hab
      have hae : G.Reach (G.src e) t := hs ▸ (hbe.head ⟨e, hs, he⟩).trans ht'
      exact (R.vertex_sameCycle ht u (e, false) (hu ▸ hs ▸ hae) (hu.trans hs.symm)).trans
        ((R.edge_sameCycle ht e hae).trans (ih (e, true) he))
  exact aux _ h d rfl

/-- All incidences in the basin of a terminal vertex lie on its one tour. -/
lemma basin_sameCycle [Finite E] {t : V} (ht : ∀ e, G.src e ≠ t) (d d' r : E × Bool)
    (hd : G.Reach (G.vertex d) t) (hd' : G.Reach (G.vertex d') t)
    (hr : G.vertex r = t) : R.tour.SameCycle d d' := by
  exact (R.reach_sameCycle ht d r (hr ▸ hd) (hr ▸ .refl)).trans
    (R.reach_sameCycle ht d' r (hr ▸ hd') (hr ▸ .refl)).symm

lemma color_eq_of_sameCycle {D C : Type*} [Finite D] (τ : Equiv.Perm D)
    (color : D → C) (hc : ∀ d, color (τ d) = color d)
    {d d' : D} (h : τ.SameCycle d d') : color d = color d' := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => rfl
  | succ n ih => simpa only [pow_succ', Equiv.Perm.mul_apply, hc] using ih

end Rotation
end FunctionalEdges
end OneWayLiveness

end OAI

-- ---- from OAI.Combinatorics.Automata.Normalization ----
namespace OAI

namespace OneWayLiveness

namespace Machine
variable {Alpha Q : Type}
variable (M : Machine Alpha Q)
end Machine

namespace Machine
variable {Alpha Q : Type} (M : Machine Alpha Q)

lemma sinkCopy_step_old (w : List Alpha) (c : Config (Q := Q) w)
    (c' : Config (Q := Option Q) w) :
    M.sinkCopy.Step w (c.1, some c.2) c' ↔
      (c.2 ∈ M.accepting ∧ c' = (c.1, none)) ∨
      (c.2 ∉ M.accepting ∧ ∃ r, c'.2 = some r ∧ M.Step w c (c'.1, r)) := by
  classical
  simp only [Step, sinkCopy]
  by_cases ha : c.2 ∈ M.accepting
  · simp only [ha, ↓reduceIte, Option.some.injEq, Prod.mk.injEq, true_and, not_true_eq_false,
      false_and, or_false]
    constructor
    · rintro ⟨d, ⟨hq, rfl⟩, hd⟩
      exact Prod.ext (Fin.ext hd) hq.symm
    · rintro rfl
      exact ⟨.stay, ⟨rfl, rfl⟩, rfl⟩
  · simp only [ha, ↓reduceIte, false_and, not_false_eq_true, true_and, false_or]
    constructor
    · rintro ⟨d, hd, hr⟩
      obtain ⟨⟨r,e⟩, ht, he⟩ := Option.map_eq_some_iff.mp hd
      simp only [Prod.mk.injEq] at he
      exact ⟨r, he.1.symm, e, ht, he.2 ▸ hr⟩
    · rintro ⟨r, hr, d, ht, hd⟩
      exact ⟨d, by simp only [ht, Option.map_some, hr], hd⟩

end Machine

namespace Machine
variable {Alpha Q : Type} (M : Machine Alpha Q)

lemma sinkCopy_sweep (w : List Alpha) (i : Fin (w.length + 2)) :
    Relation.ReflTransGen (M.sinkCopy.Step w) (i, none) (terminal w) := by
  classical
  induction i using Fin.reverseInduction with
  | last => exact .refl
  | @cast i ih =>
    apply ih.head
    refine ⟨.right, ?_, rfl⟩
    change (match scanned w i.castSucc with | .right => none | _ => some (none, Move.right)) = _
    have hn : scanned w i.castSucc ≠ .right := by
      rw [ne_eq, scanned_eq_right_iff]
      exact Nat.ne_of_lt i.isLt
    cases h : scanned w i.castSucc <;> simp_all

lemma sinkCopy_reach_iff (w : List Alpha) (c : Config (Q := Q) w) :
    Relation.ReflTransGen (M.sinkCopy.Step w) (c.1, some c.2) (terminal w) ↔
      ∃ a, Relation.ReflTransGen (M.Step w) c a ∧ a.2 ∈ M.accepting := by
  classical
  constructor
  · intro hp
    have aux (b : Config (Q := Option Q) w)
        (h : Relation.ReflTransGen (M.sinkCopy.Step w) b (terminal w)) :
        ∀ q, b.2 = some q → ∃ a, Relation.ReflTransGen (M.Step w) (b.1,q) a ∧ a.2 ∈ M.accepting := by
      induction h using Relation.ReflTransGen.head_induction_on with
      | refl => intro q hq; cases hq
      | @head b d hbd _ ih =>
        intro q hq
        have hb : b = (b.1, some q) := Prod.ext rfl hq
        rw [hb] at hbd
        rcases (M.sinkCopy_step_old w (b.1,q) d).mp hbd with ⟨ha, _⟩ | ⟨_hn, r, hr, hs⟩
        · exact ⟨(b.1,q), .refl, ha⟩
        · obtain ⟨a, hda, ha⟩ := ih r hr
          exact ⟨a, hda.head hs, ha⟩
    exact aux _ hp c.2 rfl
  · rintro ⟨a, hp, ha⟩
    induction hp using Relation.ReflTransGen.head_induction_on with
    | refl =>
      exact (M.sinkCopy_sweep w a.1).head
        ((M.sinkCopy_step_old w a (a.1,none)).mpr (.inl ⟨ha, rfl⟩))
    | @head b d hbd _ ih =>
      by_cases hb : b.2 ∈ M.accepting
      · exact (M.sinkCopy_sweep w b.1).head
          ((M.sinkCopy_step_old w b (b.1,none)).mpr (.inl ⟨hb, rfl⟩))
      · exact ih.head ((M.sinkCopy_step_old w b (d.1,some d.2)).mpr (.inr ⟨hb, d.2, rfl, hbd⟩))

lemma sinkCopy_accepts (w : List Alpha) :
    Relation.ReflTransGen (M.sinkCopy.Step w) (⟨0, by omega⟩, some M.initial) (terminal w) ↔
      M.Accepts false w := M.sinkCopy_reach_iff w (⟨0, by omega⟩, M.initial)

end Machine
end OneWayLiveness

end OAI

-- ---- from OAI.Combinatorics.Automata.Network ----
namespace OAI

namespace OneWayLiveness
namespace CellNetwork
variable (Q : Type)

variable {Q} {Alpha : Type} (M : Machine Alpha Q)

variable (Q)
variable {Q}

lemma graphOrder_apply [Fintype Q] (finish : Q) (w : List Alpha) (d : Edge Q w.length × Bool) :
    edgeInc Q w.length ((graphOrder M finish w).perm d) =
      (wholeOrder M finish w).perm (edgeInc Q w.length d) := by
  change incidenceEquiv Q w.length ((incidenceEquiv Q w.length).symm (_)) = _
  exact (incidenceEquiv Q w.length).apply_symm_apply _

lemma graph_terminal (finish : Q) (w : List Alpha) (t : Machine.Config (Q := Q) w)
    (ht : M.transition t.2 (scanned w t.1) = none) :
    ∀ e, (graph M finish w).src e ≠ stateVertex w t := by
  intro e he
  obtain ⟨c,_,d,hd,_⟩ := (graph_step_from_state M finish w t _).mp ⟨e,he,rfl⟩
  simp [ht] at hd

lemma scanned_outCell (w : List Alpha) (s : Bool) :
    scanned w (outCell w.length s) = if s then .right else .left := by
  cases s with
  | false => exact (scanned_eq_left_iff _ _).mpr rfl
  | true => exact (scanned_eq_right_iff _ _).mpr rfl

lemma test_destination (finish : Q) (w : List Alpha) (s : Bool) :
    (graph M finish w).dst (.inr (.inr (s,testSlot M finish))) =
      stateVertex w (outCell w.length s,if s then finish else M.initial) := by
  classical
  change Sum.inl (_,localVertex M finish _ _) = _
  rw [scanned_outCell]
  cases s <;> simp [localVertex, outward, stateVertex]

lemma test_step (finish : Q) (w : List Alpha) (s : Bool) :
    (graph M finish w).Step (.inr (s,testSlot M finish))
      (stateVertex w (outCell w.length s,if s then finish else M.initial)) :=
  ⟨.inr (.inr (s,testSlot M finish)),rfl,test_destination M finish w s⟩

end CellNetwork
end OneWayLiveness

end OAI

-- ---- from OAI.Combinatorics.Automata.Diagrams ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace OneWayLiveness
namespace Pairing
variable {A : Type} [Fintype A]

lemma prod_compatible_chain (as : List (Pairing (A ⊕ A))) (l r : A → Bool) :
    as.prod.Compatible (Sum.elim l r) ↔ ∃ b : ℕ → A → Bool,
      b 0 = l ∧ b as.length = r ∧
      ∀ i (hi : i < as.length), (as[i]).Compatible (Sum.elim (b i) (b (i+1))) := by
  induction as generalizing l with
  | nil =>
    change (identity A).Compatible (Sum.elim l r) ↔ _
    rw [identity_compatible]
    constructor
    · intro h; subst r; exact ⟨fun _ => l,rfl,rfl,by simp⟩
    · rintro ⟨b,hb,hb',_⟩; exact hb.symm.trans hb'
  | cons a as ih =>
    change (compose a as.prod).Compatible (Sum.elim l r) ↔ _
    rw [compose_compatible]
    constructor
    · rintro ⟨m,ha,has⟩
      obtain ⟨b,hb,hb',hc⟩ := (ih m).mp has
      refine ⟨fun i => Nat.casesOn i l b,rfl,hb',?_⟩
      intro i hi
      cases i with
      | zero => simpa [hb] using ha
      | succ i => exact hc i (by simpa using hi)
    · rintro ⟨b,hb,hb',hc⟩
      refine ⟨b 1, ?_, (ih (b 1)).mpr ⟨fun i => b (i+1),rfl,hb',?_⟩⟩
      · have hzero := hc 0 (by simp)
        change a.Compatible (Sum.elim (b 0) (b 1)) at hzero
        simpa only [hb] using hzero
      · intro i hi
        exact hc (i+1) (by simpa using hi)

lemma ofFn_compatible_chain {n : ℕ} (as : Fin n → Pairing (A ⊕ A)) (l r : A → Bool) :
    (List.ofFn as).prod.Compatible (Sum.elim l r) ↔ ∃ b : ℕ → A → Bool,
      b 0 = l ∧ b n = r ∧
      ∀ i : Fin n, (as i).Compatible (Sum.elim (b i.val) (b (i.val+1))) := by
  rw [prod_compatible_chain]
  simp only [List.length_ofFn, List.getElem_ofFn]
  constructor
  · rintro ⟨b,hl,hr,h⟩; exact ⟨b,hl,hr,fun i => h i.val i.isLt⟩
  · rintro ⟨b,hl,hr,h⟩; exact ⟨b,hl,hr,fun i hi => h ⟨i,hi⟩⟩
end Pairing

namespace CellNetwork
variable {Q Alpha : Type} [Fintype Q] (M : Machine Alpha Q)

lemma fullDiagram_compatible (finish : Q) (w : List Alpha) (l r : Port Q → Bool) :
    (fullDiagram M finish w).Compatible (Sum.elim l r) ↔
      ∃ C : ColorData M finish w, C.boundary 0 = l ∧ C.boundary (w.length+2) = r := by
  classical
  rw [fullDiagram, Pairing.ofFn_compatible_chain]
  constructor
  · rintro ⟨b,hl,hr,hc⟩
    have hparts := fun i => (diagram_compatible Q (orders M finish (scanned w i)).perm
      (b i.val) (b (i.val+1))).mp (hc i)
    choose f hf using hparts
    exact ⟨⟨b,f,fun i => (hf i).1, fun i => (hf i).2.1,fun i => (hf i).2.2⟩,hl,hr⟩
  · rintro ⟨C,hl,hr⟩
    exact ⟨C.boundary,hl,hr,fun i => (diagram_compatible Q _ _ _).mpr
      ⟨C.tip i,C.port_eq i,C.stay_eq i,C.join_eq i⟩⟩

namespace ColorData
variable {M} {finish : Q} {w : List Alpha} (C : ColorData M finish w)

lemma wholeTip_join (hl : Flat (C.boundary 0)) (hr : Flat (C.boundary (w.length+2)))
    (x : WholeInc Q w.length) :
    C.wholeTip x false = C.wholeTip ((wholeOrder M finish w).perm x) true := by
  rcases x with ⟨i,j⟩ | ⟨s,slot⟩
  · exact C.join_eq i j
  · cases s with
    | false => exact (hl slot).symm
    | true => exact hr slot

lemma wholeTip_lane (d : Edge Q w.length × Bool) :
    C.wholeTip (edgeInc Q w.length d) true =
      C.wholeTip (edgeInc Q w.length ((graph M finish w).flip d)) false := by
  rcases d with ⟨(⟨j,⟨dir,p,q⟩⟩ | (⟨i,pq⟩ | ⟨s,slot⟩)),role⟩
  · have hleft (lane : Bool) := C.port_eq j.castSucc true (dir,p,q) lane
    have hright (lane : Bool) := C.port_eq j.succ false (dir,p,q) lane
    cases dir <;> cases role <;>
      simp only [edgeInc, FunctionalEdges.flip_apply, Bool.false_xor, Bool.true_xor,
        Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, wholeTip] <;>
      first
        | exact (hleft false).symm.trans (hright false)
        | exact (hright true).symm.trans (hleft true)
  · exact C.stay_eq i pq role true
  · have hp (lane : Bool) := C.port_eq (outCell w.length s) s slot lane
    cases s <;> cases role <;>
      simp only [edgeInc, FunctionalEdges.flip_apply, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, wholeTip, outCell, tipRole, Bool.false_xor,
        Bool.true_xor] <;>
      first
        | exact (hp false).symm
        | exact (hp true).symm
        | exact hp false
        | exact hp true

lemma tour_invariant (hl : Flat (C.boundary 0)) (hr : Flat (C.boundary (w.length+2)))
    (d : Edge Q w.length × Bool) :
    C.wholeTip (edgeInc Q w.length ((graphOrder M finish w).tour d)) true =
      C.wholeTip (edgeInc Q w.length d) true := by
  change C.wholeTip (edgeInc Q w.length ((graphOrder M finish w).perm
    ((graph M finish w).flip d))) true = _
  rw [graphOrder_apply, ← C.wholeTip_join hl hr]
  exact (C.wholeTip_lane d).symm

end ColorData
lemma reach_excludes_separation (finish : Q) (ht : M.transition finish .right = none)
    (w : List Alpha)
    (hp : Relation.ReflTransGen (M.Step w) (outCell w.length false,M.initial)
      (outCell w.length true,finish))
    (C : ColorData M finish w) : ¬ Separated M finish (C.boundary 0) (C.boundary (w.length+2)) := by
  rintro ⟨hl,hr,hleft,hright⟩
  let eL : Edge Q w.length := .inr (.inr (false,testSlot M finish))
  let eR : Edge Q w.length := .inr (.inr (true,testSlot M finish))
  have hterm : ∀ e, (graph M finish w).src e ≠
      stateVertex w (outCell w.length true,finish) :=
    graph_terminal M finish w _ (by simpa only [scanned_outCell, ↓reduceIte] using ht)
  have hL : (graph M finish w).Reach ((graph M finish w).vertex (eL,false))
      (stateVertex w (outCell w.length true,finish)) :=
    ((graph_reach_state M finish w _ _).mpr hp).head (test_step M finish w false)
  have hR : (graph M finish w).Reach ((graph M finish w).vertex (eR,false))
      (stateVertex w (outCell w.length true,finish)) :=
    Relation.ReflTransGen.single (test_step M finish w true)
  have hh := (graphOrder M finish w).basin_sameCycle hterm (eL,false) (eR,false) (eR,true)
    hL hR (test_destination M finish w true)
  have he := FunctionalEdges.Rotation.color_eq_of_sameCycle (graphOrder M finish w).tour
    (fun d => C.wholeTip (edgeInc Q w.length d) true) (C.tour_invariant hl hr) hh
  change C.boundary 0 (testSlot M finish,false) =
    C.boundary (w.length+2) (testSlot M finish,true) at he
  rw [hleft, ← hr _, hright] at he
  cases he

omit [Fintype Q] in
lemma boundaryColor_test (finish : Q) (w : List Alpha) (c : Vertex Q w.length → Bool)
    (hc : ∀ e, c ((graph M finish w).src e) = c ((graph M finish w).dst e)) (s lane : Bool) :
    boundaryColor M finish w c (if s then w.length+2 else 0) (testSlot M finish,lane) =
      c (stateVertex w (outCell w.length s,if s then finish else M.initial)) := by
  calc
    _ = c (wholeVertex M finish w (.inl (outCell w.length s,.inl (s,testSlot M finish)))) := by
      cases s with
      | false => exact boundaryColor_left M finish w c hc (outCell w.length false) _ _
      | true => exact boundaryColor_right M finish w c (outCell w.length true) _ _
    _ = _ := congrArg c (test_destination M finish w s)

lemma separation_of_not_reach (finish : Q) (ht : M.transition finish .right = none)
    (w : List Alpha)
    (hp : ¬ Relation.ReflTransGen (M.Step w) (outCell w.length false,M.initial)
      (outCell w.length true,finish)) :
    ∃ C : ColorData M finish w, Separated M finish (C.boundary 0) (C.boundary (w.length+2)) := by
  classical
  let sink := stateVertex w (outCell w.length true,finish)
  have hterm : ∀ e, (graph M finish w).src e ≠ sink :=
    graph_terminal M finish w _ (by simpa only [scanned_outCell, ↓reduceIte] using ht)
  let c : Vertex Q w.length → Bool := fun v => decide ((graph M finish w).Reach v sink)
  have hc : ∀ e, c ((graph M finish w).src e) = c ((graph M finish w).dst e) := by
    intro e
    apply Bool.eq_iff_iff.mpr
    simp only [c, decide_eq_true_eq]
    exact ⟨fun h => (graph M finish w).successor_reaches hterm h ⟨e,rfl,rfl⟩,
      fun h => h.head ⟨e,rfl,rfl⟩⟩
  refine ⟨vertexColorData M finish w c hc, ?_, ?_, ?_, ?_⟩
  · intro slot; rfl
  · intro slot; rfl
  · change boundaryColor M finish w c 0 _ = false
    rw [show (0 : ℕ) = (if false then w.length+2 else 0) from rfl,
      boundaryColor_test M finish w c hc false false]
    change decide ((graph M finish w).Reach (stateVertex w (outCell w.length false,M.initial)) sink) = false
    rw [decide_eq_false_iff_not, graph_reach_state]
    exact hp
  · change boundaryColor M finish w c (w.length+2) _ = true
    rw [show w.length+2 = (if true then w.length+2 else 0) from rfl,
      boundaryColor_test M finish w c hc true false]
    change decide ((graph M finish w).Reach sink sink) = true
    exact decide_eq_true Relation.ReflTransGen.refl

/-- The Boolean test recovers exactly acceptance, not a halting assumption.
Only the normalized distinguished right state is required to be terminal. -/
lemma diagram_recognizes_reach (finish : Q) (ht : M.transition finish .right = none)
    (w : List Alpha) :
    (¬ ∃ l r, (fullDiagram M finish w).Compatible (Sum.elim l r) ∧ Separated M finish l r) ↔
      Relation.ReflTransGen (M.Step w) (outCell w.length false,M.initial)
        (outCell w.length true,finish) := by
  classical
  constructor
  · intro h
    by_contra hn
    obtain ⟨C,hC⟩ := separation_of_not_reach M finish ht w hn
    exact h ⟨C.boundary 0,C.boundary (w.length+2),
      (fullDiagram_compatible M finish w _ _).mpr ⟨C,rfl,rfl⟩,hC⟩
  · rintro h ⟨l,r,hd,hs⟩
    obtain ⟨C,rfl,rfl⟩ := (fullDiagram_compatible M finish w l r).mp hd
    exact reach_excludes_separation M finish ht w h C hs

end CellNetwork
end OneWayLiveness

end OAI

-- ---- from OAI.Combinatorics.Automata.Recognition ----
namespace OAI

namespace OneWayLiveness

namespace CellNetwork
variable {Alpha Q : Type} [Fintype Q] (M : Machine Alpha Q)

lemma fullDiagram_markers (finish : Q) (w : List Alpha) :
    fullDiagram M finish w =
      bodyDiagram M finish .left * (w.map (fun a => bodyDiagram M finish (.letter a))).prod *
        bodyDiagram M finish .right := by
  unfold fullDiagram
  have h : (List.ofFn fun i : Fin (w.length+2) => bodyDiagram M finish (scanned w i)) =
      (List.ofFn (scanned w)).map (bodyDiagram M finish) := by rw [List.map_ofFn]; rfl
  rw [h, scanned_list]
  simp only [List.map_cons, List.map_append, List.map_nil, List.map_map,
    List.prod_cons, List.prod_append, List.prod_nil, mul_one, Function.comp_def, mul_assoc]

lemma recognitionTest_iff (finish : Q) (ht : M.transition finish .right = none)
    (w : List Alpha) :
    recognitionTest M finish (w.map (fun a => bodyDiagram M finish (.letter a))).prod ↔
      Relation.ReflTransGen (M.Step w) (outCell w.length false,M.initial)
        (outCell w.length true,finish) := by
  rw [recognitionTest, ← fullDiagram_markers]
  exact diagram_recognizes_reach M finish ht w

end CellNetwork

namespace Machine
variable {H Q : Type} [Fintype H] [Fintype Q] (M : Machine (BRel H) Q)

lemma liveness_rank_bound (hM : ∀ w, M.Accepts false w ↔ BRel.live w)
    (x y : H) (hxy : x ≠ y) : rankLoss (Fintype.card H) ≤ 4 * (Fintype.card Q + 1)^2 := by
  classical
  let S := M.sinkCopy
  have ht : S.transition none .right = none := rfl
  have hr (w : List (BRel H)) :
      CellNetwork.recognitionTest S none
        (w.map (fun a => CellNetwork.bodyDiagram S none (.letter a))).prod ↔ BRel.live w := by
    rw [CellNetwork.recognitionTest_iff S none ht]
    exact (M.sinkCopy_accepts w).trans (hM w)
  have hb := matching_recognition_degree
    (fun a => CellNetwork.bodyDiagram S none (.letter a))
    (CellNetwork.recognitionTest S none) hr x y hxy
  have hc : Fintype.card (CellNetwork.Port (Option Q)) = 4 * (Fintype.card Q + 1)^2 := by
    simp only [CellNetwork.Port, CellNetwork.Slot, Fintype.card_prod, Fintype.card_bool,
      Fintype.card_option]
    ring
  rwa [hc] at hb

end Machine

/-- The representation uses four ports per ordered state pair. One sink state
suffices under reflexive acceptance; a fresh initial row handles positive runs. -/
theorem deterministic_lower_bound (h : ℕ) (hh : 2 ≤ h) (positive : Bool) (s : ℕ)
    (D : DMachine (Alphabet h) s) (hD : D.Recognizes positive (OWL h)) :
    2 ^ ((h - 2) / 31) ≤ 4 * (s + if positive then 2 else 1)^2 := by
  let x : Fin h := ⟨0, by omega⟩
  let y : Fin h := ⟨1, by omega⟩
  have hxy : x ≠ y := by intro he; have := congrArg Fin.val he; simp [x,y] at this
  cases positive with
  | false =>
    have hb := D.toMachine.liveness_rank_bound hD x y hxy
    simpa only [rankLoss, Fintype.card_fin, Bool.false_eq_true, ↓reduceIte] using hb
  | true =>
    have hd (w) : D.toMachine.positiveCopy.Accepts false w ↔ BRel.live w :=
      (D.toMachine.positiveCopy_accepts w).trans (hD w)
    have hb := D.toMachine.positiveCopy.liveness_rank_bound hd x y hxy
    simpa only [rankLoss, Fintype.card_fin, Fintype.card_option, ↓reduceIte,
      Nat.add_assoc] using hb

end OneWayLiveness

end OAI

-- ---- platform node ----
open OAI OAI.OneWayLiveness


theorem solution : type_of% @_root_.OAI.OneWayLiveness.deterministic_lower_bound := @_root_.OAI.OneWayLiveness.deterministic_lower_bound
