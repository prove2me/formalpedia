-- Prove2me | solution 1 for NagamochiIbaraki.EdgeConn.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:27:18.035798+00:00
-- url     : https://prove2.me/submissions/fc8bdf89-b3db-4afa-aff8-2cf21bddd244

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_EdgeConn_localEdgeConn
import Definitions.Def_NagamochiIbaraki_EdgeConn_Forest

namespace NagamochiIbaraki.EdgeConn

section aux_ni25

variable {V E : Type*}

theorem aux_ni25_reach_closed {G : SimpleGraph V} {u v : V} (h : G.Reachable u v)
    (S : V → Prop) (hu : S u) (hS : ∀ a b, G.Adj a b → S a → S b) : S v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hu
  | cons hadj _ ih => exact ih (hS _ _ hadj hu)

theorem aux_ni25_mono (ends : E → Sym2 V) {F F' : Finset E} (h : F ⊆ F') {u v : V}
    (hr : (edgeGraph ends F).Reachable u v) : (edgeGraph ends F').Reachable u v := by
  refine SimpleGraph.Reachable.mono ?_ hr
  unfold edgeGraph
  exact SimpleGraph.fromEdgeSet_mono (Set.image_mono (by exact_mod_cast h))

theorem aux_ni25_adj (ends : E → Sym2 V) {F : Finset E} {e : E} (he : e ∈ F) {x y : V}
    (hxy : x ≠ y) (hends : ends e = s(x, y)) : (edgeGraph ends F).Adj x y := by
  unfold edgeGraph
  rw [SimpleGraph.fromEdgeSet_adj]
  exact ⟨⟨e, by simpa using he, hends⟩, hxy⟩

theorem aux_ni25_isolated (ends : E → Sym2 V) {F : Finset E} {y : V}
    (hy : ∀ e ∈ F, y ∉ ends e) {u : V} (h : (edgeGraph ends F).Reachable u y) : u = y := by
  by_contra hne
  have := aux_ni25_reach_closed h (fun w => w ≠ y) hne (by
    intro a b hab _ hb
    subst hb
    unfold edgeGraph at hab
    rw [SimpleGraph.fromEdgeSet_adj] at hab
    obtain ⟨⟨g, hg, hge⟩, _⟩ := hab
    exact hy g (by simpa using hg) (by rw [hge]; exact Sym2.mem_mk_right _ _))
  exact this rfl

theorem aux_ni25_forest_insert [DecidableEq E] (ends : E → Sym2 V) {F : Finset E} {e : E}
    (hF : IsForest ends F) (heF : e ∉ F) {x y : V} (hxy : x ≠ y) (hends : ends e = s(x, y))
    (hy : ∀ g ∈ F, y ∉ ends g) : IsForest ends (insert e F) := by
  intro f hf u v hfuv
  rcases Finset.mem_insert.mp hf with rfl | hfF
  · rw [Finset.erase_insert heF]
    intro hr
    rw [hends] at hfuv
    rcases Sym2.eq_iff.mp hfuv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hxy (aux_ni25_isolated ends hy hr)
    · exact hxy (aux_ni25_isolated ends hy hr.symm)
  · intro hr
    have hfe : f ≠ e := by rintro rfl; exact heF hfF
    have huy : u ≠ y := by
      rintro rfl; exact hy f hfF (by rw [hfuv]; exact Sym2.mem_mk_left _ _)
    have hvy : v ≠ y := by
      rintro rfl; exact hy f hfF (by rw [hfuv]; exact Sym2.mem_mk_right _ _)
    have hFf := hF f hfF u v hfuv
    rw [Finset.erase_insert_of_ne hfe.symm] at hr
    have hy' : ∀ g ∈ F.erase f, y ∉ ends g := fun g hg => hy g (Finset.mem_of_mem_erase hg)
    have key := aux_ni25_reach_closed hr
      (fun w => (edgeGraph ends (F.erase f)).Reachable u w ∨
        (w = y ∧ (edgeGraph ends (F.erase f)).Reachable u x))
      (Or.inl (SimpleGraph.Reachable.refl _)) ?_
    · rcases key with h | ⟨h, _⟩
      · exact hFf h
      · exact hvy h
    · intro a b hab ha
      unfold edgeGraph at hab
      rw [SimpleGraph.fromEdgeSet_adj] at hab
      obtain ⟨⟨g, hg, hge⟩, hab⟩ := hab
      have hg' : g = e ∨ g ∈ F.erase f := Finset.mem_insert.mp (Finset.mem_coe.mp hg)
      rcases hg' with rfl | hg'
      · rw [hends] at hge
        rcases Sym2.eq_iff.mp hge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rcases ha with h | ⟨h, _⟩
          · exact Or.inr ⟨rfl, h⟩
          · exact absurd h hxy
        · rcases ha with h | ⟨_, h⟩
          · exact absurd (aux_ni25_isolated ends hy' h) huy
          · exact Or.inl h
      · rcases ha with h | ⟨rfl, _⟩
        · exact Or.inl (h.trans (aux_ni25_adj ends hg' hab hge).reachable)
        · exfalso
          exact hy' g hg' (by rw [hge]; exact Sym2.mem_mk_left _ _)

/-- Nodes that are not scanned and are either current or already carry an edge of class `i`. -/
def aux_ni25_A (s : State V E) (i : ℕ) (v : V) : Prop :=
  v ∉ s.done ∧ (s.cur = some v ∨ i ≤ s.r v)

structure aux_ni25_Inv [Fintype E] [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V)
    (i : ℕ) (s : State V E) : Prop where
  cur_nd : ∀ x, s.cur = some x → x ∉ s.done
  done_sc : ∀ v ∈ s.done, ∀ e, v ∈ ends e → s.idx e ≠ 0
  le_r : ∀ v, v ∉ s.done → s.cur ≠ some v → ∀ e, v ∈ ends e → s.idx e ≤ s.r v
  conn : ∀ u w, aux_ni25_A s i u → aux_ni25_A s i w →
    (edgeGraph ends (cls s i)).Reachable u w
  maxl : ∀ e, i < s.idx e → ∀ u v, ends e = s(u, v) →
    (edgeGraph ends (cls s i)).Reachable u v
  forest : IsForest ends (cls s i)

theorem aux_ni25_init [Fintype E] [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V)
    {i : ℕ} (hi : 1 ≤ i) : aux_ni25_Inv ends i (init : State V E) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; simp [init] at hx
  · intro v hv; simp [init] at hv
  · intro v _ _ e _; simp [init]
  · intro u w hu _
    exfalso
    rcases hu with ⟨_, h | h⟩
    · simp [init] at h
    · simp [init] at h; omega
  · intro e he; simp [init] at he
  · intro e he
    exfalso
    have h1 : (init : State V E).idx e = i := by simpa [cls] using he
    have h2 : (init : State V E).idx e = 0 := rfl
    omega

theorem aux_ni25_step [Fintype E] [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) {i : ℕ} (hi : 1 ≤ i) {s t : State V E}
    (hst : Step ends s t) (hs : aux_ni25_Inv ends i s) : aux_ni25_Inv ends i t := by
  rcases hst with ⟨x, hcur, hxd, hmax, rfl⟩ | ⟨x, y, e, hcur, he0, hends, rfl⟩ |
      ⟨x, hcur, hall, rfl⟩
  · -- select
    refine ⟨?_, hs.done_sc, ?_, ?_, hs.maxl, hs.forest⟩
    · intro z hz
      simp at hz
      subst hz
      exact hxd
    · intro v hv _
      exact hs.le_r v hv (by rw [hcur]; simp)
    · intro u w hu hw
      show (edgeGraph ends (cls s i)).Reachable u w
      by_cases hx : i ≤ s.r x
      · have hA : ∀ v, aux_ni25_A { s with cur := some x, order := s.order ++ [x] } i v →
            aux_ni25_A s i v := by
          rintro v ⟨hv1, hv2⟩
          refine ⟨hv1, Or.inr ?_⟩
          rcases hv2 with h | h
          · simp at h; subst h; exact hx
          · exact h
        exact hs.conn u w (hA u hu) (hA w hw)
      · have hA : ∀ v, aux_ni25_A { s with cur := some x, order := s.order ++ [x] } i v →
            v = x := by
          rintro v ⟨hv1, hv2⟩
          rcases hv2 with h | h
          · simp at h; exact h.symm
          · exfalso
            have := hmax v hv1
            simp at h
            omega
        rw [hA u hu, hA w hw]
  · -- scan
    have hxy : x ≠ y := by
      intro h
      apply hloop e
      rw [hends, h]
      exact Sym2.mk_isDiag_iff.mpr rfl
    have hyd : y ∉ s.done := by
      intro hy
      exact hs.done_sc y hy e (by rw [hends]; exact Sym2.mem_mk_right _ _) he0
    have hxd : x ∉ s.done := hs.cur_nd x hcur
    have hyle : ∀ g, y ∈ ends g → s.idx g ≤ s.r y :=
      hs.le_r y hyd (by rw [hcur]; simpa using hxy)
    have hsub : cls s i ⊆ cls { s with
        idx := Function.update s.idx e (s.r y + 1),
        r := Function.update
          (Function.update s.r x (if s.r x = s.r y then s.r x + 1 else s.r x))
          y (s.r y + 1) } i := by
      intro g hg
      simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      have hge : g ≠ e := by rintro rfl; omega
      rw [Function.update_of_ne hge]
      exact hg
    have hxA : aux_ni25_A s i x := ⟨hxd, Or.inl hcur⟩
    refine ⟨hs.cur_nd, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv g hg
      show Function.update s.idx e (s.r y + 1) g ≠ 0
      by_cases hge : g = e
      · subst hge; simp
      · rw [Function.update_of_ne hge]; exact hs.done_sc v hv g hg
    · intro v hv hvc g hg
      show Function.update s.idx e (s.r y + 1) g ≤ Function.update
          (Function.update s.r x (if s.r x = s.r y then s.r x + 1 else s.r x))
          y (s.r y + 1) v
      have hvx : v ≠ x := by rintro rfl; exact hvc hcur
      by_cases hvy : v = y
      · subst hvy
        rw [Function.update_self]
        by_cases hge : g = e
        · subst hge; simp
        · rw [Function.update_of_ne hge]; have := hyle g hg; omega
      · rw [Function.update_of_ne hvy, Function.update_of_ne hvx]
        have hge : g ≠ e := by
          rintro rfl
          rw [hends] at hg
          rcases Sym2.mem_iff.mp hg with h | h
          · exact hvx h
          · exact hvy h
        rw [Function.update_of_ne hge]
        exact hs.le_r v hv hvc g hg
    · -- conn
      have hreach : ∀ v, aux_ni25_A { s with
          idx := Function.update s.idx e (s.r y + 1),
          r := Function.update
            (Function.update s.r x (if s.r x = s.r y then s.r x + 1 else s.r x))
            y (s.r y + 1) } i v →
          (edgeGraph ends (cls { s with
            idx := Function.update s.idx e (s.r y + 1),
            r := Function.update
              (Function.update s.r x (if s.r x = s.r y then s.r x + 1 else s.r x))
              y (s.r y + 1) } i)).Reachable x v := by
        rintro v ⟨hv1, hv2⟩
        change v ∉ s.done at hv1
        change s.cur = some v ∨ i ≤ Function.update
            (Function.update s.r x (if s.r x = s.r y then s.r x + 1 else s.r x))
            y (s.r y + 1) v at hv2
        by_cases hvy : v = y
        · subst hvy
          rw [Function.update_self] at hv2
          rcases hv2 with h | h
          · rw [hcur] at h; simp at h; exact absurd h hxy
          · by_cases hri : s.r v + 1 = i
            · have hein : e ∈ cls { s with
                  idx := Function.update s.idx e (s.r v + 1),
                  r := Function.update
                    (Function.update s.r x (if s.r x = s.r v then s.r x + 1 else s.r x))
                    v (s.r v + 1) } i := by
                simp [cls, hri]
              exact (aux_ni25_adj ends hein hxy hends).reachable
            · exact aux_ni25_mono ends hsub (hs.conn x v hxA ⟨hv1, Or.inr (by omega)⟩)
        · have hvA : aux_ni25_A s i v := by
            by_cases hvx : v = x
            · subst hvx; exact hxA
            refine ⟨hv1, ?_⟩
            rcases hv2 with h | h
            · exact Or.inl h
            · right
              rw [Function.update_of_ne hvy, Function.update_of_ne hvx] at h
              exact h
          exact aux_ni25_mono ends hsub (hs.conn x v hxA hvA)
      intro u w hu hw
      exact (hreach u hu).symm.trans (hreach w hw)
    · -- maxl
      intro g hg u v huv
      change i < Function.update s.idx e (s.r y + 1) g at hg
      by_cases hge : g = e
      · subst hge
        rw [Function.update_self] at hg
        have hyA : aux_ni25_A s i y := ⟨hyd, Or.inr (by omega)⟩
        have hxy' := aux_ni25_mono ends hsub (hs.conn x y hxA hyA)
        rw [hends] at huv
        rcases Sym2.eq_iff.mp huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hxy'
        · exact hxy'.symm
      · rw [Function.update_of_ne hge] at hg
        exact aux_ni25_mono ends hsub (hs.maxl g hg u v huv)
    · -- forest
      by_cases hri : s.r y + 1 = i
      · have hcl : cls { s with
            idx := Function.update s.idx e (s.r y + 1),
            r := Function.update
              (Function.update s.r x (if s.r x = s.r y then s.r x + 1 else s.r x))
              y (s.r y + 1) } i = insert e (cls s i) := by
          ext g
          simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          by_cases hge : g = e
          · subst hge; simp [hri]
          · rw [Function.update_of_ne hge]; simp [hge]
        rw [hcl]
        refine aux_ni25_forest_insert ends hs.forest ?_ hxy hends ?_
        · simp [cls]; omega
        · intro g hg hyg
          simp [cls] at hg
          have := hyle g hyg
          omega
      · have hcl : cls { s with
            idx := Function.update s.idx e (s.r y + 1),
            r := Function.update
              (Function.update s.r x (if s.r x = s.r y then s.r x + 1 else s.r x))
              y (s.r y + 1) } i = cls s i := by
          ext g
          simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hge : g = e
          · subst hge; simp; omega
          · rw [Function.update_of_ne hge]
        rw [hcl]
        exact hs.forest
  · -- finish
    refine ⟨?_, ?_, ?_, ?_, hs.maxl, hs.forest⟩
    · intro z hz; simp at hz
    · intro v hv g hg
      simp only [Finset.mem_insert] at hv
      rcases hv with rfl | hv
      · exact hall g hg
      · exact hs.done_sc v hv g hg
    · intro v hv _ g hg
      simp only [Finset.mem_insert, not_or] at hv
      exact hs.le_r v hv.2 (by rw [hcur]; simpa using fun h => hv.1 h.symm) g hg
    · have hA : ∀ v, aux_ni25_A { s with done := insert x s.done, cur := none } i v →
          aux_ni25_A s i v := by
        rintro v ⟨hv1, hv2⟩
        simp only [Finset.mem_insert, not_or] at hv1
        refine ⟨hv1.2, Or.inr ?_⟩
        rcases hv2 with h | h
        · simp at h
        · exact h
      intro u w hu hw
      exact hs.conn u w (hA u hu) (hA w hw)

end aux_ni25

end NagamochiIbaraki.EdgeConn

open NagamochiIbaraki.EdgeConn

theorem solution
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsCompletedRun ends σ K) :
    ∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card E →
      IsMaxSpanningForest ends
        (Finset.univ.filter (fun e => ¬ (1 ≤ (σ K).idx e ∧ (σ K).idx e ≤ i - 1)))
        (cls (σ K) i) := by
  intro i hi1 _
  obtain ⟨⟨h0, hstep⟩, hdone⟩ := hrun
  have hinv : ∀ k, k ≤ K → aux_ni25_Inv ends i (σ k) := by
    intro k
    induction k with
    | zero => intro _; rw [h0]; exact aux_ni25_init ends hi1
    | succ k ih =>
      intro hk
      exact aux_ni25_step ends hloop hi1 (hstep k (by omega)) (ih (by omega))
  have hK := hinv K le_rfl
  have hends : ∀ e, ∃ u v, ends e = s(u, v) := fun e =>
    Sym2.ind (f := fun z => ∃ u v, z = s(u, v)) (fun u v => ⟨u, v, rfl⟩) (ends e)
  have hsc : ∀ e, (σ K).idx e ≠ 0 := by
    intro e
    obtain ⟨u, v, huv⟩ := hends e
    exact hK.done_sc u (by rw [hdone]; exact Finset.mem_univ _) e
      (by rw [huv]; exact Sym2.mem_mk_left _ _)
  refine ⟨?_, hK.forest, ?_⟩
  · intro e he
    simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    omega
  · intro e he heF hfor
    simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and] at he heF
    obtain ⟨u, v, huv⟩ := hends e
    have hgt : i < (σ K).idx e := by have := hsc e; omega
    have h1 := hfor e (Finset.mem_insert_self _ _) u v huv
    rw [Finset.erase_insert (by simp [cls]; exact heF)] at h1
    exact h1 (hK.maxl e hgt u v huv)
