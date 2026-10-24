-- Prove2me | solution 1 for OAI.Problem315.PairResampling.spectralGap_of_triples_and_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:14:38.857222+00:00
-- url     : https://prove2.me/submissions/dca9fb57-3c3c-4215-90c6-641f19ebd7a0

import Mathlib
import Definitions.Def_SwitchChain
import Definitions.Def_OAIQWSWC002

section
-- module Solutions.OAIQW_Problem315.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_Problem315.FourVertexSwitch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315

theorem validSwitch_fourVertexProposal_iff {n : Nat} (G : SimpleGraph (Fin n))
    (a b c d : Fin n) (h : FourDistinct a b c d) :
    validSwitch G (fourVertexProposal a b c d h) ↔
      G.Adj a b ∧ G.Adj c d ∧ ¬ G.Adj a c ∧ ¬ G.Adj b d := by
  constructor
  · intro hv
    refine ⟨hv.1 ?_, hv.1 ?_, hv.2 ?_, hv.2 ?_⟩ <;> simp
  · rintro ⟨hab, hcd, hac, hbd⟩
    constructor
    · intro u v huv
      rw [removedMatching_fourVertexProposal] at huv
      rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab
      · exact G.symm.symm _ _ hab
      · exact hcd
      · exact G.symm.symm _ _ hcd
    · intro u v huv
      rw [addedMatching_fourVertexProposal] at huv
      rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hac
      · exact fun he => hac (G.symm.symm _ _ he)
      · exact hbd
      · exact fun he => hbd (G.symm.symm _ _ he)

theorem proposalResult_fourVertex_adj {n : Nat} (G : SimpleGraph (Fin n))
    (a b c d : Fin n) (h : FourDistinct a b c d)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : ¬ G.Adj a c) (hbd : ¬ G.Adj b d) (u v : Fin n) :
    (proposalResult G (fourVertexProposal a b c d h)).Adj u v ↔
      (G.Adj u v ∧ ¬ ((u = a ∧ v = b) ∨ (u = b ∧ v = a) ∨
        (u = c ∧ v = d) ∨ (u = d ∧ v = c))) ∨
      (u = a ∧ v = c) ∨ (u = c ∧ v = a) ∨
      (u = b ∧ v = d) ∨ (u = d ∧ v = b) := by
  classical
  have hv : validSwitch G (fourVertexProposal a b c d h) :=
    (validSwitch_fourVertexProposal_iff G a b c d h).2 ⟨hab, hcd, hac, hbd⟩
  simp only [proposalResult, ite_eq_left hv, replaceEdges,
    removedMatching_fourVertexProposal, addedMatching_fourVertexProposal]

theorem proposalResult_fourVertex_adj_first {n : Nat} (G : SimpleGraph (Fin n))
    (a b c d : Fin n) (h : FourDistinct a b c d)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : ¬ G.Adj a c) (hbd : ¬ G.Adj b d) (v : Fin n) :
    (proposalResult G (fourVertexProposal a b c d h)).Adj a v ↔
      (G.Adj a v ∧ v ≠ b) ∨ v = c := by
  simpa [h.1, h.2.1, h.2.2.1] using
    proposalResult_fourVertex_adj G a b c d h hab hcd hac hbd a v

theorem proposalResult_fourVertex_adj_outside {n : Nat} (G : SimpleGraph (Fin n))
    (a b c d : Fin n) (h : FourDistinct a b c d)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : ¬ G.Adj a c) (hbd : ¬ G.Adj b d)
    (u v : Fin n) (hua : u ≠ a) (hub : u ≠ b) (huc : u ≠ c) (hud : u ≠ d) :
    (proposalResult G (fourVertexProposal a b c d h)).Adj u v ↔ G.Adj u v := by
  simpa [hua, hub, huc, hud] using
    proposalResult_fourVertex_adj G a b c d h hab hcd hac hbd u v

theorem fourVertexState_agrees_outside {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (R : Finset (Fin n))
    (a b c e : Fin n) (h : FourDistinct a b c e)
    (ha : a ∈ R) (hb : b ∈ R) (hc : c ∈ R) (he : e ∈ R)
    (hab : G.val.Adj a b) (hce : G.val.Adj c e)
    (hac : ¬ G.val.Adj a c) (hbe : ¬ G.val.Adj b e)
    (u v : Fin n) (hu : u ∉ R) :
    (fourVertexState G a b c e h).val.Adj u v ↔ G.val.Adj u v := by
  apply proposalResult_fourVertex_adj_outside G.val a b c e h hab hce hac hbe u v
  · exact fun heq => hu (heq ▸ ha)
  · exact fun heq => hu (heq ▸ hb)
  · exact fun heq => hu (heq ▸ hc)
  · exact fun heq => hu (heq ▸ he)

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.FrozenRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315

theorem FrozenRowsAgree.refl {n : Nat} (G : SimpleGraph (Fin n))
    (R : Finset (Fin n)) : FrozenRowsAgree G G R := by
  intro u hu v
  rfl

theorem FrozenRowsAgree.symm {n : Nat} {G H : SimpleGraph (Fin n)}
    {R : Finset (Fin n)} (h : FrozenRowsAgree G H R) : FrozenRowsAgree H G R := by
  intro u hu v
  exact (h u hu v).symm

theorem FrozenRowsAgree.trans {n : Nat} {G H K : SimpleGraph (Fin n)}
    {R : Finset (Fin n)} (hGH : FrozenRowsAgree G H R)
    (hHK : FrozenRowsAgree H K R) : FrozenRowsAgree G K R := by
  intro u hu v
  exact (hGH u hu v).trans (hHK u hu v)

theorem graphDegree_split_residual {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (R : Finset (Fin n)) (v : Fin n) :
    (R.filter (G.Adj v)).card + ((Finset.univ \ R).filter (G.Adj v)).card =
      graphDegree G v := by
  classical
  have hin : (Finset.univ.filter (G.Adj v)).filter (fun w => w ∈ R) =
      R.filter (G.Adj v) := by
    ext w
    simp [and_comm]
  have hout : (Finset.univ.filter (G.Adj v)).filter (fun w => w ∉ R) =
      (Finset.univ \ R).filter (G.Adj v) := by
    ext w
    simp [and_comm]
  have hs := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (G.Adj v)) (fun w => w ∈ R)
  rw [hin, hout] at hs
  calc
    _ = (Finset.univ.filter (G.Adj v)).card := hs
    _ = graphDegree G v := by
      unfold graphDegree
      congr 1
      ext w
      simp

theorem residualDegree_eq_of_frozenRows {n : Nat} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (R : Finset (Fin n))
    (hdeg : ∀ v, graphDegree G v = graphDegree H v)
    (hfreeze : FrozenRowsAgree G H R) (v : Fin n) :
    (R.filter (G.Adj v)).card = (R.filter (H.Adj v)).card := by
  classical
  have hout : (Finset.univ \ R).filter (G.Adj v) =
      (Finset.univ \ R).filter (H.Adj v) := by
    apply Finset.filter_congr
    intro w hw
    have hwR : w ∉ R := (Finset.mem_sdiff.mp hw).2
    constructor
    · intro hvw
      exact ((hfreeze w hwR v).1 hvw.symm).symm
    · intro hvw
      exact ((hfreeze w hwR v).2 hvw.symm).symm
  have hg := graphDegree_split_residual G R v
  have hh := graphDegree_split_residual H R v
  rw [hout, hdeg v] at hg
  omega

theorem graphState_residualDegree_eq {n : Nat} {d : Fin n → Nat}
    (G H : GraphState n d) [DecidableRel G.val.Adj] [DecidableRel H.val.Adj]
    (R : Finset (Fin n)) (hfreeze : FrozenRowsAgree G.val H.val R) (v : Fin n) :
    (R.filter (G.val.Adj v)).card = (R.filter (H.val.Adj v)).card := by
  apply residualDegree_eq_of_frozenRows G.val H.val R _ hfreeze v
  intro u
  exact (G.property u).trans (H.property u).symm

theorem fourVertexState_residual_neighbors {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (R : Finset (Fin n))
    (a b c e : Fin n) (h : FourDistinct a b c e)
    [DecidableRel G.val.Adj] [DecidableRel (fourVertexState G a b c e h).val.Adj]
    (hc : c ∈ R) (hab : G.val.Adj a b) (hce : G.val.Adj c e)
    (hac : ¬ G.val.Adj a c) (hbe : ¬ G.val.Adj b e) :
    R.filter ((fourVertexState G a b c e h).val.Adj a) =
      insert c ((R.filter (G.val.Adj a)).erase b) := by
  classical
  ext w
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
  change (w ∈ R ∧ (proposalResult G.val (fourVertexProposal a b c e h)).Adj a w) ↔ _
  rw [proposalResult_fourVertex_adj_first G.val a b c e h hab hce hac hbe]
  constructor
  · rintro ⟨hwR, ⟨hadj, hwb⟩ | rfl⟩
    · exact Or.inr ⟨hwb, hwR, hadj⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨hwb, hwR, hadj⟩)
    · exact ⟨hc, Or.inr rfl⟩
    · exact ⟨hwR, Or.inl ⟨hadj, hwb⟩⟩

theorem fourVertexState_frozenRows {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (R : Finset (Fin n))
    (a b c e : Fin n) (h : FourDistinct a b c e)
    (ha : a ∈ R) (hb : b ∈ R) (hc : c ∈ R) (he : e ∈ R)
    (hab : G.val.Adj a b) (hce : G.val.Adj c e)
    (hac : ¬ G.val.Adj a c) (hbe : ¬ G.val.Adj b e) :
    FrozenRowsAgree (fourVertexState G a b c e h).val G.val R := by
  intro u hu v
  exact fourVertexState_agrees_outside G R a b c e h ha hb hc he hab hce hac hbe u v hu

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.HavelInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.HavelCanonical

theorem exists_top_subset {V : Type*} [DecidableEq V]
    (R : Finset V) (weight : V → Nat) (k : Nat) (hk : k ≤ R.card) :
    ∃ T : Finset V, T ⊆ R ∧ T.card = k ∧
      ∀ i ∈ R, i ∉ T → ∀ j ∈ T, weight i ≤ weight j := by
  classical
  obtain ⟨T₀, hT₀R, hT₀k⟩ := Finset.exists_subset_card_eq hk
  have hne : (R.powersetCard k).Nonempty :=
    ⟨T₀, Finset.mem_powersetCard.mpr ⟨hT₀R, hT₀k⟩⟩
  obtain ⟨T, hT, hmax⟩ :=
    Finset.exists_max_image (R.powersetCard k) (fun S => ∑ x ∈ S, weight x) hne
  obtain ⟨hTR, hTk⟩ := Finset.mem_powersetCard.mp hT
  refine ⟨T, hTR, hTk, ?_⟩
  intro i hiR hiT j hjT
  let U := insert i (T.erase j)
  have hiE : i ∉ T.erase j := fun h => hiT (Finset.mem_of_mem_erase h)
  have hUR : U ⊆ R := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · simpa [h] using hiR
    · exact hTR (Finset.mem_of_mem_erase h)
  have hUk : U.card = k := by
    simp only [U, Finset.card_insert_of_notMem hiE, Finset.card_erase_of_mem hjT]
    have hjpos : 0 < T.card := Finset.card_pos.mpr ⟨j, hjT⟩
    omega
  have hbound := hmax U (Finset.mem_powersetCard.mpr ⟨hUR, hUk⟩)
  have hsum : (∑ x ∈ T.erase j, weight x) + weight j = ∑ x ∈ T, weight x :=
    Finset.sum_erase_add T weight hjT
  simp only [U, Finset.sum_insert hiE] at hbound
  omega

theorem residual_degree_eq {V : Type*} [Fintype V] [DecidableEq V]
    (R : Finset V) (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hout : AgreeOutside R G H) (hdegree : ∀ v, G.degree v = H.degree v) (v : V) :
    (R.filter (G.Adj v)).card = (R.filter (H.Adj v)).card := by
  classical
  have hin (K : SimpleGraph V) [DecidableRel K.Adj] :
      (K.neighborFinset v).filter (fun w => w ∈ R) = R.filter (K.Adj v) := by
    ext w
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    exact and_comm
  have hext : (G.neighborFinset v).filter (fun w => w ∉ R) =
      (H.neighborFinset v).filter (fun w => w ∉ R) := by
    ext w
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hvw, hwR⟩
      exact ⟨((hout w hwR v).mp hvw.symm).symm, hwR⟩
    · rintro ⟨hvw, hwR⟩
      exact ⟨((hout w hwR v).mpr hvw.symm).symm, hwR⟩
  have hG := (G.neighborFinset v).card_filter_add_card_filter_not (fun w => w ∈ R)
  have hH := (H.neighborFinset v).card_filter_add_card_filter_not (fun w => w ∈ R)
  rw [hin G, hext, SimpleGraph.card_neighborFinset_eq_degree] at hG
  rw [hin H, SimpleGraph.card_neighborFinset_eq_degree] at hH
  have hd := hdegree v
  omega

theorem agreeOutside_erase {V : Type*} [DecidableEq V]
    {R : Finset V} {G H : SimpleGraph V} {v : V}
    (hout : AgreeOutside R G H) (hrow : ∀ w, G.Adj v w ↔ H.Adj v w) :
    AgreeOutside (R.erase v) G H := by
  intro u hu w
  by_cases huv : u = v
  · simpa [huv] using hrow w
  · exact hout u (fun huR => hu (Finset.mem_erase.mpr ⟨huv, huR⟩)) w

theorem connected_of_row_alignment
    {V X : Type*} [Fintype V] [DecidableEq V]
    (graph : X → SimpleGraph V) (hinj : Function.Injective graph)
    (r : X → X → Prop) (hsymm : ∀ ⦃first second⦄, r first second → r second first)
    (halign : ∀ (R : Finset V) (v : V), v ∈ R → ∀ x y : X,
      AgreeOutside R (graph x) (graph y) →
      ∃ x' y' : X,
        Relation.ReflTransGen r x x' ∧ Relation.ReflTransGen r y y' ∧
        AgreeOutside R (graph x') (graph y') ∧
        ∀ w, (graph x').Adj v w ↔ (graph y').Adj v w)
    (x y : X) : Relation.ReflTransGen r x y := by
  classical
  have hreverse {a b : X} (h : Relation.ReflTransGen r a b) :
      Relation.ReflTransGen r b a := by
    induction h with
    | refl => exact .refl
    | tail hab hbc ih => exact (Relation.ReflTransGen.single (hsymm hbc)).trans ih
  have haux : ∀ R : Finset V, ∀ a b : X,
      AgreeOutside R (graph a) (graph b) → Relation.ReflTransGen r a b := by
    intro R
    induction R using Finset.induction_on with
    | empty =>
      intro a b hab
      have hgraphs : graph a = graph b := by
        apply SimpleGraph.ext
        funext v w
        exact propext (hab v (by simp) w)
      have heq := hinj hgraphs
      subst b
      exact .refl
    | @insert v R hv ih =>
      intro a b hab
      obtain ⟨a', b', haa', hbb', hout, hrow⟩ :=
        halign (insert v R) v (Finset.mem_insert_self v R) a b hab
      have hout' : AgreeOutside R (graph a') (graph b') := by
        simpa [Finset.erase_insert hv] using agreeOutside_erase hout hrow
      exact haa'.trans ((ih a' b' hout').trans (hreverse hbb'))
  exact haux Finset.univ x y (by intro v hv; exact False.elim (hv (Finset.mem_univ v)))

theorem connected_of_neighborhood_repair
    {V X : Type*} [Fintype V] [DecidableEq V]
    (graph : X → SimpleGraph V) [∀ x, DecidableRel (graph x).Adj]
    (hinj : Function.Injective graph) (r : X → X → Prop)
    (hsymm : ∀ ⦃first second⦄, r first second → r second first)
    (hdegree : ∀ x y v, (graph x).degree v = (graph y).degree v)
    (hrepair : ∀ (R T : Finset V) (v : V) (x : X),
      v ∈ R → T ⊆ R.erase v → T.card = (R.filter ((graph x).Adj v)).card →
      (∀ i ∈ R, i ≠ v → i ∉ T → ∀ j ∈ T,
        (R.filter ((graph x).Adj i)).card ≤ (R.filter ((graph x).Adj j)).card) →
      ∃ x' : X, Relation.ReflTransGen r x x' ∧
        AgreeOutside R (graph x) (graph x') ∧ R.filter ((graph x').Adj v) = T)
    (x y : X) : Relation.ReflTransGen r x y := by
  classical
  apply connected_of_row_alignment graph hinj r hsymm _ x y
  intro R v hv a b hab
  have hcard : (R.filter ((graph a).Adj v)).card ≤ (R.erase v).card := by
    apply Finset.card_le_card
    intro w hw
    obtain ⟨hwR, hvw⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_erase.mpr ⟨hvw.ne.symm, hwR⟩
  obtain ⟨T, hTR, hTcard, htop⟩ := exists_top_subset (R.erase v)
    (fun w => (R.filter ((graph a).Adj w)).card)
    (R.filter ((graph a).Adj v)).card hcard
  have hsortedA : ∀ i ∈ R, i ≠ v → i ∉ T → ∀ j ∈ T,
      (R.filter ((graph a).Adj i)).card ≤ (R.filter ((graph a).Adj j)).card := by
    intro i hiR hiv hiT j hjT
    exact htop i (Finset.mem_erase.mpr ⟨hiv, hiR⟩) hiT j hjT
  have hres : ∀ w, (R.filter ((graph a).Adj w)).card =
      (R.filter ((graph b).Adj w)).card :=
    residual_degree_eq R (graph a) (graph b) hab (hdegree a b)
  have hsizeB : T.card = (R.filter ((graph b).Adj v)).card :=
    hTcard.trans (hres v)
  have hsortedB : ∀ i ∈ R, i ≠ v → i ∉ T → ∀ j ∈ T,
      (R.filter ((graph b).Adj i)).card ≤ (R.filter ((graph b).Adj j)).card := by
    intro i hiR hiv hiT j hjT
    rw [← hres i, ← hres j]
    exact hsortedA i hiR hiv hiT j hjT
  obtain ⟨a', haa', houtA, hrowA⟩ := hrepair R T v a hv hTR hTcard hsortedA
  obtain ⟨b', hbb', houtB, hrowB⟩ := hrepair R T v b hv hTR hsizeB hsortedB
  have hout' : AgreeOutside R (graph a') (graph b') := by
    intro u hu w
    exact (houtA u hu w).symm.trans ((hab u hu w).trans (houtB u hu w))
  refine ⟨a', b', haa', hbb', hout', ?_⟩
  intro w
  by_cases hw : w ∈ R
  · have h := Finset.ext_iff.mp (hrowA.trans hrowB.symm) w
    simpa only [Finset.mem_filter, hw, true_and] using h
  · constructor
    · intro h
      exact ((hout' w hw v).mp h.symm).symm
    · intro h
      exact ((hout' w hw v).mpr h.symm).symm

end Problem315.HavelCanonical

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.NeighborAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315

theorem reach_target_by_neighbor_swaps
    {α β : Type*} [DecidableEq β]
    (r : α → α → Prop) (N : α → Finset β) (S : Finset β)
    (hcard : ∀ x, (N x).card = S.card)
    (hstep : ∀ x i j, i ∈ N x → i ∉ S → j ∈ S → j ∉ N x →
      ∃ y, r x y ∧ N y = insert j ((N x).erase i)) :
    ∀ x, ∃ y, Relation.ReflTransGen r x y ∧ N y = S := by
  classical
  have aux : ∀ k : ℕ, ∀ x, (S \ N x).card = k →
      ∃ y, Relation.ReflTransGen r x y ∧ N y = S := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x hk
      by_cases heq : N x = S
      · exact ⟨x, Relation.ReflTransGen.refl, heq⟩
      have hnotSN : ¬S ⊆ N x := by
        intro hsub
        exact heq (Finset.eq_of_subset_of_card_le hsub (hcard x).le).symm
      have hnotNS : ¬N x ⊆ S := by
        intro hsub
        exact heq (Finset.eq_of_subset_of_card_le hsub (hcard x).ge)
      obtain ⟨j, hjS, hjN⟩ := Finset.not_subset.mp hnotSN
      obtain ⟨i, hiN, hiS⟩ := Finset.not_subset.mp hnotNS
      obtain ⟨y, hxy, hNy⟩ := hstep x i j hiN hiS hjS hjN
      have hdiff : S \ N y = (S \ N x).erase j := by
        rw [hNy]
        ext z
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        aesop
      have hj : j ∈ S \ N x := Finset.mem_sdiff.mpr ⟨hjS, hjN⟩
      have hlt : (S \ N y).card < k := by
        rw [hdiff, ← hk]
        exact Finset.card_erase_lt_of_mem hj
      obtain ⟨z, hyz, hz⟩ := ih (S \ N y).card hlt y rfl
      exact ⟨z, (Relation.ReflTransGen.single hxy).trans hyz, hz⟩
  intro x
  exact aux (S \ N x).card x rfl

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SwitchWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Problem315

namespace Havel

section FinsetWitness

variable {V : Type*} [DecidableEq V]

theorem exists_switch_witness_in (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset V)
    {v i j : V} (hvR : v ∈ R) (hiR : i ∈ R) (hjR : j ∈ R)
    (hvi : G.Adj v i) (hvj : ¬ G.Adj v j) (hvj_ne : v ≠ j)
    (hdeg : (R.filter (G.Adj i)).card ≤ (R.filter (G.Adj j)).card) :
    ∃ k ∈ R, k ≠ v ∧ k ≠ i ∧ k ≠ j ∧ G.Adj j k ∧ ¬ G.Adj i k := by
  classical
  let A := (R.filter (G.Adj i)).erase j
  let B := (R.filter (G.Adj j)).erase i
  have hcard : A.card ≤ B.card := by
    dsimp [A, B]
    simp only [Finset.card_erase_eq_ite, Finset.mem_filter, hiR, hjR, true_and]
    by_cases hij : G.Adj i j
    · have hji := hij.symm
      simp only [hij, hji, ite_true]
      omega
    · have hji : ¬ G.Adj j i := fun h => hij h.symm
      simpa only [hij, hji, ite_false] using hdeg
  have hvA : v ∈ A := by
    exact Finset.mem_erase.mpr ⟨hvj_ne, Finset.mem_filter.mpr ⟨hvR, hvi.symm⟩⟩
  have hvB : v ∉ B := by
    intro h
    exact hvj (Finset.mem_filter.mp (Finset.mem_of_mem_erase h)).2.symm
  have hcard' : (A.erase v).card < B.card :=
    lt_of_lt_of_le (Finset.card_erase_lt_of_mem hvA) hcard
  obtain ⟨k, hkB, hkA⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard'
  have hkv : k ≠ v := by
    intro h
    exact hvB (h ▸ hkB)
  have hkA' : k ∉ A := by
    intro h
    exact hkA (Finset.mem_erase.mpr ⟨hkv, h⟩)
  have hki : k ≠ i := (Finset.mem_erase.mp hkB).1
  have hkR : k ∈ R := (Finset.mem_filter.mp (Finset.mem_erase.mp hkB).2).1
  have hjk : G.Adj j k := (Finset.mem_filter.mp (Finset.mem_erase.mp hkB).2).2
  have hkj : k ≠ j := hjk.ne.symm
  refine ⟨k, hkR, hkv, hki, hkj, hjk, ?_⟩
  intro hik
  exact hkA' (Finset.mem_erase.mpr ⟨hkj, Finset.mem_filter.mpr ⟨hkR, hik⟩⟩)

end FinsetWitness

end Havel

end Problem315

end OAI
end

section
-- module Solutions.OAIQW_Problem315.HavelConnectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315
attribute [local instance] Classical.propDecidable

theorem havel_neighborhood_repair_of_moves {n : Nat} {d : Fin n → Nat}
    (r : GraphState n d → GraphState n d → Prop)
    (hmoves : ∀ (G : GraphState n d) (a b c e : Fin n) (h : FourDistinct a b c e),
      G.val.Adj a b → G.val.Adj c e → ¬ G.val.Adj a c → ¬ G.val.Adj b e →
      r G (fourVertexState G a b c e h))
    (R T : Finset (Fin n)) (v : Fin n) (G : GraphState n d)
    (hv : v ∈ R) (hTR : T ⊆ R.erase v)
    (hsize : T.card = (R.filter (G.val.Adj v)).card)
    (hsorted : ∀ i ∈ R, i ≠ v → i ∉ T → ∀ j ∈ T,
      (R.filter (G.val.Adj i)).card ≤ (R.filter (G.val.Adj j)).card) :
    ∃ H : GraphState n d, Relation.ReflTransGen r G H ∧
      HavelCanonical.AgreeOutside R G.val H.val ∧ R.filter (H.val.Adj v) = T := by
  classical
  let A := {H : GraphState n d // FrozenRowsAgree H.val G.val R}
  let rA : A → A → Prop := fun H K => r H.val K.val
  let N : A → Finset (Fin n) := fun H => R.filter (H.val.val.Adj v)
  have hres (H : A) (w : Fin n) :
      (R.filter (H.val.val.Adj w)).card = (R.filter (G.val.Adj w)).card :=
    graphState_residualDegree_eq H.val G R H.property w
  have hcard (H : A) : (N H).card = T.card := (hres H v).trans hsize.symm
  have hstep : ∀ H i j, i ∈ N H → i ∉ T → j ∈ T → j ∉ N H →
      ∃ K, rA H K ∧ N K = insert j ((N H).erase i) := by
    intro H i j hi hiT hjT hj
    obtain ⟨hiR, hvi⟩ := Finset.mem_filter.mp hi
    have hjR : j ∈ R := Finset.mem_of_mem_erase (hTR hjT)
    have hvj_ne : v ≠ j := (Finset.mem_erase.mp (hTR hjT)).1.symm
    have hvj : ¬ H.val.val.Adj v j := by
      intro h
      exact hj (Finset.mem_filter.mpr ⟨hjR, h⟩)
    have hdeg : (R.filter (H.val.val.Adj i)).card ≤
        (R.filter (H.val.val.Adj j)).card := by
      rw [hres H i, hres H j]
      exact hsorted i hiR hvi.ne.symm hiT j hjT
    obtain ⟨k, hkR, hkv, hki, hkj, hjk, hik⟩ :=
      Havel.exists_switch_witness_in H.val.val R hv hiR hjR hvi hvj hvj_ne hdeg
    have hij : i ≠ j := by
      intro heq
      exact hiT (heq ▸ hjT)
    have hdist : FourDistinct v i j k :=
      ⟨hvi.ne, hvj_ne, hkv.symm, hij, hki.symm, hkj.symm⟩
    let K := fourVertexState H.val v i j k hdist
    have hfreeze : FrozenRowsAgree K.val H.val.val R :=
      fourVertexState_frozenRows H.val R v i j k hdist hv hiR hjR hkR hvi hjk hvj hik
    let KA : A := ⟨K, hfreeze.trans H.property⟩
    refine ⟨KA, hmoves H.val v i j k hdist hvi hjk hvj hik, ?_⟩
    exact fourVertexState_residual_neighbors H.val R v i j k hdist hjR hvi hjk hvj hik
  let GA : A := ⟨G, FrozenRowsAgree.refl G.val R⟩
  obtain ⟨H, hpath, hneigh⟩ := reach_target_by_neighbor_swaps rA N T hcard hstep GA
  refine ⟨H.val, ?_, ?_, hneigh⟩
  · exact Relation.ReflTransGen.lift (fun K : A => K.val) (fun _ _ h => h) _ _ hpath
  · intro u hu w
    exact (H.property u hu w).symm

private theorem graphDegree_eq_degree {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (v : Fin n) : graphDegree G v = G.degree v := by
  classical
  unfold graphDegree SimpleGraph.degree
  congr 1
  ext w
  simp

theorem connectivity_of_fourVertex_moves (n : Nat) (d : Fin n → Nat)
    (r : GraphState n d → GraphState n d → Prop)
    (hsymm : ∀ ⦃first second⦄, r first second → r second first)
    (hmoves : ∀ (G : GraphState n d) (a b c e : Fin n) (h : FourDistinct a b c e),
      G.val.Adj a b → G.val.Adj c e → ¬ G.val.Adj a c → ¬ G.val.Adj b e →
      r G (fourVertexState G a b c e h))
    (G H : GraphState n d) : Relation.ReflTransGen r G H := by
  classical
  apply HavelCanonical.connected_of_neighborhood_repair
    (fun K : GraphState n d => K.val) Subtype.val_injective r hsymm _ _ G H
  · intro K L v
    rw [← graphDegree_eq_degree, ← graphDegree_eq_degree]
    exact (K.property v).trans (L.property v).symm
  · intro R T v K hv hTR hsize hsorted
    exact havel_neighborhood_repair_of_moves r hmoves R T v K hv hTR hsize hsorted

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.MatchingCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315.MatchingCount

private theorem involution_fin_four_card :
    Fintype.card (FixedPointFreeInvolution (Fin 4)) = 3 := by
  decide

 theorem involution_card_of_card_four {V : Type*} [Fintype V]
    (hV : Fintype.card V = 4) : Nat.card (FixedPointFreeInvolution V) = 3 := by
  classical
  let e : V ≃ Fin 4 := Fintype.equivFinOfCardEq hV
  rw [Nat.card_congr (involutionCongr e), Nat.card_eq_fintype_card]
  exact involution_fin_four_card

variable {n : ℕ} {S : FourSet n}

theorem perfectMatching_card (S : FourSet n) : Nat.card (PerfectMatching S) = 3 := by
  rw [Nat.card_congr (matchingEquivInvolution S)]
  apply involution_card_of_card_four
  simpa only [Fintype.card_coe] using S.property

theorem orderedMatchings_card (S : FourSet n) :
    Nat.card {p : PerfectMatching S × PerfectMatching S // p.1 ≠ p.2} = 6 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfilter : (Finset.univ.filter fun p : PerfectMatching S × PerfectMatching S => p.1 ≠ p.2) =
      (Finset.univ : Finset (PerfectMatching S)).offDiag := by
    ext p
    simp
  rw [hfilter, Finset.offDiag_card, Finset.card_univ]
  have hcard : Fintype.card (PerfectMatching S) = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact perfectMatching_card S
  rw [hcard]

theorem fourSet_card (n : ℕ) : Nat.card (FourSet n) = n.choose 4 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.univ_filter_card_eq, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

theorem switchProposal_card (n : ℕ) : Nat.card (SwitchProposal n) = 6 * n.choose 4 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  have hcard (S : FourSet n) :
      Fintype.card {p : PerfectMatching S × PerfectMatching S // p.1 ≠ p.2} = 6 := by
    rw [← Nat.card_eq_fintype_card]
    exact orderedMatchings_card S
  simp_rw [hcard]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
    fourSet_card, Nat.mul_comm]

theorem allProposals_card (n : ℕ) : (allProposals n).card = 6 * n.choose 4 := by
  classical
  unfold allProposals
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
  exact switchProposal_card n

end Problem315.MatchingCount

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.KernelNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Problem315

theorem proposal_fiber_cards_sum {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) :
    (∑ H ∈ allGraphStates n d,
      ((allProposals n).filter (fun p => proposalResult G.val p = H.val)).card) =
      (allProposals n).card := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (allProposals n) (allGraphStates n d) (proposalState G)
  have hf (H : GraphState n d) :
      ((allProposals n).filter (fun p => proposalState G p = H)) =
      ((allProposals n).filter (fun p => proposalResult G.val p = H.val)) := by
    ext p
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro _
    exact Subtype.ext_iff
  simp_rw [hf] at h
  simpa only [allGraphStates, Finset.mem_univ, Finset.filter_true] using h

theorem switchKernel_row_sum {n : ℕ} {d : Fin n → ℕ}
    (hn : 4 ≤ n) (G : GraphState n d) :
    (∑ H ∈ allGraphStates n d, switchKernel n d G H) = 1 := by
  classical
  have hc : (Nat.choose n 4 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hn))
  unfold switchKernel
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Nat.cast_sum,
    proposal_fiber_cards_sum, MatchingCount.allProposals_card]
  have hdiag : (∑ H ∈ allGraphStates n d, if G = H then (1 : ℝ) / 2 else 0) = 1 / 2 := by
    simp [allGraphStates]
  rw [hdiag]
  push_cast
  field_simp
  ring

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairAggregation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairAggregation

variable {V : Type*} [DecidableEq V]

lemma card_union_of_pairs {a b : Finset V} (ha : a.card = 2) (hb : b.card = 2)
    (hne : a ≠ b) (hnd : ¬ Disjoint a b) : (a ∪ b).card = 3 := by
  have hi_pos : 0 < (a ∩ b).card := by
    apply Finset.card_pos.mpr
    exact Finset.not_disjoint_iff_nonempty_inter.mp hnd
  have hi_le : (a ∩ b).card ≤ 2 := by
    simpa [ha] using Finset.card_le_card (Finset.inter_subset_left : a ∩ b ⊆ a)
  have hi_ne : (a ∩ b).card ≠ 2 := by
    intro hi
    have hia : a ∩ b = a := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hab : a ⊆ b := by rw [← hia]; exact Finset.inter_subset_right
    exact hne (Finset.eq_of_subset_of_card_le hab (by omega))
  have h := Finset.card_union_add_card_inter a b
  omega

lemma triple_incidence_count (s a b : Finset V) (ha : a.card = 2) (hb : b.card = 2)
    (has : a ⊆ s) (hbs : b ⊆ s) :
    ((s.powersetCard 3).filter (fun T => a ⊆ T ∧ b ⊆ T)).card =
      if a = b then s.card - 2 else if Disjoint a b then 0 else 1 := by
  have hfilter : (s.powersetCard 3).filter (fun T => a ⊆ T ∧ b ⊆ T) =
      (s.powersetCard 3).filter (a ∪ b ⊆ ·) := by
    ext T
    simp only [Finset.mem_filter, Finset.union_subset_iff]
  rw [hfilter]
  by_cases hab : a = b
  · subst b
    simp only [Finset.union_self]
    rw [Finset.card_filter_powersetCard_subset a s 3 has (by omega), ha]
    simp
  · simp only [ite_eq_right hab]
    by_cases hd : Disjoint a b
    · rw [ite_eq_left hd]
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro T hT
      obtain ⟨hT, huT⟩ := Finset.mem_filter.mp hT
      have hcard := Finset.card_le_card huT
      have hTu := (Finset.mem_powersetCard.mp hT).2
      have hu := Finset.card_union_of_disjoint hd
      omega
    · rw [ite_eq_right hd]
      have hu := card_union_of_pairs ha hb hab hd
      rw [Finset.card_filter_powersetCard_subset (a ∪ b) s 3
        (Finset.union_subset has hbs) (by omega), hu]
      simp

lemma sum_triple_incidence (s : Finset V) (B : Finset V → Finset V → ℝ) :
    (∑ T ∈ s.powersetCard 3, ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
      if a ⊆ T ∧ b ⊆ T then B a b else 0) =
    ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
      (((s.powersetCard 3).filter (fun T => a ⊆ T ∧ b ⊆ T)).card : ℝ) * B a b := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← Finset.sum_filter]
  simp

lemma triple_expansion (s : Finset V) (hs : 3 ≤ s.card)
    (B : Finset V → Finset V → ℝ) :
    (∑ T ∈ s.powersetCard 3, ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
      if a ⊆ T ∧ b ⊆ T then B a b else 0) =
    (∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2, B a b) +
      (s.card - 3 : ℕ) * (∑ a ∈ s.powersetCard 2, B a a) -
      (∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
        if Disjoint a b then B a b else 0) := by
  rw [sum_triple_incidence]
  have hpoint : ∀ a ∈ s.powersetCard 2, ∀ b ∈ s.powersetCard 2,
      (((s.powersetCard 3).filter (fun T => a ⊆ T ∧ b ⊆ T)).card : ℝ) * B a b =
        B a b + (if a = b then (s.card - 3 : ℕ) * B a b else 0) -
          (if Disjoint a b then B a b else 0) := by
    intro a ha b hb
    obtain ⟨has, ha⟩ := Finset.mem_powersetCard.mp ha
    obtain ⟨hbs, hb⟩ := Finset.mem_powersetCard.mp hb
    rw [triple_incidence_count s a b ha hb has hbs]
    by_cases he : a = b
    · subst b
      have hnd : ¬ Disjoint a a := by
        intro hd
        have he := disjoint_self.mp hd
        simp [he] at ha
      simp only [ite_eq_right hnd]
      have hc : s.card - 2 = (s.card - 3) + 1 := by omega
      rw [hc]
      push_cast
      ring
    · by_cases hd : Disjoint a b <;> simp [he, hd]
  simp_rw [Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (hpoint a ha))]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  congr 2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp [ha]

lemma sum_pair_terms_over_triples (s : Finset V) (h : Finset V → ℝ) :
    (∑ T ∈ s.powersetCard 3, ∑ a ∈ s.powersetCard 2,
      if a ⊆ T then h a else 0) =
      (s.card - 2 : ℕ) * (∑ a ∈ s.powersetCard 2, h a) := by
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨has, ha⟩ := Finset.mem_powersetCard.mp ha
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_filter_powersetCard_subset a s 3 has (by omega), ha]
  simp

theorem global_of_local_ambient (s : Finset V) (hs : 3 ≤ s.card)
    (h : Finset V → ℝ) (B : Finset V → Finset V → ℝ)
    (hdiag : ∀ a ∈ s.powersetCard 2, B a a = h a)
    (htriple : ∀ T ∈ s.powersetCard 3,
      (∑ a ∈ s.powersetCard 2, if a ⊆ T then h a else 0) ≤
      ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
        if a ⊆ T ∧ b ⊆ T then B a b else 0)
    (hdisjoint : 0 ≤ ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
      if Disjoint a b then B a b else 0) :
    (∑ a ∈ s.powersetCard 2, h a) ≤
      ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2, B a b := by
  have hsum := Finset.sum_le_sum htriple
  rw [sum_pair_terms_over_triples, triple_expansion s hs] at hsum
  have hd : (∑ a ∈ s.powersetCard 2, B a a) =
      ∑ a ∈ s.powersetCard 2, h a := Finset.sum_congr rfl hdiag
  rw [hd] at hsum
  have hc : s.card - 2 = (s.card - 3) + 1 := by omega
  rw [hc] at hsum
  push_cast at hsum
  nlinarith

lemma pairSum_restrict (s T : Finset V) (hTs : T ⊆ s) (f : Finset V → ℝ) :
    (∑ a ∈ s.powersetCard 2, if a ⊆ T then f a else 0) =
      ∑ a ∈ T.powersetCard 2, f a := by
  rw [← Finset.sum_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨has, ha⟩, haT⟩
    exact ⟨haT, ha⟩
  · rintro ⟨haT, ha⟩
    exact ⟨⟨haT.trans hTs, ha⟩, haT⟩

lemma local_quadratic_restrict (s T : Finset V) (hTs : T ⊆ s)
    (B : Finset V → Finset V → ℝ) :
    (∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
      if a ⊆ T ∧ b ⊆ T then B a b else 0) =
      ∑ a ∈ T.powersetCard 2, ∑ b ∈ T.powersetCard 2, B a b := by
  have he : (∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
      if a ⊆ T ∧ b ⊆ T then B a b else 0) =
      ∑ a ∈ s.powersetCard 2, if a ⊆ T then
        (∑ b ∈ s.powersetCard 2, if b ⊆ T then B a b else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    by_cases haT : a ⊆ T <;> simp [haT]
  rw [he, pairSum_restrict s T hTs]
  apply Finset.sum_congr rfl
  intro a ha
  exact pairSum_restrict s T hTs (B a)

theorem global_of_local (s : Finset V) (hs : 3 ≤ s.card)
    (h : Finset V → ℝ) (B : Finset V → Finset V → ℝ)
    (hdiag : ∀ a ∈ s.powersetCard 2, B a a = h a)
    (htriple : ∀ T ∈ s.powersetCard 3,
      (∑ a ∈ T.powersetCard 2, h a) ≤
      ∑ a ∈ T.powersetCard 2, ∑ b ∈ T.powersetCard 2, B a b)
    (hdisjoint : 0 ≤ ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
      if Disjoint a b then B a b else 0) :
    (∑ a ∈ s.powersetCard 2, h a) ≤
      ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2, B a b := by
  apply global_of_local_ambient s hs h B hdiag _ hdisjoint
  intro T hT
  have hTs := (Finset.mem_powersetCard.mp hT).1
  rw [pairSum_restrict s T hTs, local_quadratic_restrict s T hTs]
  exact htriple T hT

end Problem315.PairAggregation

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.OrthogonalPairResampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace Problem315
namespace PairResampling

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {d : Fin n → ℕ} (a : Finset (Fin n))

theorem expectation_isSymmetric :
    (expectation n d a).toLinearMap.IsSymmetric :=
  (fiberSpace n d a).starProjection_isSymmetric

theorem fluctuation_isSymmetric :
    (fluctuation n d a).toLinearMap.IsSymmetric :=
  (fiberSpace n d a)ᗮ.starProjection_isSymmetric

theorem fluctuation_eq_sub (f : StateSpace n d) :
    fluctuation n d a f = f - expectation n d a f := by
  exact (fiberSpace n d a).starProjection_orthogonal_val f

@[simp] theorem fluctuation_eq_zero_iff (f : StateSpace n d) :
    fluctuation n d a f = 0 ↔ f ∈ fiberSpace n d a := by
  rw [fluctuation_eq_sub, sub_eq_zero, eq_comm, expectation_eq_self_iff]

theorem inner_fluctuation (f : StateSpace n d) :
    ⟪f, fluctuation n d a f⟫ = ‖fluctuation n d a f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  have h := ((fluctuation_isSymmetric a) f (fluctuation n d a f)).symm
  change ⟪f, fluctuation n d a (fluctuation n d a f)⟫ =
    ⟪fluctuation n d a f, fluctuation n d a f⟫ at h
  simpa only [fluctuation_idempotent] using h

theorem generator_apply (f : StateSpace n d) :
    generator n d f = ∑ a ∈ pairs n, fluctuation n d a f := by
  simp [generator]

theorem generator_isSymmetric : (generator n d).toLinearMap.IsSymmetric := by
  intro f g
  change ⟪generator n d f, g⟫ = ⟪f, generator n d g⟫
  simp only [generator_apply, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro b hb
  exact fluctuation_isSymmetric b f g

theorem inner_generator (f : StateSpace n d) :
    ⟪f, generator n d f⟫ = ∑ a ∈ pairs n, ‖fluctuation n d a f‖ ^ 2 := by
  simp only [generator_apply, inner_sum, inner_fluctuation]

theorem generator_nonneg (f : StateSpace n d) : 0 ≤ ⟪f, generator n d f⟫ := by
  rw [inner_generator]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem generator_eq_zero_iff (f : StateSpace n d) :
    generator n d f = 0 ↔ ∀ a ∈ pairs n, f ∈ fiberSpace n d a := by
  constructor
  · intro h a ha
    have hz : (∑ b ∈ pairs n, ‖fluctuation n d b f‖ ^ 2) = 0 := by
      rw [← inner_generator, h, inner_zero_right]
    have hterm : ‖fluctuation n d a f‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => sq_nonneg ‖fluctuation n d b f‖)).mp hz a ha
    exact (fluctuation_eq_zero_iff a f).mp
      (norm_eq_zero.mp (sq_eq_zero_iff.mp hterm))
  · intro h
    rw [generator_apply]
    apply Finset.sum_eq_zero
    intro a ha
    exact (fluctuation_eq_zero_iff a f).mpr (h a ha)

theorem state_inner (f g : StateSpace n d) :
    ⟪f, g⟫ = ∑ G : GraphState n d, f G * g G := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

theorem constant_mem (c : ℝ) :
    WithLp.toLp 2 (fun _ : GraphState n d => c) ∈ fiberSpace n d a := by
  intro G H h
  rfl

@[simp] theorem generator_constant (c : ℝ) :
    generator n d (WithLp.toLp 2 (fun _ : GraphState n d => c)) = 0 := by
  apply (generator_eq_zero_iff _).mpr
  intro a ha
  exact constant_mem a c

theorem fiberStates_nonempty (G : GraphState n d) : (fiberStates a G).Nonempty :=
  ⟨G, self_mem_fiberStates a G⟩

theorem fiberIndicator_mem (G : GraphState n d) :
    fiberIndicator a G ∈ fiberSpace n d a := by
  intro H K hHK
  change (if SameFiber a G.val H.val then (1 : ℝ) else 0) =
    if SameFiber a G.val K.val then 1 else 0
  have hi : SameFiber a G.val H.val ↔ SameFiber a G.val K.val :=
    ⟨fun h => h.trans hHK, fun h => h.trans hHK.symm⟩
  simp only [hi]

theorem expectation_eq_average (f : StateSpace n d) (G : GraphState n d) :
    expectation n d a f G = (∑ H ∈ fiberStates a G, f H) / (fiberStates a G).card := by
  have horth := Submodule.starProjection_inner_eq_zero (K := fiberSpace n d a)
    f (fiberIndicator a G) (fiberIndicator_mem a G)
  change ⟪f - expectation n d a f, fiberIndicator a G⟫ = 0 at horth
  rw [state_inner] at horth
  have hsum : (∑ H ∈ fiberStates a G, (f H - expectation n d a f H)) = 0 := by
    calc
      _ = ∑ H : GraphState n d, (f - expectation n d a f) H * fiberIndicator a G H := by
        unfold fiberStates
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro H hH
        by_cases h : SameFiber a G.val H.val <;> simp [fiberIndicator, h]
      _ = 0 := horth
  have hequal : ∀ H ∈ fiberStates a G, expectation n d a f H = expectation n d a f G := by
    intro H hH
    exact (expectation_mem a f) H G ((mem_fiberStates a G H).mp hH).symm
  have hsconst : (∑ H ∈ fiberStates a G, expectation n d a f H) =
      (fiberStates a G).card * expectation n d a f G := by
    calc
      _ = ∑ _H ∈ fiberStates a G, expectation n d a f G := Finset.sum_congr rfl hequal
      _ = _ := by simp
  rw [Finset.sum_sub_distrib, hsconst] at hsum
  have hcard : (0 : ℝ) < (fiberStates a G).card := by
    exact_mod_cast Finset.card_pos.mpr (fiberStates_nonempty a G)
  apply (eq_div_iff (ne_of_gt hcard)).mpr
  linarith

end PairResampling
end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairFiberRedundancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315.PairResampling

attribute [local instance] Classical.propDecidable

theorem degree_eq_inside_add_outside {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Finset (Fin n)) (w : Fin n) :
    graphDegree G w = (a.filter (G.Adj w)).card +
      ((Finset.univ.filter (G.Adj w)).filter (fun v => v ∉ a)).card := by
  have h := (Finset.univ.filter (G.Adj w)).card_filter_add_card_filter_not
    (fun v => v ∈ a)
  have hin : (Finset.univ.filter (G.Adj w)).filter (fun v => v ∈ a) =
      a.filter (G.Adj w) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hin] at h
  exact h.symm

theorem inside_count_eq_of_degrees_outside {n : ℕ}
    {G H : SimpleGraph (Fin n)} (a : Finset (Fin n))
    (hdegree : ∀ w, graphDegree G w = graphDegree H w)
    (hout : ∀ u ∉ a, ∀ v ∉ a, G.Adj u v ↔ H.Adj u v)
    (w : Fin n) (hw : w ∉ a) :
    (a.filter (G.Adj w)).card = (a.filter (H.Adj w)).card := by
  have hs : (Finset.univ.filter (G.Adj w)).filter (fun v => v ∉ a) =
      (Finset.univ.filter (H.Adj w)).filter (fun v => v ∉ a) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hG, hv⟩
      exact ⟨(hout w hw v hv).mp hG, hv⟩
    · rintro ⟨hH, hv⟩
      exact ⟨(hout w hw v hv).mpr hH, hv⟩
  have h := hdegree w
  rw [degree_eq_inside_add_outside G a w, degree_eq_inside_add_outside H a w,
    hs] at h
  exact Nat.add_right_cancel h

theorem sameFiber_iff_outside_inside {n : ℕ} {d : Fin n → ℕ}
    (a : Finset (Fin n)) (G H : GraphState n d) :
    SameFiber a G.val H.val ↔
      (∀ u ∉ a, ∀ v ∉ a, G.val.Adj u v ↔ H.val.Adj u v) ∧
      (∀ u ∈ a, ∀ v ∈ a, G.val.Adj u v ↔ H.val.Adj u v) := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · rintro ⟨hout, hin⟩
    refine ⟨hout, hin, ?_⟩
    exact inside_count_eq_of_degrees_outside a
      (fun w => (G.property w).trans (H.property w).symm) hout

end Problem315.PairResampling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairFiberConnectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315.PairResampling

attribute [local instance] Classical.propDecidable

theorem fourVertexState_sameFiber {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (a b c e : Fin n) (h : FourDistinct a b c e)
    (hab : G.val.Adj a b) (hce : G.val.Adj c e)
    (hac : ¬ G.val.Adj a c) (hbe : ¬ G.val.Adj b e) :
    SameFiber {a, e} G.val (fourVertexState G a b c e h).val := by
  apply (sameFiber_iff_outside_inside {a, e} G _).mpr
  constructor
  · intro u hu v hv
    have hua : u ≠ a := fun h' => hu (by simp [h'])
    have hue : u ≠ e := fun h' => hu (by simp [h'])
    have hva : v ≠ a := fun h' => hv (by simp [h'])
    have hve : v ≠ e := fun h' => hv (by simp [h'])
    change G.val.Adj u v ↔
      (proposalResult G.val (fourVertexProposal a b c e h)).Adj u v
    rw [proposalResult_fourVertex_adj G.val a b c e h hab hce hac hbe]
    simp [hua, hue, hva, hve]
  · intro u hu v hv
    have hub : u ≠ b := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact h.1
      · exact h.2.2.2.2.1.symm
    have huc : u ≠ c := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact h.2.1
      · exact h.2.2.2.2.2.symm
    have hvb : v ≠ b := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact h.1
      · exact h.2.2.2.2.1.symm
    have hvc : v ≠ c := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact h.2.1
      · exact h.2.2.2.2.2.symm
    change G.val.Adj u v ↔
      (proposalResult G.val (fourVertexProposal a b c e h)).Adj u v
    rw [proposalResult_fourVertex_adj G.val a b c e h hab hce hac hbe]
    simp [hub, huc, hvb, hvc]

theorem fiberMove_connectivity (n : Nat) (d : Fin n → Nat) (G H : GraphState n d) :
    Relation.ReflTransGen (FiberMove n d) G H := by
  apply connectivity_of_fourVertex_moves n d (FiberMove n d) _ _ G H
  · intro K L h
    obtain ⟨a, ha, hfiber⟩ := h
    exact ⟨a, ha, hfiber.symm⟩
  · intro K a b c e h hab hce hac hbe
    refine ⟨{a, e}, ?_, fourVertexState_sameFiber K a b c e h hab hce hac hbe⟩
    simp [pairs, Finset.mem_powersetCard, h.2.2.1]

theorem generator_eq_zero_iff_constant {n : Nat} {d : Fin n → Nat}
    (f : StateSpace n d) :
    generator n d f = 0 ↔ ∀ G H : GraphState n d, f G = f H := by
  constructor
  · intro hf G H
    have hconst := (generator_eq_zero_iff f).mp hf
    have hpath := fiberMove_connectivity n d G H
    induction hpath with
    | refl => rfl
    | @tail K L hGK hKL ih =>
      obtain ⟨a, ha, hsame⟩ := hKL
      exact ih.trans (hconst a ha K L hsame)
  · intro hf
    apply (generator_eq_zero_iff f).mpr
    intro a ha G H _
    exact hf G H

end Problem315.PairResampling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SpectralFromSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace Problem315.Analytic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem norm_sq_le_inner_of_square_ge
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hpos : ∀ x : E, 0 ≤ ⟪x, T x⟫)
    (hsquare : ∀ x : E, ⟪x, T x⟫ ≤ ⟪T x, T x⟫)
    (x : E) (hx : ∀ y : E, T y = 0 → ⟪y, x⟫ = 0) :
    ‖x‖ ^ 2 ≤ ⟪x, T x⟫ := by
  classical
  let b := hT.eigenvectorBasis (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  let ev := hT.eigenvalues (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  have hbe (i : Fin (Module.finrank ℝ E)) : T (b i) = ev i • b i :=
    hT.apply_eigenvectorBasis rfl i
  have hunit (i : Fin (Module.finrank ℝ E)) : ⟪b i, b i⟫ = 1 :=
    by rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i]; norm_num
  have hevpos (i : Fin (Module.finrank ℝ E)) : 0 ≤ ev i := by
    simpa only [hbe, inner_smul_right, hunit, mul_one] using hpos (b i)
  have hevsquare (i : Fin (Module.finrank ℝ E)) : ev i ≤ (ev i) ^ 2 := by
    simpa only [hbe, inner_smul_left, inner_smul_right, hunit, mul_one,
      RCLike.conj_to_real, pow_two] using hsquare (b i)
  rw [← b.sum_sq_inner_right x, ← b.sum_inner_mul_inner x (T x)]
  apply Finset.sum_le_sum
  intro i hi
  have hcoord : ⟪b i, T x⟫ = ev i * ⟪b i, x⟫ := by
    rw [← hT (b i) x, hbe, inner_smul_left]
    simp
  have hcomm : ⟪x, b i⟫ = ⟪b i, x⟫ := real_inner_comm _ _
  rw [hcoord, hcomm]
  by_cases he : ev i = 0
  · have hz : ⟪b i, x⟫ = 0 := hx (b i) (by simp [hbe, he])
    simp [hz]
  · have hone : 1 ≤ ev i := by
      have hp := hevpos i
      have hs := hevsquare i
      have hp' : 0 < ev i := lt_of_le_of_ne hp (Ne.symm he)
      nlinarith
    nlinarith [sq_nonneg ⟪b i, x⟫]

end Problem315.Analytic

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairPoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.PairResampling
attribute [local instance] Classical.propDecidable

theorem generator_centered_poincare {n : Nat} {d : Fin n → Nat}
    (hsquare : ∀ f : StateSpace n d,
      ⟪f, generator n d f⟫ ≤ ⟪generator n d f, generator n d f⟫)
    (f : StateSpace n d) (hf : ∑ G : GraphState n d, f G = 0) :
    ‖f‖ ^ 2 ≤ ⟪f, generator n d f⟫ := by
  classical
  apply Analytic.norm_sq_le_inner_of_square_ge (generator n d).toLinearMap
    generator_isSymmetric generator_nonneg hsquare f
  intro y hy
  have hconst := (generator_eq_zero_iff_constant y).mp hy
  by_cases hne : Nonempty (GraphState n d)
  · let G : GraphState n d := Classical.choice hne
    rw [state_inner]
    simp_rw [hconst _ G]
    rw [← Finset.mul_sum, hf, mul_zero]
  · have : IsEmpty (GraphState n d) := not_nonempty_iff.mp hne
    simp [state_inner]

theorem uniformVariance_le_generator {n : Nat} {d : Fin n → Nat}
    (hgraph : Graphical n d)
    (hsquare : ∀ f : StateSpace n d,
      ⟪f, generator n d f⟫ ≤ ⟪generator n d f, generator n d f⟫)
    (f : GraphState n d → ℝ) :
    uniformVariance n d f ≤
      ⟪WithLp.toLp 2 f, generator n d (WithLp.toLp 2 f)⟫ / (stateCount n d : ℝ) := by
  classical
  let : Nonempty (GraphState n d) := hgraph
  have hN : (0 : ℝ) < (stateCount n d : ℝ) := by
    exact_mod_cast (show 0 < stateCount n d by
      simpa only [stateCount, allGraphStates, Finset.card_univ] using
        (Fintype.card_pos (α := GraphState n d)))
  let v : StateSpace n d := WithLp.toLp 2 f
  let c : ℝ := uniformAverage n d f
  let k : StateSpace n d := WithLp.toLp 2 (fun _ : GraphState n d => c)
  let x : StateSpace n d := v - k
  have hx : (∑ G : GraphState n d, x G) = 0 := by
    simp only [x, v, k, PiLp.sub_apply]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change (∑ G : GraphState n d, f G) - (Fintype.card (GraphState n d) : ℝ) *
      ((∑ G : GraphState n d, f G) / (stateCount n d : ℝ)) = 0
    have hcard : (Fintype.card (GraphState n d) : ℝ) = stateCount n d := rfl
    rw [hcard]
    field_simp
    ring
  have hk : generator n d k = 0 := generator_constant c
  have hgen : generator n d x = generator n d v := by
    change generator n d (v - k) = generator n d v
    rw [map_sub, hk, sub_zero]
  have horth : ⟪k, generator n d v⟫ = 0 := by
    have h := generator_isSymmetric (n := n) (d := d) k v
    change ⟪generator n d k, v⟫ = ⟪k, generator n d v⟫ at h
    rw [hk, inner_zero_left] at h
    exact h.symm
  have henergy : ⟪x, generator n d x⟫ = ⟪v, generator n d v⟫ := by
    rw [hgen]
    change ⟪v - k, generator n d v⟫ = _
    rw [inner_sub_left, horth, sub_zero]
  have hnorm : ‖x‖ ^ 2 = ∑ G ∈ allGraphStates n d, (f G - c) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, state_inner]
    simp only [x, v, k, PiLp.sub_apply, allGraphStates, pow_two]
  have hp := generator_centered_poincare hsquare x hx
  rw [henergy, hnorm] at hp
  exact div_le_div_of_nonneg_right hp (le_of_lt hN)

end Problem315.PairResampling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairGeneratorSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling

attribute [local instance] Classical.propDecidable

theorem tripleGenerator_apply {n : Nat} {d : Fin n → Nat}
    (T : Finset (Fin n)) (f : StateSpace n d) :
    tripleGenerator n d T f = ∑ a ∈ T.powersetCard 2, fluctuation n d a f := by
  simp [tripleGenerator]

theorem inner_tripleGenerator {n : Nat} {d : Fin n → Nat}
    (T : Finset (Fin n)) (f : StateSpace n d) :
    ⟪f, tripleGenerator n d T f⟫ =
      ∑ a ∈ T.powersetCard 2, ‖fluctuation n d a f‖ ^ 2 := by
  simp only [tripleGenerator_apply, inner_sum, inner_fluctuation]

theorem generator_square_of_local {n : Nat} {d : Fin n → Nat}
    (hn : 3 ≤ n) (f : StateSpace n d)
    (htriple : ∀ T : Finset (Fin n), T.card = 3 →
      ⟪f, tripleGenerator n d T f⟫ ≤
        ⟪tripleGenerator n d T f, tripleGenerator n d T f⟫)
    (hdisjoint : 0 ≤ ∑ a ∈ pairs n, ∑ b ∈ pairs n,
      if Disjoint a b then ⟪fluctuation n d a f, fluctuation n d b f⟫ else 0) :
    ⟪f, generator n d f⟫ ≤ ⟪generator n d f, generator n d f⟫ := by
  rw [inner_generator]
  simp only [generator_apply]
  simp only [sum_inner]
  simp only [inner_sum]
  apply PairAggregation.global_of_local (Finset.univ : Finset (Fin n)) (by simpa using hn)
    (fun a => ‖fluctuation n d a f‖ ^ 2)
    (fun a b => ⟪fluctuation n d a f, fluctuation n d b f⟫)
  · intro a ha
    exact real_inner_self_eq_norm_sq _
  · intro T hT
    have hcard := (Finset.mem_powersetCard.mp hT).2
    have h := htriple T hcard
    rw [inner_tripleGenerator] at h
    simp only [tripleGenerator_apply] at h
    simp only [sum_inner] at h
    simp only [inner_sum] at h
    exact h
  · exact hdisjoint

end Problem315.PairResampling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairFiberEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315.PairFiber

variable {V : Type*} [Fintype V]

theorem assignment_natCard (G : SimpleGraph V) (i j : V) :
    Nat.card (Assignment G i j) =
      Nat.choose (singletonSet G i j).card (leftSet G i j).card := by
  classical
  let e : Assignment G i j ≃ ((singletonSet G i j).powersetCard (leftSet G i j).card) :=
    { toFun := fun T => ⟨T.val, Finset.mem_powersetCard.mpr T.property⟩
      invFun := fun T => ⟨T.val, Finset.mem_powersetCard.mp T.property⟩
      left_inv := fun T => by apply Subtype.ext; rfl
      right_inv := fun T => by apply Subtype.ext; rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_powersetCard]

end Problem315.PairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairFiberBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairFiber
attribute [local instance] Classical.propDecidable

variable {n : Nat}

theorem fiberStates_card {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) :
    (PairResampling.fiberStates {i, j} G).card =
      Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card := by
  classical
  calc
    _ = Nat.card (PairResampling.fiberStates {i, j} G) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = Nat.card (Assignment G.val i j) := Nat.card_congr (resamplingFiberEquiv G i j hij)
    _ = _ := assignment_natCard G.val i j

theorem expectation_eq_assignment_average {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (f : PairResampling.StateSpace n d) :
    PairResampling.expectation n d {i, j} f G =
      (∑ T : Assignment G.val i j, f ((stateFiberEquiv G i j hij).symm T).val) /
        (Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card : ℝ) := by
  classical
  rw [PairResampling.expectation_eq_average, fiberStates_card G i j hij]
  congr 1
  rw [← Finset.sum_coe_sort]
  exact ((resamplingFiberEquiv G i j hij).symm.sum_comp
    (fun H : (PairResampling.fiberStates {i, j} G) => f H.val)).symm

end Problem315.PairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PermutationFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Equiv

namespace Problem315.PermutationFactors

variable {α : Type*} [DecidableEq α]

theorem swapFactorsAux_length_le (l : List α) (σ : Perm α)
    (h : ∀ {x}, σ x ≠ x → x ∈ l) :
    (Perm.swapFactorsAux l σ h).val.length ≤ l.length := by
  induction l generalizing σ with
  | nil => simp [Perm.swapFactorsAux]
  | cons x l ih =>
    rw [Perm.swapFactorsAux]
    dsimp only
    split_ifs with hfix
    · have htail : ∀ {y}, σ y ≠ y → y ∈ l := by
        intro y hy
        exact List.mem_of_ne_of_mem (fun hyx => by simp [hyx, hfix.symm] at hy) (h hy)
      exact (ih σ htail).trans (Nat.le_succ _)
    · have htail : ∀ {y}, (swap x (σ x) * σ) y ≠ y → y ∈ l := by
        intro y hy
        have hh := Perm.ne_and_ne_of_swap_mul_apply_ne_self hy
        exact List.mem_of_ne_of_mem hh.2 (h hh.1)
      simpa only [List.length_cons] using
        Nat.succ_le_succ (ih (swap x (σ x) * σ) htail)

theorem exists_swap_factors_length_le [Fintype α] (σ : Perm α) :
    ∃ l : List (Perm α), l.prod = σ ∧
      (∀ τ ∈ l, Perm.IsSwap τ) ∧ l.length ≤ Fintype.card α := by
  classical
  let support : List α := Finset.univ.toList
  have hsupport : ∀ {x}, σ x ≠ x → x ∈ support := by
    intro x _
    simp [support]
  let factors := Perm.swapFactorsAux support σ hsupport
  refine ⟨factors.val, factors.property.1, factors.property.2, ?_⟩
  have h := swapFactorsAux_length_le support σ hsupport
  simpa only [factors, support, Finset.length_toList, Finset.card_univ] using h

end Problem315.PermutationFactors

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PermutationPathComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PermutationPaths

theorem path_squared_difference_le {α : Type*} [Fintype α]
    (f : α → ℝ) (p : ℕ → α → α) (N : ℕ) :
    (∑ x, (f (p 0 x) - f (p N x)) ^ 2) ≤
      (N : ℝ) * ∑ i ∈ Finset.range N,
        ∑ x, (f (p i x) - f (p (i + 1) x)) ^ 2 := by
  have hpoint (x : α) : (f (p 0 x) - f (p N x)) ^ 2 ≤
      (N : ℝ) * ∑ i ∈ Finset.range N,
        (f (p i x) - f (p (i + 1) x)) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range N)
      (f := fun i => f (p i x) - f (p (i + 1) x))
    simpa only [Finset.sum_range_sub', Finset.card_range] using h
  calc
    (∑ x, (f (p 0 x) - f (p N x)) ^ 2)
        ≤ ∑ x, (N : ℝ) * ∑ i ∈ Finset.range N,
            (f (p i x) - f (p (i + 1) x)) ^ 2 :=
      Finset.sum_le_sum fun x _ => hpoint x
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

theorem permutation_path_energy_le {α : Type*} [Fintype α]
    (f : α → ℝ) (S : Finset (Equiv.Perm α))
    (p : ℕ → Equiv.Perm α) (N : ℕ)
    (hstep : ∀ i < N, ∃ s ∈ S, p (i + 1) = s * p i) :
    (∑ x, (f (p 0 x) - f (p N x)) ^ 2) ≤
      (N : ℝ) ^ 2 * ∑ s ∈ S, ∑ x, (f x - f (s x)) ^ 2 := by
  classical
  let B : ℝ := ∑ s ∈ S, ∑ x, (f x - f (s x)) ^ 2
  have hone (i : ℕ) (hi : i ∈ Finset.range N) :
      (∑ x, (f (p i x) - f (p (i + 1) x)) ^ 2) ≤ B := by
    obtain ⟨s, hs, hsi⟩ := hstep i (Finset.mem_range.mp hi)
    calc
      (∑ x, (f (p i x) - f (p (i + 1) x)) ^ 2)
          = ∑ x, (f x - f (s x)) ^ 2 := by
        apply Fintype.sum_equiv (p i)
        intro x
        rw [hsi, Equiv.Perm.mul_apply]
      _ ≤ B := by
        dsimp [B]
        exact Finset.single_le_sum
          (fun t _ => show 0 ≤ ∑ x, (f x - f (t x)) ^ 2 from
            Finset.sum_nonneg fun x _ => sq_nonneg _) hs
  calc
    (∑ x, (f (p 0 x) - f (p N x)) ^ 2)
        ≤ (N : ℝ) * ∑ i ∈ Finset.range N,
          ∑ x, (f (p i x) - f (p (i + 1) x)) ^ 2 :=
      path_squared_difference_le f (fun i => p i) N
    _ ≤ (N : ℝ) * ∑ _i ∈ Finset.range N, B := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hone) (Nat.cast_nonneg _)
    _ = (N : ℝ) ^ 2 * ∑ s ∈ S, ∑ x, (f x - f (s x)) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      dsimp [B]
      ring

theorem sum_group_apply_eq {α G : Type*} [Fintype α] [Nonempty α]
    [Group G] [Fintype G] (ρ : G →* Equiv.Perm α)
    (htrans : ∀ x y : α, ∃ g : G, ρ g x = y) (f : α → ℝ) (x : α) :
    (∑ g : G, f (ρ g x)) =
      (Fintype.card G : ℝ) / Fintype.card α * ∑ y, f y := by
  have hsame (y : α) : (∑ g : G, f (ρ g y)) = ∑ g : G, f (ρ g x) := by
    obtain ⟨h, rfl⟩ := htrans x y
    apply Fintype.sum_equiv (Equiv.mulRight h)
    intro g
    simp [map_mul, Equiv.Perm.mul_apply]
  have hsum (g : G) : (∑ y, f (ρ g y)) = ∑ y, f y := by
    exact Fintype.sum_equiv (ρ g) _ _ (fun _ => rfl)
  have hid : (Fintype.card α : ℝ) * (∑ g : G, f (ρ g x)) =
      (Fintype.card G : ℝ) * ∑ y, f y := by
    calc
      (Fintype.card α : ℝ) * (∑ g : G, f (ρ g x))
          = ∑ y : α, ∑ g : G, f (ρ g y) := by simp [hsame]
      _ = ∑ g : G, ∑ y : α, f (ρ g y) := Finset.sum_comm
      _ = _ := by simp [hsum]
  have hc : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hc).2
  simpa [mul_comm] using hid

theorem sum_pairwise_sq_eq {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) :
    (∑ x, ∑ y, (f x - f y) ^ 2) =
      2 * (Fintype.card α : ℝ) *
        ∑ x, (f x - (∑ y, f y) / Fintype.card α) ^ 2 := by
  let μ : ℝ := (∑ y, f y) / Fintype.card α
  have hc : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcenter : (∑ x, (f x - μ)) = 0 := by
    simp [μ, Finset.sum_sub_distrib, hc, mul_div_cancel₀]
  change _ = 2 * (Fintype.card α : ℝ) * ∑ x, (f x - μ) ^ 2
  calc
    (∑ x, ∑ y, (f x - f y) ^ 2) =
        ∑ x, ∑ y, ((f x - μ) ^ 2 + (f y - μ) ^ 2 -
          2 * (f x - μ) * (f y - μ)) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = _ := by
      simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hcenter]
      simp only [mul_zero, Finset.sum_const_zero, sub_zero, Finset.card_univ]
      rw [← Finset.mul_sum]
      ring

theorem sum_group_squared_difference_eq {α G : Type*} [Fintype α] [Nonempty α]
    [Group G] [Fintype G] (ρ : G →* Equiv.Perm α)
    (htrans : ∀ x y : α, ∃ g : G, ρ g x = y) (f : α → ℝ) :
    (∑ g : G, ∑ x, (f x - f (ρ g x)) ^ 2) =
      2 * (Fintype.card G : ℝ) *
        ∑ x, (f x - (∑ y, f y) / Fintype.card α) ^ 2 := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    (∑ g : G, ∑ x, (f x - f (ρ g x)) ^ 2)
        = ∑ x, ∑ g : G, (f x - f (ρ g x)) ^ 2 := Finset.sum_comm
    _ = ∑ x, (Fintype.card G : ℝ) / Fintype.card α *
        ∑ y, (f x - f y) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      exact sum_group_apply_eq ρ htrans (fun y => (f x - f y) ^ 2) x
    _ = (Fintype.card G : ℝ) / Fintype.card α *
        (∑ x, ∑ y, (f x - f y) ^ 2) := (Finset.mul_sum _ _ _).symm
    _ = _ := by
      rw [sum_pairwise_sq_eq f]
      field_simp

theorem variance_le_generator_energy {α G : Type*} [Fintype α] [Nonempty α]
    [Group G] [Fintype G] (ρ : G →* Equiv.Perm α)
    (htrans : ∀ x y : α, ∃ g : G, ρ g x = y)
    (S : Finset (Equiv.Perm α)) (N : ℕ)
    (hpaths : ∀ g : G, ∃ (p : ℕ → Equiv.Perm α) (L : ℕ),
      L ≤ N ∧ p 0 = 1 ∧ p L = ρ g ∧
        ∀ i < L, ∃ s ∈ S, p (i + 1) = s * p i)
    (f : α → ℝ) :
    (∑ x, (f x - (∑ y, f y) / Fintype.card α) ^ 2) ≤
      (N : ℝ) ^ 2 / 2 * ∑ s ∈ S, ∑ x, (f x - f (s x)) ^ 2 := by
  classical
  let B : ℝ := ∑ s ∈ S, ∑ x, (f x - f (s x)) ^ 2
  have hB : 0 ≤ B := Finset.sum_nonneg fun s _ =>
    Finset.sum_nonneg fun x _ => sq_nonneg _
  have hbound (g : G) : (∑ x, (f x - f (ρ g x)) ^ 2) ≤ (N : ℝ) ^ 2 * B := by
    obtain ⟨p, L, hLN, hzero, hend, hstep⟩ := hpaths g
    have hpath := permutation_path_energy_le f S p L hstep
    simp only [hzero, hend, Equiv.Perm.one_apply] at hpath
    calc
      (∑ x, (f x - f (ρ g x)) ^ 2) ≤ (L : ℝ) ^ 2 * B := hpath
      _ ≤ (N : ℝ) ^ 2 * B := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg L) (by exact_mod_cast hLN) 2) hB
  have hsum : 2 * (Fintype.card G : ℝ) *
      (∑ x, (f x - (∑ y, f y) / Fintype.card α) ^ 2) ≤
      (Fintype.card G : ℝ) * ((N : ℝ) ^ 2 * B) := by
    rw [← sum_group_squared_difference_eq ρ htrans f]
    calc
      _ ≤ ∑ _g : G, (N : ℝ) ^ 2 * B := Finset.sum_le_sum fun g _ => hbound g
      _ = _ := by simp
  have hG : 0 < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcancel : 2 * (∑ x, (f x - (∑ y, f y) / Fintype.card α) ^ 2) ≤
      (N : ℝ) ^ 2 * B := by
    apply (mul_le_mul_iff_right₀ hG).mp
    nlinarith [hsum]
  change _ ≤ (N : ℝ) ^ 2 / 2 * B
  linarith

theorem exists_path_of_word {α : Type*} (S : Finset (Equiv.Perm α))
    (l : List (Equiv.Perm α)) (hl : ∀ s ∈ l, s ∈ S) :
    ∃ p : ℕ → Equiv.Perm α, p 0 = 1 ∧ p l.length = l.prod ∧
      ∀ i < l.length, ∃ s ∈ S, p (i + 1) = s * p i := by
  classical
  induction l with
  | nil =>
      exact ⟨fun _ => 1, rfl, rfl, by simp⟩
  | cons s l ih =>
      obtain ⟨p, hp0, hpend, hpstep⟩ := ih (fun t ht => hl t (List.mem_cons_of_mem s ht))
      let q : ℕ → Equiv.Perm α := fun i => if i ≤ l.length then p i else s * p l.length
      refine ⟨q, ?_, ?_, ?_⟩
      · simp [q, hp0]
      · simp [q, hpend]
      · intro i hi
        simp only [List.length_cons] at hi
        by_cases hil : i < l.length
        · obtain ⟨t, ht, hti⟩ := hpstep i hil
          refine ⟨t, ht, ?_⟩
          simpa [q, Nat.le_of_lt hil, Nat.succ_le_of_lt hil] using hti
        · have hieq : i = l.length := by omega
          subst i
          refine ⟨s, hl s (List.mem_cons_self ..), ?_⟩
          simp [q]

theorem variance_le_generator_energy_of_words {α G : Type*}
    [Fintype α] [Nonempty α] [Group G] [Fintype G]
    (ρ : G →* Equiv.Perm α)
    (htrans : ∀ x y : α, ∃ g : G, ρ g x = y)
    (S : Finset (Equiv.Perm α)) (N : ℕ)
    (hwords : ∀ g : G, ∃ l : List (Equiv.Perm α),
      l.length ≤ N ∧ l.prod = ρ g ∧ ∀ s ∈ l, s ∈ S)
    (f : α → ℝ) :
    (∑ x, (f x - (∑ y, f y) / Fintype.card α) ^ 2) ≤
      (N : ℝ) ^ 2 / 2 * ∑ s ∈ S, ∑ x, (f x - f (s x)) ^ 2 := by
  apply variance_le_generator_energy ρ htrans S N ?_ f
  intro g
  obtain ⟨l, hlength, hprod, hletters⟩ := hwords g
  obtain ⟨p, hp0, hpend, hpstep⟩ := exists_path_of_word S l hletters
  exact ⟨p, l.length, hlength, hp0, hpend.trans hprod, hpstep⟩

end Problem315.PermutationPaths

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SlicePermutationAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SlicePermutationAction

variable {α : Type*} [sectionFintypeα : Fintype α] [sectionDecidableEqα : DecidableEq α]

theorem exists_perm_map_eq (s t : Finset α) (hcard : s.card = t.card) :
    ∃ σ : Equiv.Perm α, s.map σ.toEmbedding = t := by
  classical
  let e : s ≃ t := Fintype.equivOfCardEq (by simpa using hcard)
  let σ : Equiv.Perm α := e.extendSubtype
  refine ⟨σ, Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    exact e.extendSubtype_mem x hx
  · simpa using hcard.ge

theorem sum_relabel {q : ℕ} (σ : Equiv.Perm α) (f : Slice α q → ℝ) :
    (∑ s : Slice α q, f (relabel σ s)) = ∑ s : Slice α q, f s :=
  Equiv.sum_comp (relabelEquiv σ) f

theorem relabelEquiv_list_prod {q : ℕ} (l : List (Equiv.Perm α)) :
    relabelEquiv (q := q) l.prod = (l.map relabelEquiv).prod :=
  map_list_prod (relabelHom q) l

theorem exists_relabel_eq {q : ℕ} (s t : Slice α q) :
    ∃ σ : Equiv.Perm α, relabel σ s = t := by
  obtain ⟨σ, hσ⟩ := exists_perm_map_eq s.val t.val (s.property.trans t.property.symm)
  exact ⟨σ, Subtype.ext hσ⟩

end Problem315.SlicePermutationAction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SlicePathComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Problem315.SlicePermutationAction

namespace Problem315.SlicePathComparison

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem variance_le_swap_squared_differences {q : ℕ} [Nonempty (Slice α q)]
    (f : Slice α q → ℝ) :
    (∑ s, (f s - (∑ t, f t) / (Fintype.card (Slice α q) : ℝ)) ^ 2) ≤
      (Fintype.card α : ℝ) ^ 2 / 2 *
        ∑ σ ∈ swaps, ∑ s, (f s - f (relabel σ s)) ^ 2 := by
  classical
  let S : Finset (Equiv.Perm (Slice α q)) := swaps.image relabelEquiv
  have hwords (σ : Equiv.Perm α) :
      ∃ l : List (Equiv.Perm (Slice α q)), l.length ≤ Fintype.card α ∧
        l.prod = relabelHom q σ ∧ ∀ τ ∈ l, τ ∈ S := by
    obtain ⟨l, hprod, hswap, hlen⟩ := PermutationFactors.exists_swap_factors_length_le σ
    refine ⟨l.map relabelEquiv, by simpa using hlen, ?_, ?_⟩
    · rw [← relabelEquiv_list_prod, hprod]
      rfl
    · intro τ hτ
      obtain ⟨υ, hυ, rfl⟩ := List.mem_map.mp hτ
      exact Finset.mem_image.mpr ⟨υ, (mem_swaps υ).mpr (hswap υ hυ), rfl⟩
  have h := PermutationPaths.variance_le_generator_energy_of_words
    (relabelHom q) (fun s t => exists_relabel_eq s t) S (Fintype.card α) hwords f
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact Finset.sum_image_le_of_nonneg (fun τ _ =>
    Finset.sum_nonneg fun s _ => sq_nonneg (f s - f (τ s)))

theorem relabel_displacement_eq_twice_energy {q : ℕ}
    (σ : Equiv.Perm α) (f : Slice α q → ℝ) :
    (∑ s, (f s - f (relabel σ s)) ^ 2) =
      2 * (∑ s, f s * (f s - f (relabel σ s))) := by
  have hnorm := sum_relabel σ (fun s => (f s) ^ 2)
  simp only [sub_sq, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum, ← sq]
  rw [hnorm]
  ring

theorem variance_le_card_sq_swap_energy {q : ℕ} [Nonempty (Slice α q)]
    (f : Slice α q → ℝ) :
    (∑ s, (f s - (∑ t, f t) / (Fintype.card (Slice α q) : ℝ)) ^ 2) ≤
      (Fintype.card α : ℝ) ^ 2 *
        ∑ s, f s * (∑ σ ∈ swaps, (f s - f (relabel σ s))) := by
  have h := variance_le_swap_squared_differences f
  simp_rw [relabel_displacement_eq_twice_energy] at h
  rw [← Finset.mul_sum] at h
  have hcomm : (∑ σ ∈ swaps, ∑ s, f s * (f s - f (relabel σ s))) =
      ∑ s, f s * (∑ σ ∈ swaps, (f s - f (relabel σ s))) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    exact (Finset.mul_sum _ _ _).symm
  rw [hcomm] at h
  nlinarith [h]

theorem variance_le_card_sq_transport {q : ℕ} {X : Type*} [Fintype X] [Nonempty X]
    (e : X ≃ Slice α q) (f : X → ℝ) :
    (∑ x, (f x - (∑ y, f y) / (Fintype.card X : ℝ)) ^ 2) ≤
      (Fintype.card α : ℝ) ^ 2 *
        ∑ x, f x * (∑ σ ∈ swaps, (f x - f (e.symm (relabel σ (e x))))) := by
  classical
  let : Nonempty (Slice α q) := ⟨e (Classical.arbitrary X)⟩
  have hmean : (∑ s : Slice α q, f (e.symm s)) = ∑ x : X, f x :=
    Equiv.sum_comp e.symm f
  have hcard : Fintype.card (Slice α q) = Fintype.card X := Fintype.card_congr e.symm
  have h := variance_le_card_sq_swap_energy (fun s => f (e.symm s))
  rw [hmean, hcard] at h
  have hleft : (∑ s : Slice α q,
      (f (e.symm s) - (∑ y, f y) / (Fintype.card X : ℝ)) ^ 2) =
      ∑ x : X, (f x - (∑ y, f y) / (Fintype.card X : ℝ)) ^ 2 :=
    Equiv.sum_comp e.symm (fun x => (f x - (∑ y, f y) / (Fintype.card X : ℝ)) ^ 2)
  have hright : (∑ s : Slice α q, f (e.symm s) *
      (∑ σ ∈ swaps, (f (e.symm s) - f (e.symm (relabel σ s))))) =
      ∑ x : X, f x * (∑ σ ∈ swaps, (f x - f (e.symm (relabel σ (e x))))) := by
    apply Fintype.sum_equiv e.symm
    intro s
    simp
  rwa [hleft, hright] at h

end Problem315.SlicePathComparison

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairFiberSliceComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairFiber

open SlicePermutationAction
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem assignmentRelabel_swap_val (G : SimpleGraph V) (i j : V)
    (x y : singletonSet G i j) (T : Assignment G i j) :
    (assignmentRelabel G i j (Equiv.swap x y) T).val =
      T.val.map (Equiv.swap x.val y.val).toEmbedding := by
  classical
  change ((T.val.subtype (fun z => z ∈ singletonSet G i j)).map
    (Equiv.swap x y).toEmbedding).map
      (Function.Embedding.subtype (fun z => z ∈ singletonSet G i j)) = _
  rw [Finset.map_map]
  have he : (Equiv.swap x y).toEmbedding.trans
      (Function.Embedding.subtype (fun z => z ∈ singletonSet G i j)) =
      (Function.Embedding.subtype (fun z => z ∈ singletonSet G i j)).trans
        (Equiv.swap x.val y.val).toEmbedding := by
    ext z
    exact Function.Injective.map_swap Subtype.val_injective x y z
  rw [he, ← Finset.map_map, Finset.subtype_map_of_mem T.property.1]

theorem assignment_variance_le_swap_energy (G : SimpleGraph V) (i j : V)
    (f : Assignment G i j → ℝ) :
    (∑ T, (f T - (∑ U, f U) / (Fintype.card (Assignment G i j) : ℝ)) ^ 2) ≤
      ((singletonSet G i j).card : ℝ) ^ 2 *
        ∑ T, f T * (∑ σ ∈ SlicePathComparison.swaps,
          (f T - f (assignmentRelabel G i j σ T))) := by
  classical
  let : Nonempty (Assignment G i j) :=
    ⟨⟨leftSet G i j, leftSet_subset_singletonSet G i j, rfl⟩⟩
  simpa only [Fintype.card_coe, assignmentRelabel] using
    SlicePathComparison.variance_le_card_sq_transport (assignmentSliceEquiv G i j) f

theorem assignment_displacement_eq_twice_energy (G : SimpleGraph V) (i j : V)
    (σ : Equiv.Perm (singletonSet G i j)) (f : Assignment G i j → ℝ) :
    (∑ T, (f T - f (assignmentRelabel G i j σ T)) ^ 2) =
      2 * (∑ T, f T * (f T - f (assignmentRelabel G i j σ T))) := by
  have hnorm : (∑ T, (f (assignmentRelabel G i j σ T)) ^ 2) = ∑ T, (f T)^2 :=
    Equiv.sum_comp (assignmentRelabelEquiv G i j σ) (fun T => (f T)^2)
  simp only [sub_sq, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum, ← sq]
  rw [hnorm]
  ring

theorem assignment_variance_le_swap_squared_differences (G : SimpleGraph V) (i j : V)
    (f : Assignment G i j → ℝ) :
    (∑ T, (f T - (∑ U, f U) / (Fintype.card (Assignment G i j) : ℝ)) ^ 2) ≤
      ((singletonSet G i j).card : ℝ) ^ 2 / 2 *
        ∑ T, ∑ σ ∈ SlicePathComparison.swaps,
          (f T - f (assignmentRelabel G i j σ T)) ^ 2 := by
  have h := assignment_variance_le_swap_energy G i j f
  have hs : (∑ T, ∑ σ ∈ SlicePathComparison.swaps,
      (f T - f (assignmentRelabel G i j σ T)) ^ 2) =
      2 * ∑ T, f T * (∑ σ ∈ SlicePathComparison.swaps,
        (f T - f (assignmentRelabel G i j σ T))) := by
    rw [Finset.sum_comm]
    simp_rw [assignment_displacement_eq_twice_energy]
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro T _
    exact (Finset.mul_sum _ _ _).symm
  rw [hs]
  nlinarith [h]

end Problem315.PairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SwitchPairFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315.SwitchPairFiber

attribute [local instance] Classical.propDecidable

lemma matching_endpoints_mem {n : ℕ} {S : FourSet n}
    (M : PerfectMatching S) {u v : Fin n} (h : M.val.Adj u v) :
    u ∈ S.val ∧ v ∈ S.val := by
  constructor
  · by_contra hu
    exact (M.property u).2 hu v h
  · by_contra hv
    exact (M.property v).2 hv u h.symm

theorem exists_cross_cut {n : ℕ} {G : SimpleGraph (Fin n)}
    (p : SwitchProposal n) (hp : validSwitch G p) :
    ∃ A : Finset (Fin n), A.card = 2 ∧ A ⊆ p.1.val ∧
      ∀ a b, ((removedMatching p).Adj a b ∨ (addedMatching p).Adj a b) →
        (a ∈ A ↔ b ∉ A) := by
  classical
  let S := p.1
  let M := p.2.val.1
  let N := p.2.val.2
  have hS : S.val.card = 4 := S.property
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < S.val.card by omega)
  obtain ⟨v, huv, hvuniq⟩ := (M.property u).1 hu
  obtain ⟨w, huw, hwuniq⟩ := (N.property u).1 hu
  have hv := (matching_endpoints_mem M huv).2
  have hw := (matching_endpoints_mem N huw).2
  have huvne : u ≠ v := M.val.ne_of_adj huv
  have huwne : u ≠ w := N.val.ne_of_adj huw
  have hvwne : v ≠ w := by
    intro heq
    subst w
    exact validSwitch_matchings_disjoint hp huv huw
  let T : Finset (Fin n) := {u, v, w}
  have hT : T.card = 3 := by simp [T, huvne, huwne, hvwne]
  have hnot : ¬ S.val ⊆ T := by
    intro h
    have := Finset.card_le_card h
    omega
  obtain ⟨x, hx⟩ := Finset.sdiff_nonempty.mpr hnot
  have hxS : x ∈ S.val := (Finset.mem_sdiff.mp hx).1
  have hxT : x ∉ T := (Finset.mem_sdiff.mp hx).2
  have hxune : x ≠ u := by intro h; apply hxT; simp [T, h]
  have hxvne : x ≠ v := by intro h; apply hxT; simp [T, h]
  have hxwne : x ≠ w := by intro h; apply hxT; simp [T, h]
  have hfull : S.val = {u, v, w, x} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> assumption
    · simp [hS, huvne, huwne, hvwne, hxune.symm, hxvne.symm, hxwne.symm]
  have hMxw : M.val.Adj x w := by
    obtain ⟨y, hxy, hyuniq⟩ := (M.property x).1 hxS
    have hy := (matching_endpoints_mem M hxy).2
    rw [hfull] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hy | hy | hy | hy <;> subst y
    · exact False.elim (hxvne (hvuniq x hxy.symm))
    · obtain ⟨z, hz, hzuniq⟩ := (M.property v).1 hv
      have hxu : x = u := (hzuniq x hxy.symm).trans (hzuniq u huv.symm).symm
      exact False.elim (hxune hxu)
    · exact hxy
    · exact False.elim (M.val.loopless.irrefl x hxy)
  have hNxv : N.val.Adj x v := by
    obtain ⟨y, hxy, hyuniq⟩ := (N.property x).1 hxS
    have hy := (matching_endpoints_mem N hxy).2
    rw [hfull] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hy | hy | hy | hy <;> subst y
    · exact False.elim (hxwne (hwuniq x hxy.symm))
    · exact hxy
    · obtain ⟨z, hz, hzuniq⟩ := (N.property w).1 hw
      have hxu : x = u := (hzuniq x hxy.symm).trans (hzuniq u huw.symm).symm
      exact False.elim (hxune hxu)
    · exact False.elim (N.val.loopless.irrefl x hxy)
  refine ⟨{u, x}, by simp [hxune.symm], ?_, ?_⟩
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> assumption
  · intro a b hab
    have hmem : a ∈ S.val := by
      rcases hab with hab | hab
      · exact (matching_endpoints_mem M hab).1
      · exact (matching_endpoints_mem N hab).1
    rw [hfull] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with ha | ha | ha | ha <;> subst a
    all_goals rcases hab with hab | hab
    all_goals simp only [Finset.mem_insert, Finset.mem_singleton]
    · have hb := hvuniq b hab
      subst b
      simp [huvne, hxvne, hxune, Ne.symm]
    · have hb := hwuniq b hab
      subst b
      simp [huwne, hxwne, hxune, Ne.symm]
    · have hb : b = u := by
        obtain ⟨z, hz, hzuniq⟩ := (M.property v).1 hv
        exact (hzuniq b hab).trans (hzuniq u huv.symm).symm
      subst b
      simp [huvne, hxvne, hxune, Ne.symm]
    · have hb : b = x := by
        obtain ⟨z, hz, hzuniq⟩ := (N.property v).1 hv
        exact (hzuniq b hab).trans (hzuniq x hNxv.symm).symm
      subst b
      simp [huvne, hxvne, hxune, Ne.symm]
    · have hb : b = x := by
        obtain ⟨z, hz, hzuniq⟩ := (M.property w).1 hw
        exact (hzuniq b hab).trans (hzuniq x hMxw.symm).symm
      subst b
      simp [huwne, hxwne, hxune, Ne.symm]
    · have hb : b = u := by
        obtain ⟨z, hz, hzuniq⟩ := (N.property w).1 hw
        exact (hzuniq b hab).trans (hzuniq u huw.symm).symm
      subst b
      simp [huwne, hxwne, hxune, Ne.symm]
    · have hb : b = w := by
        obtain ⟨z, hz, hzuniq⟩ := (M.property x).1 hxS
        exact (hzuniq b hab).trans (hzuniq w hMxw).symm
      subst b
      simp [huwne, hxwne, hxune, Ne.symm]
    · have hb : b = v := by
        obtain ⟨z, hz, hzuniq⟩ := (N.property x).1 hxS
        exact (hzuniq b hab).trans (hzuniq v hNxv).symm
      subst b
      simp [huvne, hxvne, hxune, Ne.symm]

end Problem315.SwitchPairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SwitchMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315.SwitchPairFiber

attribute [local instance] Classical.propDecidable

lemma complement_card {n : ℕ} (p : SwitchProposal n) {A : Finset (Fin n)}
    (hAS : A ⊆ p.1.val) (hA : A.card = 2) : (p.1.val \ A).card = 2 := by
  rw [Finset.card_sdiff_of_subset hAS, p.1.property, hA]

lemma crosses_complement {n : ℕ} (p : SwitchProposal n) {A : Finset (Fin n)}
    (hcross : Crosses p A) : Crosses p (p.1.val \ A) := by
  intro u v huv
  have hmem : u ∈ p.1.val ∧ v ∈ p.1.val := by
    rcases huv with h | h
    · exact matching_endpoints_mem p.2.val.1 h
    · exact matching_endpoints_mem p.2.val.2 h
  have h := hcross u v huv
  simp only [Finset.mem_sdiff, hmem.1, hmem.2, true_and]
  tauto

theorem cross_cuts_eq_of_inter_nonempty {n : ℕ} {G : SimpleGraph (Fin n)}
    (p : SwitchProposal n) (hp : validSwitch G p) {A B : Finset (Fin n)}
    (hA : A.card = 2) (hB : B.card = 2) (hAS : A ⊆ p.1.val) (hBS : B ⊆ p.1.val)
    (hcA : Crosses p A) (hcB : Crosses p B) (hi : (A ∩ B).Nonempty) : A = B := by
  classical
  obtain ⟨u, hu⟩ := hi
  obtain ⟨huA, huB⟩ := Finset.mem_inter.mp hu
  have huS := hAS huA
  obtain ⟨v, huv, hvuniq⟩ := (p.2.val.1.property u).1 huS
  obtain ⟨w, huw, hwuniq⟩ := (p.2.val.2.property u).1 huS
  have hvS := (matching_endpoints_mem p.2.val.1 huv).2
  have hwS := (matching_endpoints_mem p.2.val.2 huw).2
  have hvw : v ≠ w := by
    intro h
    subst w
    exact validSwitch_matchings_disjoint hp huv huw
  have hvA : v ∉ A := (hcA u v (Or.inl huv)).mp huA
  have hwA : w ∉ A := (hcA u w (Or.inr huw)).mp huA
  have hvB : v ∉ B := (hcB u v (Or.inl huv)).mp huB
  have hwB : w ∉ B := (hcB u w (Or.inr huw)).mp huB
  have heqA : p.1.val \ A = {v, w} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hz | hz <;> subst z
      · exact Finset.mem_sdiff.mpr ⟨hvS, hvA⟩
      · exact Finset.mem_sdiff.mpr ⟨hwS, hwA⟩
    · simp [complement_card p hAS hA, hvw]
  have heqB : p.1.val \ B = {v, w} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hz | hz <;> subst z
      · exact Finset.mem_sdiff.mpr ⟨hvS, hvB⟩
      · exact Finset.mem_sdiff.mpr ⟨hwS, hwB⟩
    · simp [complement_card p hBS hB, hvw]
  have heq : p.1.val \ A = p.1.val \ B := heqA.trans heqB.symm
  ext z
  have hz := Finset.ext_iff.mp heq z
  simp only [Finset.mem_sdiff] at hz
  constructor
  · intro hzA
    have hzS := hAS hzA
    tauto
  · intro hzB
    have hzS := hBS hzB
    tauto

theorem cross_cuts_eq_or_complement {n : ℕ} {G : SimpleGraph (Fin n)}
    (p : SwitchProposal n) (hp : validSwitch G p) {A B : Finset (Fin n)}
    (hA : A.card = 2) (hB : B.card = 2) (hAS : A ⊆ p.1.val) (hBS : B ⊆ p.1.val)
    (hcA : Crosses p A) (hcB : Crosses p B) :
    B = A ∨ B = p.1.val \ A := by
  classical
  by_cases hi : (A ∩ B).Nonempty
  · exact Or.inl (cross_cuts_eq_of_inter_nonempty p hp hA hB hAS hBS hcA hcB hi).symm
  · right
    apply Finset.eq_of_subset_of_card_le
    · intro z hzB
      apply Finset.mem_sdiff.mpr
      refine ⟨hBS hzB, ?_⟩
      intro hzA
      exact hi ⟨z, Finset.mem_inter.mpr ⟨hzA, hzB⟩⟩
    · rw [complement_card p hAS hA, hB]

theorem crossingPairs_card {n : ℕ} {G : SimpleGraph (Fin n)}
    (p : SwitchProposal n) (hp : validSwitch G p) :
    (crossingPairs p).card = 2 := by
  classical
  obtain ⟨A, hA, hAS, hcA⟩ := exists_cross_cut p hp
  have hAc : (p.1.val \ A).card = 2 := complement_card p hAS hA
  have hcAc : Crosses p (p.1.val \ A) := crosses_complement p hcA
  have hne : A ≠ p.1.val \ A := by
    intro heq
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
    have hu' : u ∈ p.1.val \ A := heq ▸ hu
    exact (Finset.mem_sdiff.mp hu').2 hu
  have heq : crossingPairs p = {A, p.1.val \ A} := by
    ext B
    simp only [crossingPairs, Finset.mem_filter, Finset.mem_powersetCard,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hBS, hB⟩, hcB⟩
      exact cross_cuts_eq_or_complement p hp hA hB hAS hBS hcA hcB
    · intro h
      rcases h with h | h <;> subst B
      · exact ⟨⟨hAS, hA⟩, hcA⟩
      · exact ⟨⟨Finset.sdiff_subset, hAc⟩, hcAc⟩
  rw [heq]
  simp [hne]

end Problem315.SwitchPairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairTradeSwitch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315.PairFiber

theorem fourVertexState_key {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i u v j : Fin n) (h : FourDistinct i u v j)
    (hiu : G.val.Adj i u) (hvj : G.val.Adj v j)
    (hiv : ¬ G.val.Adj i v) (huj : ¬ G.val.Adj u j) :
    key i j (fourVertexState G i u v j h).val = key i j G.val := by
  classical
  have hl (w : Fin n) : (fourVertexState G i u v j h).val.Adj i w ↔
      (G.val.Adj i w ∧ w ≠ u) ∨ w = v :=
    proposalResult_fourVertex_adj_first G.val i u v j h hiu hvj hiv huj w
  have hr (w : Fin n) : (fourVertexState G i u v j h).val.Adj j w ↔
      (G.val.Adj j w ∧ w ≠ v) ∨ w = u := by
    simpa [fourVertexState, h.2.2.1.symm, h.2.2.2.2.1.symm, h.2.2.2.2.2.symm] using
      proposalResult_fourVertex_adj G.val i u v j h hiu hvj hiv huj j w
  apply key_eq_of
  · intro x y hx hy
    change (proposalResult G.val (fourVertexProposal i u v j h)).Adj x y ↔ _
    rw [proposalResult_fourVertex_adj G.val i u v j h hiu hvj hiv huj]
    simp [hx.1, hx.2, hy.1, hy.2]
  · rw [hl]
    simp [h.2.2.2.2.1.symm, h.2.2.2.2.2.symm]
  · intro w
    have hju : ¬ G.val.Adj j u := fun hadj => huj hadj.symm
    have hjv : G.val.Adj j v := hvj.symm
    by_cases hwu : w = u
    · subst w
      simp [edgeBit, hl, hr, hiu, hju, h.2.2.2.1]
    by_cases hwv : w = v
    · subst w
      simp [edgeBit, hl, hr, hiv, hjv, h.2.2.2.1.symm]
    simp [edgeBit, hl, hr, hwu, hwv]

theorem fourVertexState_leftSet {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i u v j : Fin n) (h : FourDistinct i u v j)
    (hiu : G.val.Adj i u) (hvj : G.val.Adj v j)
    (hiv : ¬ G.val.Adj i v) (huj : ¬ G.val.Adj u j) :
    leftSet (fourVertexState G i u v j h).val i j =
      insert v ((leftSet G.val i j).erase u) := by
  classical
  have hl (w : Fin n) : (fourVertexState G i u v j h).val.Adj i w ↔
      (G.val.Adj i w ∧ w ≠ u) ∨ w = v :=
    proposalResult_fourVertex_adj_first G.val i u v j h hiu hvj hiv huj w
  have hr (w : Fin n) : (fourVertexState G i u v j h).val.Adj j w ↔
      (G.val.Adj j w ∧ w ≠ v) ∨ w = u := by
    simpa [fourVertexState, h.2.2.1.symm, h.2.2.2.2.1.symm, h.2.2.2.2.2.symm] using
      proposalResult_fourVertex_adj G.val i u v j h hiu hvj hiv huj j w
  ext w
  simp only [mem_leftSet, Finset.mem_insert, Finset.mem_erase, hl, hr]
  by_cases hwu : w = u
  · subst w
    simp [h.2.2.2.1]
  by_cases hwv : w = v
  · subst w
    simp [Outside, h.2.1.symm, h.2.2.2.2.2, h.2.2.2.1.symm]
  simp [hwu, hwv, and_comm]

theorem map_swap_eq_exchange {V : Type*} [DecidableEq V]
    (A : Finset V) (u v : V) (hu : u ∈ A) (hv : v ∉ A) :
    A.map (Equiv.swap u v).toEmbedding = insert v (A.erase u) := by
  classical
  have huv : u ≠ v := fun heq => hv (heq ▸ hu)
  ext w
  simp only [Finset.mem_map_equiv, Equiv.symm_swap,
    Finset.mem_insert, Finset.mem_erase]
  by_cases hwu : w = u
  · subst w
    simp [huv, hv]
  by_cases hwv : w = v
  · subst w
    simp [hu]
  simp [Equiv.swap_apply_of_ne_of_ne hwu hwv, hwu, hwv]

theorem map_swap_eq_self_of_mem_iff {V : Type*} [DecidableEq V]
    (A : Finset V) (u v : V) (hmem : u ∈ A ↔ v ∈ A) :
    A.map (Equiv.swap u v).toEmbedding = A := by
  classical
  ext w
  simp only [Finset.mem_map_equiv, Equiv.symm_swap]
  by_cases hwu : w = u
  · subst w
    simpa using hmem.symm
  by_cases hwv : w = v
  · subst w
    simpa using hmem
  rw [Equiv.swap_apply_of_ne_of_ne hwu hwv]

theorem fourVertexProposal_mem_crossingPairs {n : ℕ}
    (i u v j : Fin n) (h : FourDistinct i u v j) :
    ({i, j} : Finset (Fin n)) ∈
      SwitchPairFiber.crossingPairs (fourVertexProposal i u v j h) := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
  · have hs : (fourVertexProposal i u v j h).1.val = {i, u, v, j} := by
      rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
      rfl
    rw [hs]
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
    tauto
  · simp [h.2.2.1]
  · intro x y hxy
    simp only [removedMatching_fourVertexProposal, addedMatching_fourVertexProposal] at hxy
    rcases hxy with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      simp [h.1.symm, h.2.1.symm, h.2.2.1,
        h.2.2.2.2.1, h.2.2.2.2.2]

theorem exists_crossingProposal_of_key_leftSet_exchange {n : ℕ} {d : Fin n → ℕ}
    (G H : GraphState n d) (i j u v : Fin n) (hij : i ≠ j)
    (hu : u ∈ leftSet G.val i j) (hv : v ∈ singletonSet G.val i j)
    (hvn : v ∉ leftSet G.val i j)
    (hkey : key i j H.val = key i j G.val)
    (hleft : leftSet H.val i j = insert v ((leftSet G.val i j).erase u)) :
    ∃ p : SwitchProposal n, validSwitch G.val p ∧
      ({i, j} : Finset (Fin n)) ∈ SwitchPairFiber.crossingPairs p ∧
      proposalResult G.val p = H.val := by
  classical
  obtain ⟨huo, hiu, hju⟩ := (mem_leftSet G.val i j u).mp hu
  obtain ⟨hvo, hvxor⟩ := (mem_singletonSet G.val i j v).mp hv
  have hvright : G.val.Adj j v ∧ ¬ G.val.Adj i v := by
    rcases hvxor with hvleft | hvright
    · exact False.elim (hvn ((mem_leftSet G.val i j v).mpr ⟨hvo, hvleft⟩))
    · exact hvright
  have huv : u ≠ v := fun heq => hvn (heq ▸ hu)
  have hdist : FourDistinct i u v j :=
    ⟨huo.1.symm, hvo.1.symm, hij, huv, huo.2, hvo.2⟩
  have huj : ¬ G.val.Adj u j := fun he => hju he.symm
  refine ⟨fourVertexProposal i u v j hdist,
    (validSwitch_fourVertexProposal_iff G.val i u v j hdist).mpr
      ⟨hiu, hvright.1.symm, hvright.2, huj⟩,
    fourVertexProposal_mem_crossingPairs i u v j hdist, ?_⟩
  change (fourVertexState G i u v j hdist).val = H.val
  apply graph_eq_of_key_leftSet_eq
  · exact (fourVertexState_key G i u v j hdist hiu hvright.1.symm hvright.2 huj).trans hkey.symm
  · exact (fourVertexState_leftSet G i u v j hdist hiu hvright.1.symm hvright.2 huj).trans hleft.symm

end Problem315.PairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairSwapInjectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem315.PairFiber

variable {V : Type*} [DecidableEq V]

theorem exchange_endpoints_unique (T : Finset V) {u v u' v' : V}
    (hu : u ∈ T) (hv : v ∉ T) (_hu' : u' ∈ T) (_hv' : v' ∉ T)
    (h : insert v (T.erase u) = insert v' (T.erase u')) :
    u = u' ∧ v = v' := by
  have hvv : v = v' := by
    have hmem : v ∈ insert v' (T.erase u') := h ▸ Finset.mem_insert_self v _
    rcases Finset.mem_insert.mp hmem with heq | hmem
    · exact heq
    · exact False.elim (hv (Finset.mem_of_mem_erase hmem))
  have huu : u = u' := by
    by_contra hne
    have huv : u ≠ v := fun heq => hv (heq ▸ hu)
    have hnot : u ∉ insert v (T.erase u) := by simp [huv]
    apply hnot
    rw [h]
    exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, hu⟩)
  exact ⟨huu, hvv⟩

theorem swap_eq_of_map_eq (T : Finset V) {u v u' v' : V}
    (hu : u ∈ T) (hv : v ∉ T) (hu' : u' ∈ T) (hv' : v' ∉ T)
    (h : T.map (Equiv.swap u v).toEmbedding =
      T.map (Equiv.swap u' v').toEmbedding) :
    Equiv.swap u v = Equiv.swap u' v' := by
  rw [map_swap_eq_exchange T u v hu hv, map_swap_eq_exchange T u' v' hu' hv'] at h
  obtain ⟨rfl, rfl⟩ := exchange_endpoints_unique T hu hv hu' hv' h
  rfl

theorem exists_oriented_swap_of_map_ne (T : Finset V) {σ : Equiv.Perm V}
    (hσ : σ.IsSwap) (hne : T.map σ.toEmbedding ≠ T) :
    ∃ u v, u ∈ T ∧ v ∉ T ∧ σ = Equiv.swap u v := by
  obtain ⟨u, v, _, rfl⟩ := hσ
  by_cases hu : u ∈ T
  · by_cases hv : v ∈ T
    · exact False.elim (hne (map_swap_eq_self_of_mem_iff T u v (by simp [hu, hv])))
    · exact ⟨u, v, hu, hv, rfl⟩
  · by_cases hv : v ∈ T
    · exact ⟨v, u, hv, hu, Equiv.swap_comm u v⟩
    · exact False.elim (hne (map_swap_eq_self_of_mem_iff T u v (by simp [hu, hv])))

theorem map_swap_injective_on_nontrivial (T : Finset V) {σ τ : Equiv.Perm V}
    (hσ : σ.IsSwap) (hτ : τ.IsSwap)
    (hneσ : T.map σ.toEmbedding ≠ T) (hneτ : T.map τ.toEmbedding ≠ T)
    (h : T.map σ.toEmbedding = T.map τ.toEmbedding) : σ = τ := by
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_oriented_swap_of_map_ne T hσ hneσ
  obtain ⟨u', v', hu', hv', rfl⟩ := exists_oriented_swap_of_map_ne T hτ hneτ
  exact swap_eq_of_map_eq T hu hv hu' hv' h

end Problem315.PairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairAssignmentMoves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem315.PairFiber
open SlicePermutationAction

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem assignmentRelabel_injective_on_nontrivial (G : SimpleGraph V) (i j : V)
    (T : Assignment G i j) {σ τ : Equiv.Perm (singletonSet G i j)}
    (hσ : σ.IsSwap) (hτ : τ.IsSwap)
    (hneσ : assignmentRelabel G i j σ T ≠ T)
    (hneτ : assignmentRelabel G i j τ T ≠ T)
    (h : assignmentRelabel G i j σ T = assignmentRelabel G i j τ T) : σ = τ := by
  let e := assignmentSliceEquiv G i j
  apply map_swap_injective_on_nontrivial (e T).val hσ hτ
  · intro hh
    apply hneσ
    apply e.injective
    change e (e.symm (relabel σ (e T))) = e T
    rw [e.apply_symm_apply]
    exact Subtype.ext hh
  · intro hh
    apply hneτ
    apply e.injective
    change e (e.symm (relabel τ (e T))) = e T
    rw [e.apply_symm_apply]
    exact Subtype.ext hh
  · have hh := congrArg (fun U => (e U).val) h
    simpa only [assignmentRelabel, Equiv.apply_symm_apply, e, relabel] using hh

theorem exists_crossingProposal_of_key_leftSet_swap {n : ℕ} {d : Fin n → ℕ}
    (G H : GraphState n d) (i j u v : Fin n) (hij : i ≠ j)
    (hu : u ∈ singletonSet G.val i j) (hv : v ∈ singletonSet G.val i j)
    (hkey : key i j H.val = key i j G.val)
    (hleft : leftSet H.val i j =
      (leftSet G.val i j).map (Equiv.swap u v).toEmbedding)
    (hne : H ≠ G) :
    ∃ p : SwitchProposal n, validSwitch G.val p ∧
      ({i, j} : Finset (Fin n)) ∈ SwitchPairFiber.crossingPairs p ∧
      proposalResult G.val p = H.val := by
  classical
  have hnot (hm : u ∈ leftSet G.val i j ↔ v ∈ leftSet G.val i j) : False := by
    apply hne
    apply Subtype.ext
    apply graph_eq_of_key_leftSet_eq hkey
    rw [hleft, map_swap_eq_self_of_mem_iff _ u v hm]
  by_cases hul : u ∈ leftSet G.val i j
  · by_cases hvl : v ∈ leftSet G.val i j
    · exact False.elim (hnot (by simp [hul, hvl]))
    · exact exists_crossingProposal_of_key_leftSet_exchange G H i j u v hij
        hul hv hvl hkey (hleft.trans (map_swap_eq_exchange _ u v hul hvl))
  · by_cases hvl : v ∈ leftSet G.val i j
    · apply exists_crossingProposal_of_key_leftSet_exchange G H i j v u hij
        hvl hu hul hkey
      rw [hleft, Equiv.swap_comm u v]
      exact map_swap_eq_exchange _ v u hvl hul
    · exact False.elim (hnot (by simp [hul, hvl]))

theorem assignmentRelabel_exists_crossingProposal {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (T : Assignment G.val i j) (σ : Equiv.Perm (singletonSet G.val i j))
    (hσ : σ.IsSwap) (hne : assignmentRelabel G.val i j σ T ≠ T) :
    let H := ((stateFiberEquiv G i j hij).symm T).val
    let K := ((stateFiberEquiv G i j hij).symm
      (assignmentRelabel G.val i j σ T)).val
    ∃ p : SwitchProposal n, validSwitch H.val p ∧
      ({i, j} : Finset (Fin n)) ∈ SwitchPairFiber.crossingPairs p ∧
      proposalResult H.val p = K.val := by
  classical
  obtain ⟨x, y, _, rfl⟩ := hσ
  let H := ((stateFiberEquiv G i j hij).symm T).val
  let K := ((stateFiberEquiv G i j hij).symm
    (assignmentRelabel G.val i j (Equiv.swap x y) T)).val
  have hkH : key i j H.val = key i j G.val :=
    ((stateFiberEquiv G i j hij).symm T).property
  have hkK : key i j K.val = key i j G.val :=
    ((stateFiberEquiv G i j hij).symm _).property
  have hlH : leftSet H.val i j = T.val := leftSet_trade G.val i j hij T.val T.property.1
  have hlK : leftSet K.val i j =
      T.val.map (Equiv.swap x.val y.val).toEmbedding := by
    exact (leftSet_trade G.val i j hij
      (assignmentRelabel G.val i j (Equiv.swap x y) T).val
      (assignmentRelabel G.val i j (Equiv.swap x y) T).property.1).trans
        (assignmentRelabel_swap_val G.val i j x y T)
  apply exists_crossingProposal_of_key_leftSet_swap H K i j x.val y.val hij
  · rw [singletonSet_eq_of_key_eq hkH]
    exact x.property
  · rw [singletonSet_eq_of_key_eq hkH]
    exact y.property
  · exact hkK.trans hkH.symm
  · rw [hlK, hlH]
  · intro heq
    apply hne
    apply Subtype.ext
    have hh := congrArg (fun F : GraphState n d => leftSet F.val i j) heq
    rw [hlH] at hh
    exact (leftSet_trade G.val i j hij
      (assignmentRelabel G.val i j (Equiv.swap x y) T).val
      (assignmentRelabel G.val i j (Equiv.swap x y) T).property.1).symm.trans hh

end Problem315.PairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairFiberEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
attribute [local instance] Classical.propDecidable

namespace Problem315.PairResampling

variable {n : Nat} {d : Fin n → Nat}

theorem sum_expectation (a : Finset (Fin n)) (f : StateSpace n d) :
    (∑ G, expectation n d a f G) = ∑ G, f G := by
  let one : StateSpace n d := WithLp.toLp 2 (fun _ => 1)
  have hone : expectation n d a one = one :=
    (expectation_eq_self_iff a one).mpr (constant_mem a 1)
  have h := expectation_isSymmetric a f one
  change inner ℝ (expectation n d a f) one = inner ℝ f (expectation n d a one) at h
  rw [hone, state_inner, state_inner] at h
  simpa [one] using h

theorem sum_fiber_average (a : Finset (Fin n)) (g : GraphState n d → ℝ) :
    (∑ G, (∑ H ∈ fiberStates a G, g H) / (fiberStates a G).card) = ∑ G, g G := by
  let f : StateSpace n d := WithLp.toLp 2 g
  have h := sum_expectation a f
  simpa only [expectation_eq_average, f] using h

theorem inner_fluctuation_eq_sum_fiber_variance (a : Finset (Fin n))
    (f : StateSpace n d) :
    inner ℝ f (fluctuation n d a f) =
      ∑ G, (∑ H ∈ fiberStates a G,
        (f H - expectation n d a f G) ^ 2) / (fiberStates a G).card := by
  have heq : ∀ G H, H ∈ fiberStates a G →
      expectation n d a f H = expectation n d a f G := by
    intro G H hH
    exact (expectation_mem a f) H G ((mem_fiberStates a G H).mp hH).symm
  calc
    inner ℝ f (fluctuation n d a f) =
        inner ℝ (fluctuation n d a f) (fluctuation n d a f) := by
      rw [inner_fluctuation, real_inner_self_eq_norm_sq]
    _ = ∑ G, (f G - expectation n d a f G) ^ 2 := by
      rw [state_inner, fluctuation_eq_sub]
      apply Finset.sum_congr rfl
      intro G hG
      change (f G - expectation n d a f G) * (f G - expectation n d a f G) = _
      ring
    _ = ∑ G, (∑ H ∈ fiberStates a G,
        (f H - expectation n d a f H) ^ 2) / (fiberStates a G).card :=
      (sum_fiber_average a (fun H => (f H - expectation n d a f H) ^ 2)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro G hG
      congr 1
      apply Finset.sum_congr rfl
      intro H hH
      rw [heq G H hH]

theorem inner_fluctuation_le_of_fiber_variance_bound
    (a : Finset (Fin n)) (f : StateSpace n d) (e : GraphState n d → ℝ) (C : ℝ)
    (hlocal : ∀ G : GraphState n d,
      (∑ H ∈ fiberStates a G, (f H - expectation n d a f G) ^ 2) /
          (fiberStates a G).card ≤
        C * ((∑ H ∈ fiberStates a G, e H) / (fiberStates a G).card)) :
    inner ℝ f (fluctuation n d a f) ≤ C * ∑ G, e G := by
  rw [inner_fluctuation_eq_sum_fiber_variance]
  calc
    _ ≤ ∑ G, C * ((∑ H ∈ fiberStates a G, e H) / (fiberStates a G).card) :=
      Finset.sum_le_sum (fun G _ => hlocal G)
    _ = _ := by rw [← Finset.mul_sum, sum_fiber_average]

end Problem315.PairResampling

namespace Problem315.PairFiber

variable {n : Nat} {d : Fin n → Nat}

theorem assignment_average_eq_fiber_average
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) (g : GraphState n d → ℝ) :
    (∑ T : Assignment G.val i j, g ((stateFiberEquiv G i j hij).symm T).val) /
        (Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card : ℝ) =
      (∑ H ∈ PairResampling.fiberStates {i, j} G, g H) /
        (PairResampling.fiberStates {i, j} G).card := by
  let f : PairResampling.StateSpace n d := WithLp.toLp 2 g
  have h := expectation_eq_assignment_average G i j hij f
  rw [PairResampling.expectation_eq_average] at h
  exact h.symm

theorem inner_fluctuation_le_of_assignment_variance_bound
    (i j : Fin n) (hij : i ≠ j) (f : PairResampling.StateSpace n d)
    (e : GraphState n d → ℝ) (C : ℝ)
    (hlocal : ∀ G : GraphState n d,
      (∑ T : Assignment G.val i j,
        (f ((stateFiberEquiv G i j hij).symm T).val -
          PairResampling.expectation n d {i, j} f G) ^ 2) /
          (Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card : ℝ) ≤
        C * ((∑ T : Assignment G.val i j, e ((stateFiberEquiv G i j hij).symm T).val) /
          (Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card : ℝ))) :
    inner ℝ f (PairResampling.fluctuation n d {i, j} f) ≤ C * ∑ G, e G := by
  apply PairResampling.inner_fluctuation_le_of_fiber_variance_bound {i, j} f e C
  intro G
  rw [← assignment_average_eq_fiber_average G i j hij
      (fun H => (f H - PairResampling.expectation n d {i, j} f G) ^ 2),
    ← assignment_average_eq_fiber_average G i j hij e]
  exact hlocal G

theorem inner_fluctuation_le_of_assignment_sum_bound
    (i j : Fin n) (hij : i ≠ j) (f : PairResampling.StateSpace n d)
    (e : GraphState n d → ℝ) (C : ℝ)
    (hlocal : ∀ G : GraphState n d,
      (∑ T : Assignment G.val i j,
        (f ((stateFiberEquiv G i j hij).symm T).val -
          PairResampling.expectation n d {i, j} f G) ^ 2) ≤
        C * (∑ T : Assignment G.val i j, e ((stateFiberEquiv G i j hij).symm T).val)) :
    inner ℝ f (PairResampling.fluctuation n d {i, j} f) ≤ C * ∑ G, e G := by
  apply inner_fluctuation_le_of_assignment_variance_bound i j hij f e C
  intro G
  simpa only [mul_div_assoc] using
    div_le_div_of_nonneg_right (hlocal G)
      (show (0 : ℝ) ≤ Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card by
        positivity)

end Problem315.PairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.ProposalUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
namespace Problem315

theorem IsPerfectMatchingOn.mem_iff_exists_adj {n : Nat} {S : Finset (Fin n)}
    {M : SimpleGraph (Fin n)} (hm : IsPerfectMatchingOn S M) (v : Fin n) :
    v ∈ S ↔ ∃ w, M.Adj v w := by
  constructor
  · intro hv
    obtain ⟨w, hw, _⟩ := (hm v).1 hv
    exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    by_contra hv
    exact (hm v).2 hv w hw

theorem IsPerfectMatchingOn.support_unique {n : Nat} {S T : Finset (Fin n)}
    {M : SimpleGraph (Fin n)} (hS : IsPerfectMatchingOn S M)
    (hT : IsPerfectMatchingOn T M) : S = T := by
  ext v
  rw [hS.mem_iff_exists_adj v, hT.mem_iff_exists_adj v]

theorem SwitchProposal.ext_matchings {n : Nat} {p q : SwitchProposal n}
    (hM : removedMatching p = removedMatching q)
    (hN : addedMatching p = addedMatching q) : p = q := by
  rcases p with ⟨⟨S, hS⟩, ⟨⟨⟨M, hm⟩, ⟨N, hn⟩⟩, hmn⟩⟩
  rcases q with ⟨⟨T, hT⟩, ⟨⟨⟨M', hm'⟩, ⟨N', hn'⟩⟩, hmn'⟩⟩
  change M = M' at hM
  change N = N' at hN
  subst M'
  subst N'
  have hST : S = T := hm.support_unique hm'
  subst T
  rfl

theorem removedMatching_adj_iff {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (hp : validSwitch G p) (u v : Fin n) :
    (removedMatching p).Adj u v ↔
      G.Adj u v ∧ ¬ (proposalResult G p).Adj u v := by
  classical
  rw [proposalResult, ite_eq_left hp]
  change (removedMatching p).Adj u v ↔ G.Adj u v ∧
    ¬ ((G.Adj u v ∧ ¬ (removedMatching p).Adj u v) ∨ (addedMatching p).Adj u v)
  constructor
  · intro hm
    refine ⟨hp.1 hm, ?_⟩
    rintro (⟨_, hnm⟩ | hn)
    · exact hnm hm
    · exact hp.2 hn (hp.1 hm)
  · rintro ⟨hg, hh⟩
    by_contra hnm
    exact hh (Or.inl ⟨hg, hnm⟩)

theorem addedMatching_adj_iff {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (hp : validSwitch G p) (u v : Fin n) :
    (addedMatching p).Adj u v ↔
      (proposalResult G p).Adj u v ∧ ¬ G.Adj u v := by
  classical
  rw [proposalResult, ite_eq_left hp]
  change (addedMatching p).Adj u v ↔
    ((G.Adj u v ∧ ¬ (removedMatching p).Adj u v) ∨ (addedMatching p).Adj u v) ∧
      ¬ G.Adj u v
  constructor
  · intro hn
    exact ⟨Or.inr hn, hp.2 hn⟩
  · rintro ⟨⟨hg, _⟩ | hn, hng⟩
    · exact False.elim (hng hg)
    · exact hn

theorem proposalResult_injective_on_valid {n : Nat} {G : SimpleGraph (Fin n)}
    {p q : SwitchProposal n} (hp : validSwitch G p) (hq : validSwitch G q)
    (heq : proposalResult G p = proposalResult G q) : p = q := by
  apply SwitchProposal.ext_matchings
  · ext u v
    rw [removedMatching_adj_iff hp, removedMatching_adj_iff hq, heq]
  · ext u v
    rw [addedMatching_adj_iff hp, addedMatching_adj_iff hq, heq]

theorem validSwitch_of_proposalResult_ne {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (h : proposalResult G p ≠ G) : validSwitch G p := by
  classical
  by_contra hn
  exact h (by simp [proposalResult, hn])

theorem proposal_count_eq_one {n : Nat} {G H : SimpleGraph (Fin n)}
    (hGH : G ≠ H) (hex : ∃ p : SwitchProposal n, proposalResult G p = H) :
    ((allProposals n).filter (fun p => proposalResult G p = H)).card = 1 := by
  classical
  obtain ⟨p, hp⟩ := hex
  apply Finset.card_eq_one.mpr
  refine ⟨p, ?_⟩
  ext q
  simp only [allProposals, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hq
    apply proposalResult_injective_on_valid
    · apply validSwitch_of_proposalResult_ne
      rw [hq]
      exact Ne.symm hGH
    · apply validSwitch_of_proposalResult_ne
      rw [hp]
      exact Ne.symm hGH
    · exact hq.trans hp.symm
  · rintro rfl
    exact hp

theorem proposal_count_eq_zero {n : Nat} {G H : SimpleGraph (Fin n)}
    (hex : ¬ ∃ p : SwitchProposal n, proposalResult G p = H) :
    ((allProposals n).filter (fun p => proposalResult G p = H)).card = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact hex ⟨p, (Finset.mem_filter.mp hp).2⟩

theorem switchKernel_of_ne {n : Nat} {d : Fin n → Nat}
    {G H : GraphState n d} (hGH : G ≠ H) :
    switchKernel n d G H =
      if SwitchStep n d G H then 1 / (12 * (Nat.choose n 4 : ℝ)) else 0 := by
  classical
  have hv : G.val ≠ H.val := fun h => hGH (Subtype.ext h)
  have hiff : SwitchStep n d G H ↔
      ∃ p : SwitchProposal n, proposalResult G.val p = H.val := by
    constructor
    · rintro ⟨p, _, hp⟩
      exact ⟨p, hp⟩
    · rintro ⟨p, hp⟩
      refine ⟨p, ?_, hp⟩
      apply validSwitch_of_proposalResult_ne
      rw [hp]
      exact Ne.symm hv
  by_cases hs : SwitchStep n d G H
  · rw [switchKernel, ite_eq_right hGH, ite_eq_left hs,
      proposal_count_eq_one hv (hiff.mp hs)]
    simp
  · rw [switchKernel, ite_eq_right hGH, ite_eq_right hs,
      proposal_count_eq_zero (fun h => hs (hiff.mpr h))]
    simp

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SwitchLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace Problem315

theorem switchKernel_mul_sub_eq {n : Nat} {d : Fin n → Nat}
    (f : GraphState n d → ℝ) (G H : GraphState n d) :
    switchKernel n d G H * (f G - f H) =
      (if SwitchStep n d G H then f G - f H else 0) /
        (12 * (Nat.choose n 4 : ℝ)) := by
  by_cases h : G = H
  · subst H
    simp
  · rw [switchKernel_of_ne h]
    split_ifs <;> ring

theorem sub_markovApply_eq_switchLaplacian {n : Nat} {d : Fin n → Nat}
    (hrow : ∀ G : GraphState n d,
      ∑ H ∈ allGraphStates n d, switchKernel n d G H = 1)
    (f : GraphState n d → ℝ) (G : GraphState n d) :
    f G - markovApply n d f G =
      switchLaplacian n d f G / (12 * (Nat.choose n 4 : ℝ)) := by
  calc
    f G - markovApply n d f G =
        (∑ H ∈ allGraphStates n d, switchKernel n d G H) * f G -
          ∑ H ∈ allGraphStates n d, switchKernel n d G H * f H := by
            rw [hrow G, one_mul]
            rfl
    _ = ∑ H ∈ allGraphStates n d, switchKernel n d G H * (f G - f H) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro H hH
      ring
    _ = switchLaplacian n d f G / (12 * (Nat.choose n 4 : ℝ)) := by
      simp only [switchKernel_mul_sub_eq, switchLaplacian, Finset.sum_div]

theorem dirichletEnergy_eq_switchLaplacian {n : Nat} {d : Fin n → Nat}
    (hrow : ∀ G : GraphState n d,
      ∑ H ∈ allGraphStates n d, switchKernel n d G H = 1)
    (f : GraphState n d → ℝ) :
    dirichletEnergy n d f =
      uniformInner n d f (switchLaplacian n d f) /
        (12 * (Nat.choose n 4 : ℝ)) := by
  unfold dirichletEnergy uniformInner uniformAverage
  simp only [sub_markovApply_eq_switchLaplacian hrow, ← mul_div_assoc]
  rw [← Finset.sum_div]
  ring

theorem hasSpectralGapAtLeast_of_switchLaplacian {n : Nat} {d : Fin n → Nat}
    (hn : 4 ≤ n)
    (hrow : ∀ G : GraphState n d,
      ∑ H ∈ allGraphStates n d, switchKernel n d G H = 1)
    (hpoincare : ∀ f : GraphState n d → ℝ,
      uniformVariance n d f ≤
        2 * (n : ℝ)^2 * uniformInner n d f (switchLaplacian n d f)) :
    hasSpectralGapAtLeast n d
      ((1 : ℝ) / (24 * (n : ℝ)^2 * (Nat.choose n 4 : ℝ))) := by
  intro f
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hc : (0 : ℝ) < Nat.choose n 4 := by exact_mod_cast Nat.choose_pos hn
  have hd : (0 : ℝ) < 12 * (Nat.choose n 4 : ℝ) := by positivity
  have hden : (0 : ℝ) < 24 * (n : ℝ)^2 * (Nat.choose n 4 : ℝ) := by positivity
  rw [dirichletEnergy_eq_switchLaplacian hrow]
  rw [div_mul_eq_mul_div, one_mul]
  apply (div_le_div_iff₀ hden hd).mpr
  have h := mul_le_mul_of_nonneg_right (hpoincare f) (le_of_lt hd)
  nlinarith only [h]

theorem switch_chain_gap_of_laplacian_poincare {n : Nat} {d : Fin n → Nat}
    (hn : 4 ≤ n)
    (hpoincare : ∀ f : GraphState n d → ℝ,
      uniformVariance n d f ≤
        2 * (n : ℝ)^2 * uniformInner n d f (switchLaplacian n d f)) :
    hasSpectralGapAtLeast n d
      ((1 : ℝ) / (24 * (n : ℝ)^2 * (Nat.choose n 4 : ℝ))) :=
  hasSpectralGapAtLeast_of_switchLaplacian hn (switchKernel_row_sum hn) hpoincare

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.ProposalLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace Problem315

theorem switchLaplacian_eq_sum_proposals {n : Nat} {d : Fin n → Nat}
    (f : GraphState n d → ℝ) (G : GraphState n d) :
    switchLaplacian n d f G =
      ∑ p ∈ allProposals n, (f G - f (proposalState G p)) := by
  have hterm (H : GraphState n d) :
      (if SwitchStep n d G H then f G - f H else 0) =
        (((allProposals n).filter (fun p => proposalResult G.val p = H.val)).card : ℝ) *
          (f G - f H) := by
    by_cases hGH : G = H
    · subst H
      simp
    · have hv : G.val ≠ H.val := fun h => hGH (Subtype.ext h)
      by_cases hs : SwitchStep n d G H
      · obtain ⟨p, hvalid, hp⟩ := hs
        rw [ite_eq_left ⟨p, hvalid, hp⟩, proposal_count_eq_one hv ⟨p, hp⟩]
        simp
      · rw [ite_eq_right hs, proposal_count_eq_zero]
        · simp
        · rintro ⟨p, hp⟩
          apply hs
          refine ⟨p, ?_, hp⟩
          apply validSwitch_of_proposalResult_ne
          rw [hp]
          exact Ne.symm hv
  unfold switchLaplacian
  simp_rw [hterm]
  calc
    _ = ∑ H ∈ allGraphStates n d, ∑ p ∈ allProposals n,
        if proposalState G p = H then f G - f H else 0 := by
      apply Finset.sum_congr rfl
      intro H hH
      rw [← Finset.sum_filter]
      have hfilter : (allProposals n).filter (fun p => proposalState G p = H) =
          (allProposals n).filter (fun p => proposalResult G.val p = H.val) := by
        ext p
        simp only [Finset.mem_filter, and_congr_right_iff]
        intro _
        exact Subtype.ext_iff
      rw [hfilter]
      simp
      ring
    _ = ∑ p ∈ allProposals n, (f G - f (proposalState G p)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      simp [allGraphStates]

theorem sum_pairProposalLaplacian_eq_of_valid {n : Nat} {d : Fin n → Nat}
    {ι : Type*} (pairs : Finset ι) (crosses : ι → SwitchProposal n → Prop)
    [∀ a p, Decidable (crosses a p)]
    (f : GraphState n d → ℝ) (G : GraphState n d)
    (hcount : ∀ p : SwitchProposal n, validSwitch G.val p →
      (pairs.filter (fun a => crosses a p)).card = 2) :
    (∑ a ∈ pairs, ∑ p ∈ allProposals n,
      if crosses a p then f G - f (proposalState G p) else 0) =
      2 * switchLaplacian n d f G := by
  rw [Finset.sum_comm, switchLaplacian_eq_sum_proposals, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hv : validSwitch G.val p
  · rw [← Finset.sum_filter]
    simp [hcount p hv]
    ring
  · have heq : proposalState G p = G := by
      apply Subtype.ext
      simp [proposalState, proposalResult, hv]
    simp [heq]

theorem sum_pairSwitchLaplacian {n : Nat} {d : Fin n → Nat}
    (f : GraphState n d → ℝ) (G : GraphState n d) :
    (∑ a ∈ (Finset.univ : Finset (Fin n)).powersetCard 2,
      pairSwitchLaplacian n d a f G) = 2 * switchLaplacian n d f G := by
  unfold pairSwitchLaplacian
  refine sum_pairProposalLaplacian_eq_of_valid
    ((Finset.univ : Finset (Fin n)).powersetCard 2)
    (fun a p => a ∈ SwitchPairFiber.crossingPairs p) f G ?_
  intro p hp
  have heq : ((Finset.univ : Finset (Fin n)).powersetCard 2).filter
      (fun a => a ∈ SwitchPairFiber.crossingPairs p) = SwitchPairFiber.crossingPairs p := by
    ext a
    constructor
    · intro ha
      exact (Finset.mem_filter.mp ha).2
    · intro ha
      refine Finset.mem_filter.mpr ⟨?_, ha⟩
      apply Finset.mem_powersetCard.mpr
      refine ⟨Finset.subset_univ a, ?_⟩
      exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp ha).1).2
  rw [heq]
  exact SwitchPairFiber.crossingPairs_card p hp

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairSquaredEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315.PairSquaredEnergy
attribute [local instance] Classical.propDecidable

lemma reverseMove_fst {n : ℕ} {d : Fin n → ℕ}
    (x : GraphState n d × SwitchProposal n) :
    (reverseMove x).1 = proposalState x.1 x.2 := by
  by_cases h : validSwitch x.1.val x.2
  · simp [reverseMove, h]
  · simp only [reverseMove, ite_eq_right h]
    apply Subtype.ext
    simp [proposalState, proposalResult, h]

lemma crossingPairs_reverse {n : ℕ} (p : SwitchProposal n) :
    SwitchPairFiber.crossingPairs (reverseProposal p) = SwitchPairFiber.crossingPairs p := by
  ext a
  simp only [SwitchPairFiber.crossingPairs, Finset.mem_filter]
  change (a ∈ p.1.val.powersetCard 2 ∧ SwitchPairFiber.Crosses (reverseProposal p) a) ↔ _
  unfold SwitchPairFiber.Crosses
  simp only [removedMatching_reverse, addedMatching_reverse, or_comm]

lemma reverseMove_crossing {n : ℕ} {d : Fin n → ℕ}
    (x : GraphState n d × SwitchProposal n) (a : Finset (Fin n)) :
    a ∈ SwitchPairFiber.crossingPairs (reverseMove x).2 ↔
      a ∈ SwitchPairFiber.crossingPairs x.2 := by
  by_cases h : validSwitch x.1.val x.2
  · simp [reverseMove, h, crossingPairs_reverse]
  · simp [reverseMove, h]

theorem involution_energy {X : Type*} [Fintype X] (e : Equiv.Perm X)
    (he : Function.Involutive e) (w f : X → ℝ) (hw : ∀ x, w (e x) = w x) :
    (∑ x, w x * f x * (f x - f (e x))) =
      (1 / 2 : ℝ) * ∑ x, w x * (f x - f (e x)) ^ 2 := by
  have hr : (∑ x, w x * f (e x) * (f (e x) - f x)) =
      ∑ x, w x * f x * (f x - f (e x)) := by
    have h := Equiv.sum_comp e (fun x => w x * f x * (f x - f (e x)))
    have he' (x : X) : e (e x) = x := he x
    simpa only [hw, he'] using h
  have hsum : (∑ x, w x * (f x - f (e x)) ^ 2) =
      (∑ x, w x * f x * (f x - f (e x))) +
      (∑ x, w x * f (e x) * (f (e x) - f x)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum, hr]
  ring

theorem pairSwitchLaplacian_energy {n : ℕ} {d : Fin n → ℕ}
    (a : Finset (Fin n)) (f : GraphState n d → ℝ) :
    (∑ G, f G * pairSwitchLaplacian n d a f G) =
      (1 / 2 : ℝ) * ∑ G, ∑ p ∈ allProposals n,
        if a ∈ SwitchPairFiber.crossingPairs p then
          (f G - f (proposalState G p)) ^ 2 else 0 := by
  let w : GraphState n d × SwitchProposal n → ℝ :=
    fun x => if a ∈ SwitchPairFiber.crossingPairs x.2 then 1 else 0
  have hw (x : GraphState n d × SwitchProposal n) :
      w (reverseMoveEquiv x) = w x := by
    change (if a ∈ SwitchPairFiber.crossingPairs (reverseMove x).2 then (1:ℝ) else 0) = _
    simp only [reverseMove_crossing, w]
  have h := involution_energy (@reverseMoveEquiv n d) reverseMove_involutive
    w (fun x => f x.1) hw
  change (∑ x, w x * f x.1 * (f x.1 - f (reverseMove x).1)) =
    (1 / 2 : ℝ) * ∑ x, w x * (f x.1 - f (reverseMove x).1) ^ 2 at h
  simp only [reverseMove_fst, Fintype.sum_prod_type] at h
  simpa only [w, pairSwitchLaplacian, allProposals, Finset.mul_sum,
    ite_mul, one_mul, zero_mul, mul_ite, mul_zero] using h

end Problem315.PairSquaredEnergy

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairLocalComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
attribute [local instance] Classical.propDecidable

namespace Problem315.PairFiber

variable {n : ℕ} {d : Fin n → ℕ}

theorem assignment_swap_squared_differences_le_proposals
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (T : Assignment G.val i j) (f : GraphState n d → ℝ) :
    (∑ σ ∈ SlicePathComparison.swaps,
      (f ((stateFiberEquiv G i j hij).symm T).val -
        f ((stateFiberEquiv G i j hij).symm
          (assignmentRelabel G.val i j σ T)).val) ^ 2) ≤
    ∑ p ∈ allProposals n,
      if ({i, j} : Finset (Fin n)) ∈ SwitchPairFiber.crossingPairs p then
        (f ((stateFiberEquiv G i j hij).symm T).val -
          f (proposalState ((stateFiberEquiv G i j hij).symm T).val p)) ^ 2
      else 0 := by
  classical
  let R : Assignment G.val i j → GraphState n d :=
    fun U => ((stateFiberEquiv G i j hij).symm U).val
  have hR : Function.Injective R := by
    intro U W h
    apply (stateFiberEquiv G i j hij).symm.injective
    exact Subtype.ext h
  let s : Finset (Equiv.Perm (singletonSet G.val i j)) :=
    SlicePathComparison.swaps.filter (fun σ => assignmentRelabel G.val i j σ T ≠ T)
  have hs (σ : s) : σ.val.IsSwap ∧ assignmentRelabel G.val i j σ.val T ≠ T := by
    exact ⟨SlicePathComparison.mem_swaps σ.val |>.mp (Finset.mem_filter.mp σ.property).1,
      (Finset.mem_filter.mp σ.property).2⟩
  have hex (σ : s) : ∃ p : SwitchProposal n, validSwitch (R T).val p ∧
      ({i, j} : Finset (Fin n)) ∈ SwitchPairFiber.crossingPairs p ∧
      proposalResult (R T).val p = (R (assignmentRelabel G.val i j σ.val T)).val :=
    assignmentRelabel_exists_crossingProposal G i j hij T σ.val (hs σ).1 (hs σ).2
  let p : s → SwitchProposal n := fun σ => Classical.choose (hex σ)
  have hp (σ : s) := Classical.choose_spec (hex σ)
  have hstate (σ : s) : proposalState (R T) (p σ) =
      R (assignmentRelabel G.val i j σ.val T) := by
    apply Subtype.ext
    exact (hp σ).2.2
  have hinj : Function.Injective p := by
    intro σ τ heq
    apply Subtype.ext
    apply assignmentRelabel_injective_on_nontrivial G.val i j T
      (hs σ).1 (hs τ).1 (hs σ).2 (hs τ).2
    apply hR
    rw [← hstate σ, ← hstate τ, heq]
  let D : Equiv.Perm (singletonSet G.val i j) → ℝ :=
    fun σ => (f (R T) - f (R (assignmentRelabel G.val i j σ T))) ^ 2
  let E : SwitchProposal n → ℝ := fun q =>
    if ({i, j} : Finset (Fin n)) ∈ SwitchPairFiber.crossingPairs q then
      (f (R T) - f (proposalState (R T) q)) ^ 2 else 0
  have hweight (σ : s) : E (p σ) = D σ.val := by
    dsimp only [E, D]
    rw [ite_eq_left (hp σ).2.1, hstate σ]
  have hrestrict : (∑ σ ∈ SlicePathComparison.swaps, D σ) = ∑ σ : s, D σ.val := by
    rw [Finset.sum_coe_sort]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro σ hσ hnot
    have hfix : assignmentRelabel G.val i j σ T = T := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨hσ, hne⟩)
    simp [D, hfix]
  change (∑ σ ∈ SlicePathComparison.swaps, D σ) ≤ ∑ q ∈ allProposals n, E q
  rw [hrestrict]
  calc
    (∑ σ : s, D σ.val) = ∑ σ : s, E (p σ) := by
      apply Finset.sum_congr rfl
      intro σ _
      exact (hweight σ).symm
    _ = ∑ q ∈ Finset.univ.image p, E q :=
      (Finset.sum_image (fun _ _ _ _ h => hinj h)).symm
    _ ≤ ∑ q ∈ allProposals n, E q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        exact Finset.mem_univ q
      · intro q _ _
        dsimp only [E]
        split_ifs <;> positivity

theorem inner_fluctuation_le_pairSwitchLaplacian
    (i j : Fin n) (hij : i ≠ j) (f : PairResampling.StateSpace n d) :
    inner ℝ f (PairResampling.fluctuation n d {i, j} f) ≤
      (n : ℝ) ^ 2 * ∑ G : GraphState n d,
        f G * pairSwitchLaplacian n d {i, j} (fun H => f H) G := by
  classical
  let E : GraphState n d → ℝ := fun H =>
    ∑ p ∈ allProposals n,
      if ({i, j} : Finset (Fin n)) ∈ SwitchPairFiber.crossingPairs p then
        (f H - f (proposalState H p)) ^ 2 else 0
  have hE (H : GraphState n d) : 0 ≤ E H := by
    apply Finset.sum_nonneg
    intro p _
    split_ifs <;> positivity
  have hlocal (G : GraphState n d) :
      (∑ T : Assignment G.val i j,
        (f ((stateFiberEquiv G i j hij).symm T).val -
          PairResampling.expectation n d {i, j} f G) ^ 2) ≤
        (n : ℝ) ^ 2 / 2 *
          ∑ T : Assignment G.val i j, E ((stateFiberEquiv G i j hij).symm T).val := by
    let R : Assignment G.val i j → GraphState n d :=
      fun T => ((stateFiberEquiv G i j hij).symm T).val
    have hcard : Fintype.card (Assignment G.val i j) =
        Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card := by
      rw [← Nat.card_eq_fintype_card]
      exact assignment_natCard G.val i j
    have hmean := expectation_eq_assignment_average G i j hij f
    rw [← hcard] at hmean
    have hvar := assignment_variance_le_swap_squared_differences G.val i j
      (fun T => f (R T))
    change (∑ T : Assignment G.val i j,
      (f (R T) - (∑ U, f (R U)) / (Fintype.card (Assignment G.val i j) : ℝ)) ^ 2) ≤ _ at hvar
    rw [← hmean] at hvar
    have hsum : (∑ T : Assignment G.val i j, ∑ σ ∈ SlicePathComparison.swaps,
        (f (R T) - f (R (assignmentRelabel G.val i j σ T))) ^ 2) ≤
          ∑ T : Assignment G.val i j, E (R T) := by
      apply Finset.sum_le_sum
      intro T _
      exact assignment_swap_squared_differences_le_proposals G i j hij T (fun H => f H)
    have hN : ((singletonSet G.val i j).card : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (show (singletonSet G.val i j).card ≤ n from
        (Finset.card_le_univ _).trans_eq (Fintype.card_fin n))
    have hN2 : ((singletonSet G.val i j).card : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hN 2
    calc
      _ ≤ ((singletonSet G.val i j).card : ℝ) ^ 2 / 2 *
          ∑ T : Assignment G.val i j, ∑ σ ∈ SlicePathComparison.swaps,
            (f (R T) - f (R (assignmentRelabel G.val i j σ T))) ^ 2 := hvar
      _ ≤ ((singletonSet G.val i j).card : ℝ) ^ 2 / 2 *
          ∑ T : Assignment G.val i j, E (R T) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ (n : ℝ) ^ 2 / 2 * ∑ T : Assignment G.val i j, E (R T) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hN2 (by norm_num))
          (Finset.sum_nonneg (fun T _ => hE (R T)))
  have h := inner_fluctuation_le_of_assignment_sum_bound i j hij f E
    ((n : ℝ) ^ 2 / 2) hlocal
  calc
    _ ≤ (n : ℝ) ^ 2 / 2 * ∑ G : GraphState n d, E G := h
    _ = _ := by
      rw [PairSquaredEnergy.pairSwitchLaplacian_energy]
      dsimp only [E]
      ring

end Problem315.PairFiber

namespace Problem315.PairResampling

theorem fluctuation_energy_le_pairSwitchLaplacian {n : ℕ} {d : Fin n → ℕ}
    (f : StateSpace n d) (a : Finset (Fin n)) (ha : a ∈ pairs n) :
    inner ℝ f (fluctuation n d a f) ≤ (n : ℝ) ^ 2 *
      ∑ G : GraphState n d, f G * pairSwitchLaplacian n d a (fun H => f H) G := by
  classical
  have hcard : a.card = 2 := (Finset.mem_powersetCard.mp ha).2
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hcard
  exact PairFiber.inner_fluctuation_le_pairSwitchLaplacian i j hij f

end Problem315.PairResampling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairSwitchComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling

theorem generator_energy_le_switchLaplacian {n : Nat} {d : Fin n → Nat}
    (f : StateSpace n d)
    (hlocal : ∀ a ∈ pairs n,
      ⟪f, fluctuation n d a f⟫ ≤ (n : ℝ)^2 *
        ∑ G : GraphState n d, f G * pairSwitchLaplacian n d a (fun H => f H) G) :
    ⟪f, generator n d f⟫ ≤
      2 * (n : ℝ)^2 *
        ∑ G : GraphState n d, f G * switchLaplacian n d (fun H => f H) G := by
  calc
    ⟪f, generator n d f⟫ = ∑ a ∈ pairs n, ⟪f, fluctuation n d a f⟫ := by
      rw [generator_apply, inner_sum]
    _ ≤ ∑ a ∈ pairs n, (n : ℝ)^2 *
        ∑ G : GraphState n d, f G * pairSwitchLaplacian n d a (fun H => f H) G :=
      Finset.sum_le_sum hlocal
    _ = 2 * (n : ℝ)^2 *
        ∑ G : GraphState n d, f G * switchLaplacian n d (fun H => f H) G := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      simp only [pairs, sum_pairSwitchLaplacian]
      have hsum : (∑ G : GraphState n d,
          f G * (2 * switchLaplacian n d (fun H => f H) G)) =
          2 * ∑ G : GraphState n d, f G * switchLaplacian n d (fun H => f H) G := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro G hG
        ring
      rw [hsum]
      ring

theorem spectralGap_of_square_and_local_comparison {n : Nat} {d : Fin n → Nat}
    (hn : 4 ≤ n) (hgraph : Graphical n d)
    (hsquare : ∀ f : StateSpace n d,
      ⟪f, generator n d f⟫ ≤ ⟪generator n d f, generator n d f⟫)
    (hlocal : ∀ (f : StateSpace n d) a, a ∈ pairs n →
      ⟪f, fluctuation n d a f⟫ ≤ (n : ℝ)^2 *
        ∑ G : GraphState n d, f G * pairSwitchLaplacian n d a (fun H => f H) G) :
    hasSpectralGapAtLeast n d
      ((1 : ℝ) / (24 * (n : ℝ)^2 * (Nat.choose n 4 : ℝ))) := by
  apply switch_chain_gap_of_laplacian_poincare hn
  intro f
  have hcomparison := generator_energy_le_switchLaplacian
    (WithLp.toLp 2 f) (hlocal (WithLp.toLp 2 f))
  calc
    uniformVariance n d f ≤
        ⟪WithLp.toLp 2 f, generator n d (WithLp.toLp 2 f)⟫ /
          (stateCount n d : ℝ) := uniformVariance_le_generator hgraph hsquare f
    _ ≤ (2 * (n : ℝ)^2 *
        ∑ G : GraphState n d, f G * switchLaplacian n d f G) /
          (stateCount n d : ℝ) :=
      div_le_div_of_nonneg_right hcomparison (Nat.cast_nonneg _)
    _ = 2 * (n : ℝ)^2 * uniformInner n d f (switchLaplacian n d f) := by
      unfold uniformInner uniformAverage allGraphStates
      ring

end Problem315.PairResampling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.LocalGapEndgame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling

attribute [local instance] Classical.propDecidable

theorem spectralGap_of_triples_disjoint_and_local_comparison
    {n : Nat} {d : Fin n → Nat} (hn : 4 ≤ n) (hgraph : Graphical n d)
    (htriple : ∀ (f : StateSpace n d) (T : Finset (Fin n)), T.card = 3 →
      ⟪f, tripleGenerator n d T f⟫ ≤
        ⟪tripleGenerator n d T f, tripleGenerator n d T f⟫)
    (hdisjoint : ∀ f : StateSpace n d,
      0 ≤ ∑ a ∈ pairs n, ∑ b ∈ pairs n,
        if Disjoint a b then ⟪fluctuation n d a f, fluctuation n d b f⟫ else 0)
    (hlocal : ∀ (f : StateSpace n d) a, a ∈ pairs n →
      ⟪f, fluctuation n d a f⟫ ≤ (n : ℝ) ^ 2 *
        ∑ G : GraphState n d, f G * pairSwitchLaplacian n d a (fun H => f H) G) :
    hasSpectralGapAtLeast n d
      ((1 : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))) := by
  apply spectralGap_of_square_and_local_comparison hn hgraph _ hlocal
  intro f
  exact generator_square_of_local (by omega) f (htriple f) (hdisjoint f)

theorem spectralGap_of_triples_and_disjoint_oai
    {n : Nat} {d : Fin n → Nat} (hn : 4 ≤ n) (hgraph : Graphical n d)
    (htriple : ∀ (f : StateSpace n d) (T : Finset (Fin n)), T.card = 3 →
      ⟪f, tripleGenerator n d T f⟫ ≤
        ⟪tripleGenerator n d T f, tripleGenerator n d T f⟫)
    (hdisjoint : ∀ f : StateSpace n d,
      0 ≤ ∑ a ∈ pairs n, ∑ b ∈ pairs n,
        if Disjoint a b then ⟪fluctuation n d a f, fluctuation n d b f⟫ else 0) :
    hasSpectralGapAtLeast n d
      ((1 : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))) :=
  spectralGap_of_triples_disjoint_and_local_comparison hn hgraph htriple hdisjoint
    fluctuation_energy_le_pairSwitchLaplacian

end Problem315.PairResampling

end

end OAI
end

theorem solution : type_of% @OAI.Problem315.PairResampling.spectralGap_of_triples_and_disjoint_oai := @OAI.Problem315.PairResampling.spectralGap_of_triples_and_disjoint_oai
