-- Prove2me | solution 1 for MatroidProphetKW.Inter.eq_20_21
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:11:53.15858+00:00
-- url     : https://prove2.me/submissions/902fce43-a630-47b5-aac2-c30e8baf00c7

import Mathlib
import Definitions.Def_MatroidProphetKW_Inter_Setting
import Definitions.Def_MatroidProphetKW_Inter_Online

open MeasureTheory

namespace Aux_MPKW_eq2021

open MatroidProphetKW.Inter

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma firstOf_mem (S : Finset (Finset α)) (h : S.Nonempty) : firstOf S ∈ S := by
  unfold firstOf
  rw [dif_pos h]
  obtain ⟨T, hT, hTe⟩ := Finset.mem_image.mp
    ((S.image (Fintype.equivFin (Finset α))).min'_mem (h.image _))
  rw [← hTe, Equiv.symm_apply_apply]
  exact hT

lemma firstOf_mem_or (Q : Finset α → Prop) {inst : DecidablePred Q} :
    Q (firstOf (Finset.univ.filter Q)) ∨ firstOf (Finset.univ.filter Q) = ∅ := by
  by_cases h : (Finset.univ.filter Q).Nonempty
  · left
    exact (Finset.mem_filter.mp (firstOf_mem _ h)).2
  · right
    unfold firstOf
    rw [dif_neg h]

lemma firstOf_filter_spec (Q : Finset α → Prop) {inst : DecidablePred Q} (h : ∃ S, Q S) :
    Q (firstOf (Finset.univ.filter Q)) := by
  obtain ⟨S, hS⟩ := h
  exact (Finset.mem_filter.mp
    (firstOf_mem _ ⟨S, Finset.mem_filter.2 ⟨Finset.mem_univ _, hS⟩⟩)).2

lemma argmaxOn_or (P : Finset α → Prop) (f : Finset α → ℝ) :
    P (argmaxOn P f) ∨ argmaxOn P f = ∅ := by
  have key : ∀ (Q : Finset α → Prop) {inst : DecidablePred Q}, (∀ S, Q S → P S) →
      P (firstOf (Finset.univ.filter Q)) ∨ firstOf (Finset.univ.filter Q) = ∅ :=
    fun Q _ hQ => (firstOf_mem_or Q).imp (hQ _) id
  unfold argmaxOn
  exact key _ (fun S h => h.1)

lemma argmaxOn_spec (P : Finset α → Prop) (f : Finset α → ℝ) (S0 : Finset α) (h0 : P S0) :
    P (argmaxOn P f) ∧ ∀ T, P T → f T ≤ f (argmaxOn P f) := by
  have hex : ∃ S, P S ∧ ∀ T, P T → f T ≤ f S := by
    classical
    obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image (Finset.univ.filter P) f
      ⟨S0, Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩⟩
    exact ⟨S, (Finset.mem_filter.mp hS).2,
      fun T hT => hmax T (Finset.mem_filter.2 ⟨Finset.mem_univ _, hT⟩)⟩
  unfold argmaxOn
  exact firstOf_filter_spec (fun S => P S ∧ ∀ T, P T → f T ≤ f S) hex

lemma Rj_sub {p : ℕ} (M : Fin p → Matroid α) (j : Fin p) (A : Finset α) (w' : α → ℝ) :
    Rj M j A w' ⊆ B M w' := by
  unfold Rj
  rcases argmaxOn_or (fun R => R ⊆ B M w' \ A ∧ (M j).Indep (↑(A ∪ R) : Set α) ∧
      (↑(B M w') : Set α) ⊆ (M j).closure (↑(A ∪ R) : Set α))
      (MatroidProphetKW.Single.wt w') with h | h
  · exact h.1.trans Finset.sdiff_subset
  · rw [h]; exact Finset.empty_subset _

lemma OPT_eq {p : ℕ} (M : Fin p → Matroid α) (w' : α → ℝ) :
    OPT M w' = MatroidProphetKW.Single.wt w' (B M w') := by
  have hspec := argmaxOn_spec (fun S => IsIndep M S) (MatroidProphetKW.Single.wt w') ∅
    (fun j => by simp)
  unfold OPT
  classical
  apply le_antisymm
  · apply Finset.sup'_le
    intro S hS
    exact hspec.2 S (Finset.mem_filter.mp hS).2
  · apply Finset.le_sup'
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hspec.1⟩

end Aux_MPKW_eq2021

open MatroidProphetKW.Inter in
theorem solution
    {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}
    (hp : 0 < p) (M : Fin p → Matroid α) (hE : ∀ j, (M j).E = Set.univ)
    (A : Finset α) (hA : IsIndep M A) (w' : α → ℝ) :
    (∀ j, MatroidProphetKW.Single.wt w' (Cj M j A w') + MatroidProphetKW.Single.wt w' (Rj M j A w') = OPT M w') ∧
      MatroidProphetKW.Single.wt w' (Cint M A w') + MatroidProphetKW.Single.wt w' (Rint M A w') = OPT M w' := by
  rw [Aux_MPKW_eq2021.OPT_eq]
  constructor
  · intro j
    unfold Cj MatroidProphetKW.Single.wt
    exact Finset.sum_sdiff (Aux_MPKW_eq2021.Rj_sub M j A w')
  · have hRsub : Rint M A w' ⊆ B M w' := by
      intro x hx
      unfold Rint at hx
      have := (Finset.mem_filter.mp hx).2 ⟨0, hp⟩
      exact Aux_MPKW_eq2021.Rj_sub M _ A w' this
    have hC : Cint M A w' = B M w' \ Rint M A w' := by
      ext x
      unfold Cint Rint Cj
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_sdiff,
        Finset.mem_filter]
      constructor
      · rintro ⟨j, hB, hR⟩
        exact ⟨hB, fun h => hR (h j)⟩
      · rintro ⟨hB, hR⟩
        push_neg at hR
        obtain ⟨j, hj⟩ := hR
        exact ⟨j, hB, hj⟩
    rw [hC]
    unfold MatroidProphetKW.Single.wt
    exact Finset.sum_sdiff hRsub
