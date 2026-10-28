-- Prove2me | solution 1 for MatroidProphetKW.Inter.T_identity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:14:06.84047+00:00
-- url     : https://prove2.me/submissions/fa6e6a09-2a1e-41d1-9f8b-7f09eb4e2025

import Mathlib
import Definitions.Def_MatroidProphetKW_Inter_Setting
import Definitions.Def_MatroidProphetKW_Inter_Online

open MeasureTheory

namespace Aux_MPKW_Tid

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

lemma wt_C {p : ℕ} (M : Fin p → Matroid α) (j : Fin p) (A : Finset α) (w' : α → ℝ) :
    MatroidProphetKW.Single.wt w' (Cj M j A w') =
      MatroidProphetKW.Single.wt w' (B M w') - MatroidProphetKW.Single.wt w' (Rj M j A w') := by
  unfold Cj MatroidProphetKW.Single.wt
  rw [Finset.sum_sdiff_eq_sub (Rj_sub M j A w')]

end Aux_MPKW_Tid

open MatroidProphetKW.Inter in
theorem solution
    {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}
    (M : Fin p → Matroid α) (hE : ∀ j, (M j).E = Set.univ)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (a : ℝ) (j : Fin p) (A : Finset α) (x : α)
    (hAx : (M j).Indep (↑(insert x A) : Set α)) :
    Tij M F a j A x =
      (1 / a) * ∫ w', (MatroidProphetKW.Single.wt w' (Cj M j (insert x A) w') - MatroidProphetKW.Single.wt w' (Cj M j A w')) ∂(law F) := by
  unfold Tij
  congr 1
  apply integral_congr_ae
  filter_upwards with w'
  rw [Aux_MPKW_Tid.wt_C, Aux_MPKW_Tid.wt_C]
  ring
