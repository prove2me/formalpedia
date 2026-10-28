-- Prove2me | solution 1 for NashVecOpt.SharedConstraint.cone_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:14:13.54599+00:00
-- url     : https://prove2.me/submissions/cf31084a-ebe3-44a4-98da-39ed7da86b7a

import Mathlib
import Definitions.Def_NashVecOpt_SharedConstraint_Model

namespace Aux_NashVecOpt_cone_decomposition
open NashVecOpt.SharedConstraint

theorem mem_coneI {ι : Type} [Fintype ι] [DecidableEq ι]
    {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    (i : ι) (z : (∀ j, E j) × (ι → ℝ)) :
    z ∈ coneI (E := E) i ↔ (∀ j, j ≠ i → z.1 j = 0) ∧ 0 ≤ z.2 i := by
  simp only [coneI, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun j hj => ?_, ?_⟩
    · have := h1 j
      rw [if_neg hj] at this
      exact this
    · have := h2 i
      rw [if_pos rfl] at this
      exact this
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun j => ?_⟩
    · by_cases hj : j = i
      · rw [if_pos hj]; exact Set.mem_univ _
      · rw [if_neg hj]; exact h1 j hj
    · by_cases hj : j = i
      · rw [if_pos hj]; subst hj; exact h2
      · rw [if_neg hj]; exact Set.mem_univ _

end Aux_NashVecOpt_cone_decomposition

open NashVecOpt.SharedConstraint Aux_NashVecOpt_cone_decomposition in
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    (hN : 2 ≤ Fintype.card ι) :
    ((orderCone : Set ((∀ j, E j) × (ι → ℝ))) = ⋃ i, coneI i) ∧
    ∀ i, Convex ℝ (coneI (E := E) i) ∧
      ∀ c : ℝ, 0 ≤ c → ∀ z ∈ coneI (E := E) i, c • z ∈ coneI (E := E) i := by
  refine ⟨?_, fun i => ⟨?_, ?_⟩⟩
  · ext z
    simp only [Set.mem_iUnion, mem_coneI]
    rfl
  · unfold coneI
    apply Convex.prod
    · apply convex_pi
      intro j _
      split_ifs
      · exact convex_univ
      · exact convex_singleton 0
    · apply convex_pi
      intro j _
      split_ifs
      · exact convex_Ici 0
      · exact convex_univ
  · intro c hc z hz
    rw [mem_coneI] at hz ⊢
    obtain ⟨h1, h2⟩ := hz
    refine ⟨fun j hj => ?_, ?_⟩
    · simp [h1 j hj]
    · simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg hc h2
