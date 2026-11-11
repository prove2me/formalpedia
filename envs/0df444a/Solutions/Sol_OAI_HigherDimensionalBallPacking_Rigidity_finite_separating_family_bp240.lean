-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.finite_separating_family_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:08:53.627898+00:00
-- url     : https://prove2.me/submissions/686bcafd-7681-4c1d-bc96-580aec45dabf

import Mathlib

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FreeLinearization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open Set Function
variable {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem finite_separating_family_bp240_oai (L : I → E →L[ℝ] F)
    (hL : ∀ v : E, (∀ i, L i v=0) → v=0) :
    ∃ s : Finset I, ∀ v : E, (∀ i ∈ s, L i v=0) → v=0 := by
  classical
  let U : I → Set E := fun i => {v | L i v≠0}
  have hU : ∀ i, IsOpen (U i) := fun i =>
    (isClosed_singleton.preimage (L i).continuous).isOpen_compl
  have hcov : Metric.sphere (0:E) 1 ⊆ ⋃ i, U i := by
    intro v hv
    by_contra hn
    have hz : ∀ i, L i v=0 := by
      intro i
      by_contra hi
      exact hn (mem_iUnion.mpr ⟨i,hi⟩)
    have hv0 := hL v hz
    simp [hv0] at hv
  obtain ⟨s,hs⟩ := (isCompact_sphere (0:E) 1).elim_finite_subcover U hU hcov
  refine ⟨s,fun v hv => ?_⟩
  by_contra hne
  have hn : ‖v‖≠0 := norm_ne_zero_iff.mpr hne
  have hw : ‖v‖⁻¹ • v ∈ Metric.sphere (0:E) 1 := by
    rw [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),inv_mul_cancel₀ hn]
  obtain ⟨i,hi⟩ := mem_iUnion.mp (hs hw)
  obtain ⟨his,hh⟩ := mem_iUnion.mp hi
  have hzi : L i (‖v‖⁻¹ • v)=0 := by rw [map_smul,hv i his,smul_zero]
  exact hh hzi


end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.finite_separating_family_bp240_oai.{u_1, u_2, u_3} := @OAI.HigherDimensionalBallPacking.Rigidity.finite_separating_family_bp240_oai.{u_1, u_2, u_3}
