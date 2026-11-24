-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.VacBd.dH_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:43:38.002718+00:00
-- url     : https://prove2.me/submissions/e6a0fa82-ef0d-4c30-ab08-f9f6495126af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergSmoothOfWeakDerivativeClosedSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FderivCompress
import Theorems.Thm_GlobalTheory_Mem_Lift_VacBd_orbit_lip

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift GlobalTheory.Mem.Lift.VacBd
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
  {om : V → V → ℝ} {ρ : V → B →L[ℂ] B}
namespace GlobalTheory.Mem.Lift.VacBd
theorem _root_.solution [CompleteSpace B] (h : IsHeis om ρ) (T : B →L[ℂ] B) (hT : ∀ x, Sm ρ (T x)) :
    ∃ C : ℝ, ∀ z x, ‖dH ρ z (T x)‖ ≤ C * ‖z‖ * ‖x‖ := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun z : V => ((‖z‖ : ℂ)⁻¹) • ((ρ z).comp T - T)) (fun x => by
    obtain ⟨C, hC⟩ := orbit_lip h (hT x)
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : z = 0
    · simp [hz]
    · have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        norm_smul, norm_inv, Complex.norm_real, norm_norm]
      rw [inv_mul_le_iff₀ hz', mul_comm]
      exact (hC z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hz'.le))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C, fun z x => ?_⟩
  have h1 : ‖fderiv ℝ (fun u => ρ u (T x)) 0‖ ≤ C * ‖x‖ := by
    refine (ContDiff.differentiable (hT x) (by simp) 0).hasFDerivAt.le_of_lip' (by positivity)
      (Filter.Eventually.of_forall fun w => ?_)
    by_cases hz : w = 0
    · simp [hz]
    · have hz' : 0 < ‖w‖ := norm_pos_iff.2 hz
      have := ContinuousLinearMap.le_of_opNorm_le _ (hC w) x
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        norm_smul, norm_inv, Complex.norm_real, norm_norm] at this
      rw [inv_mul_le_iff₀ hz', mul_comm] at this
      simpa only [h.1, sub_zero] using this
  have := ContinuousLinearMap.le_of_opNorm_le _ h1 z
  unfold dH
  linarith [mul_right_comm C ‖x‖ ‖z‖]
end GlobalTheory.Mem.Lift.VacBd
