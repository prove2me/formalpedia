-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.VacBd.sm_dH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:36:03.955438+00:00
-- url     : https://prove2.me/submissions/71ce0e0c-3fba-42f1-b5ca-5b0121b1e95b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergSmoothOfWeakDerivativeClosedSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FderivCompress
import Theorems.Thm_GlobalTheory_Mem_Lift_VacBd_heis_dH
import Theorems.Thm_GlobalTheory_Mem_Lift_VacBd_contDiff_omJ

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
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → B →L[ℂ] B}
set_option linter.unusedSectionVars false
namespace GlobalTheory.Mem.Lift.VacBd
theorem _root_.solution (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) (v : V) : Sm ρ (dH ρ v f) := by
  unfold Sm
  simp only [heis_dH h hf]
  exact ((contDiff_omJ v).smul hf).add
    ((ContDiff.fderiv_right (m := ∞) hf (by simp)).clm_apply contDiff_const)
end GlobalTheory.Mem.Lift.VacBd
