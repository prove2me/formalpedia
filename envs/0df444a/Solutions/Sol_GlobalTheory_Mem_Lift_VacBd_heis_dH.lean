-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.VacBd.heis_dH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:25:52.965126+00:00
-- url     : https://prove2.me/submissions/602d42d1-5adb-4659-9193-b01157c8e1d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergSmoothOfWeakDerivativeClosedSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FderivCompress
import Theorems.Thm_GlobalTheory_Mem_Lift_hasDerivAt_dH


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
theorem _root_.solution (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) (v w : V) :
    ρ w (dH ρ v f) = (π * I * (omJ J w v : ℂ)) • ρ w f + fderiv ℝ (fun u => ρ u f) w v := by
  have h1 := ((ρ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dH v hf)
  have h2 : HasDerivAt (fun t : ℝ => w + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w
  have h3 : HasDerivAt (fun t : ℝ => ρ (w + t • v) f) (fderiv ℝ (fun u => ρ u f) w v) 0 :=
    (ContDiff.differentiable hf (by simp) w).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h2 (by simp)
  have h4 : HasDerivAt (fun t : ℝ => cexp ((π * I * (omJ J w v : ℂ)) * (t : ℂ))) (π * I * (omJ J w v : ℂ)) 0 := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).const_mul (π * I * (omJ J w v : ℂ))).cexp
  have h5 := h4.smul h3
  have e : ((ρ w).restrictScalars ℝ) ∘ (fun t : ℝ => ρ (t • v) f) =
      (fun t : ℝ => cexp ((π * I * (omJ J w v : ℂ)) * (t : ℂ))) • fun t : ℝ => ρ (w + t • v) f := by
    funext t
    simp only [Function.comp, ContinuousLinearMap.coe_restrictScalars', h.2.1, Pi.smul_apply', omJ, map_smul,
      real_inner_smul_right]
    congr 2
    push_cast
    ring
  rw [e] at h1
  have := h1.unique h5
  simpa [add_comm] using this
end GlobalTheory.Mem.Lift.VacBd
