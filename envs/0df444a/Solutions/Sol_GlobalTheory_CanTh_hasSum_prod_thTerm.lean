-- Prove2me | solution 1 for GlobalTheory.CanTh.hasSum_prod_thTerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:54:05.079844+00:00
-- url     : https://prove2.me/submissions/e0154312-76c9-4aee-9c8e-77237dbad92e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SetIntegralPowEqZeroOfPosFreqEuclidean
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemThetaDomainIffIsSiegelAddTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsMulDotProductLeOfIsCompactThetaDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnThetaProdOfNormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasSumPolyDerivMulProdAddMatrix
import Theorems.Thm_GlobalTheory_CanTh_summable_norm_thTerm
import Theorems.Thm_GlobalTheory_CanTh_hasSum_thTerm
import Theorems.Thm_GlobalTheory_hasSum_multilinear_tuples
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
noncomputable section
open Complex Matrix Filter Topology ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real
open GlobalTheory GlobalTheory.CanTh
variable {g : ℕ}
namespace GlobalTheory.CanTh
theorem _root_.solution {κ : Type*} [Fintype κ] {τ : κ → Matrix (Fin g) (Fin g) ℂ}
    (hτ : ∀ k, τ k ∈ ThetaDomain (Fin g)) (a b : κ → Fin g → ℝ) (ζ : κ → Fin g → ℂ) :
    HasSum (fun m : κ → Fin g → ℤ => ∏ k, thTerm (τ k) (a k) (b k) (ζ k) (m k))
      (∏ k, thetaChar (τ k) (fun i => (a k i : ℂ)) (fun i => (b k i : ℂ)) (ζ k)) := by
  simpa using hasSum_multilinear_tuples (J := fun _ : κ => Fin g → ℤ)
    (ContinuousMultilinearMap.mkPiAlgebra ℂ κ ℂ) (x := fun k => thTerm (τ k) (a k) (b k) (ζ k))
    (fun k => summable_norm_thTerm (hτ k) _ _ _) fun k => hasSum_thTerm (hτ k) _ _ _
end GlobalTheory.CanTh
