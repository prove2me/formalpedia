-- Prove2me | solution 1 for GlobalTheory.CanTh.hasSum_polyDeriv_mul_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:22:25.631061+00:00
-- url     : https://prove2.me/submissions/d856052c-cea2-4d17-9a38-d8c883e019d3

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
import Theorems.Thm_GlobalTheory_CanTh_hasSum_polyDeriv_of_locally_normal
import Theorems.Thm_GlobalTheory_CanTh_polyDeriv_congr_of_eventuallyEq
import Theorems.Thm_GlobalTheory_CanTh_hasSum_prod_thTerm
import Theorems.Thm_GlobalTheory_CanTh_mul_prod_thTerm_locally_normal
import Theorems.Thm_GlobalTheory_CanTh_differentiableOn_prod_fun
import Theorems.Thm_GlobalTheory_CanTh_differentiableOn_thTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix Filter Topology ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real
open GlobalTheory GlobalTheory.CanTh
variable {g : ℕ}
variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
variable [FiniteDimensional ℂ W] {κ : Type*} [Fintype κ]
namespace GlobalTheory.CanTh
theorem _root_.solution {U : Set W} (hU : IsOpen U)
    {G : W → ℂ} {T : κ → W → Matrix (Fin g) (Fin g) ℂ} {Z : κ → W → Fin g → ℂ}
    (hG : DifferentiableOn ℂ G U) (hT : ∀ k i j, DifferentiableOn ℂ (fun w => T k w i j) U)
    (hZ : ∀ k, DifferentiableOn ℂ (Z k) U) (hdom : ∀ k, ∀ w ∈ U, T k w ∈ ThetaDomain (Fin g))
    (a b : κ → Fin g → ℝ) (P : MvPolynomial σ ℂ) (u : σ → W) {x : W} (hx : x ∈ U) :
    HasSum (fun m : κ → Fin g → ℤ =>
        I2.polyDeriv P u (fun w => G w * ∏ k, thTerm (T k w) (a k) (b k) (Z k w) (m k)) x)
      (I2.polyDeriv P u (fun w => G w *
        ∏ k, thetaChar (T k w) (fun i => (a k i : ℂ)) (fun i => (b k i : ℂ)) (Z k w)) x) := by
  have : ProperSpace W := FiniteDimensional.proper ℂ W
  have h := hasSum_polyDeriv_of_locally_normal hU
    (F := fun (m : κ → Fin g → ℤ) w => G w * ∏ k, thTerm (T k w) (a k) (b k) (Z k w) (m k))
    (fun m => hG.mul (differentiableOn_prod_fun _ fun k _ =>
      differentiableOn_thTerm (hT k) (hZ k) _ _ _))
    (fun y hy => mul_prod_thTerm_locally_normal hU hG.continuousOn
      (fun k i j => (hT k i j).continuousOn) (fun k => (hZ k).continuousOn) hdom a b hy) P u hx
  rwa [polyDeriv_congr_of_eventuallyEq P u (G := fun w => G w *
    ∏ k, thetaChar (T k w) (fun i => (a k i : ℂ)) (fun i => (b k i : ℂ)) (Z k w))] at h
  filter_upwards [hU.mem_nhds hx] with w hw
  exact ((hasSum_prod_thTerm (fun k => hdom k w hw) a b fun k => Z k w).mul_left _).tsum_eq
end GlobalTheory.CanTh
