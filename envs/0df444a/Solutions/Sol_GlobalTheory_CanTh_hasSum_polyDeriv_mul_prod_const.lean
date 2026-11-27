-- Prove2me | solution 1 for GlobalTheory.CanTh.hasSum_polyDeriv_mul_prod_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:35:16.039967+00:00
-- url     : https://prove2.me/submissions/500c1e78-d926-476d-8209-b66be6a94b21

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
import Theorems.Thm_GlobalTheory_CanTh_hasSum_polyDeriv_mul_prod

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
theorem _root_.solution {G : W → ℂ} {τ : κ → Matrix (Fin g) (Fin g) ℂ}
    {Z : κ → W → Fin g → ℂ} (hG : Differentiable ℂ G) (hZ : ∀ k, Differentiable ℂ (Z k))
    (hτ : ∀ k, τ k ∈ ThetaDomain (Fin g)) (a b : κ → Fin g → ℝ) (P : MvPolynomial σ ℂ)
    (u : σ → W) (x : W) :
    HasSum (fun m : κ → Fin g → ℤ =>
        I2.polyDeriv P u (fun w => G w * ∏ k, thTerm (τ k) (a k) (b k) (Z k w) (m k)) x)
      (I2.polyDeriv P u (fun w => G w *
        ∏ k, thetaChar (τ k) (fun i => (a k i : ℂ)) (fun i => (b k i : ℂ)) (Z k w)) x) ∧
    Summable fun m : κ → Fin g → ℤ =>
      ‖I2.polyDeriv P u (fun w => G w * ∏ k, thTerm (τ k) (a k) (b k) (Z k w) (m k)) x‖ :=
  have h := hasSum_polyDeriv_mul_prod (T := fun k _ => τ k) isOpen_univ hG.differentiableOn
    (fun _ _ _ => differentiableOn_const _) (fun k => (hZ k).differentiableOn)
    (fun k _ _ => hτ k) a b P u (Set.mem_univ x)
  ⟨h, summable_norm_iff.2 h.summable⟩
end GlobalTheory.CanTh
