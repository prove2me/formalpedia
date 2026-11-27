-- Prove2me | solution 1 for GlobalTheory.CanTh.hasSum_polyDeriv_mul_prod_add_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:53:41.461654+00:00
-- url     : https://prove2.me/submissions/40406abe-7d28-472c-89a8-4ce6c1a55fd1

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
import Theorems.Thm_GlobalTheory_CanTh_polyDeriv_const_mul
import Theorems.Thm_GlobalTheory_CanTh_thTerm_add_matrix
import Theorems.Thm_GlobalTheory_CanTh_differentiableOn_prod_fun
import Theorems.Thm_GlobalTheory_CanTh_differentiableOn_thTerm
import Theorems.Thm_GlobalTheory_CanTh_hasSum_polyDeriv_mul_prod_const
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
variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
variable [FiniteDimensional ℂ W] {κ : Type*} [Fintype κ]
namespace GlobalTheory.CanTh
theorem _root_.solution {G : W → ℂ} {τ S : κ → Matrix (Fin g) (Fin g) ℂ}
    {Z : κ → W → Fin g → ℂ} (hG : Differentiable ℂ G) (hZ : ∀ k, Differentiable ℂ (Z k))
    (hτ : ∀ k, τ k + S k ∈ ThetaDomain (Fin g)) (a b : κ → Fin g → ℝ) (P : MvPolynomial σ ℂ)
    (u : σ → W) (x : W) :
    HasSum (fun m : κ → Fin g → ℤ =>
        I2.polyDeriv P u (fun w => G w * ∏ k, thTerm (τ k) (a k) (b k) (Z k w) (m k)) x *
          cexp (π * I * ∑ k, ((fun i => (m k i : ℂ)) + fun i => (a k i : ℂ)) ⬝ᵥ
            S k *ᵥ ((fun i => (m k i : ℂ)) + fun i => (a k i : ℂ))))
      (I2.polyDeriv P u (fun w => G w *
        ∏ k, thetaChar (τ k + S k) (fun i => (a k i : ℂ)) (fun i => (b k i : ℂ)) (Z k w)) x) := by
  convert (hasSum_polyDeriv_mul_prod_const hG hZ hτ a b P u x).1 using 2 with m
  rw [mul_comm, ← polyDeriv_const_mul P u isOpen_univ _ _ (Set.mem_univ x)]
  · congr 1
    funext w
    simp only [thTerm_add_matrix, Finset.prod_mul_distrib, Finset.mul_sum, Complex.exp_sum]
    ring
  · exact hG.differentiableOn.mul (differentiableOn_prod_fun _ fun k _ =>
      differentiableOn_thTerm (T := fun _ => τ k) (fun _ _ => differentiableOn_const _)
        (hZ k).differentiableOn _ _ _)
end GlobalTheory.CanTh
