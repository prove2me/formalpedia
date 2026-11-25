-- Prove2me | solution 1 for GlobalTheory.LeftSmoothing.rightDeriv_conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:21:42.533731+00:00
-- url     : https://prove2.me/submissions/f1ed955c-30b0-4240-a268-87efb3897bb2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftSmoothingProdExpSmoothCommute
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_ParamIntegral_iter_eq_zero_of_eventually
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conjCME_apply
import Theorems.Thm_GroundTheory_Automorphic_iteratedFDeriv_integral_eq
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightDerivEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] GroundTheory.Automorphic.conjCME_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.LeftSmoothing
open scoped Manifold Topology
open Set Filter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
variable (h : IsExpLieAlgebra G 𝔤) {n : ℕ} (X : Fin n → 𝔤) (κ : (Fin n → ℝ) → ℂ)
variable {h X κ}
namespace GlobalTheory.LeftSmoothing
theorem _root_.solution (hκ : Continuous κ) (hκs : HasCompactSupport κ) {f : G → ℂ}
    (hf : h.IsSmoothFun f) (Z : 𝔤) (g : G) :
    h.rightDeriv Z (conv h X κ f) g = conv h X κ (h.rightDeriv Z f) g := by
  show fderiv ℝ (fun Y : 𝔤 => conv h X κ f (g * h.expG Y)) 0 Z = _
  simp_rw [conv_mul_expG]
  rw [← iteratedFDeriv_one_apply (fun _ : Fin 1 => Z),
    iteratedFDeriv_integral_eq _ (integrand_contDiff hf g) (integrand_cont hκ hf g)
      (integrand_supp hκs f g) 1]
  have hint : Integrable (fun t => ParamIntegral.iter (integrand h X κ f g) 1 (0 : 𝔤) t) := by
    refine Continuous.integrable_of_hasCompactSupport
      ((integrand_cont hκ hf g 1).comp (continuous_const.prodMk continuous_id)) ?_
    refine HasCompactSupport.intro hκs fun t ht => ParamIntegral.iter_eq_zero_of_eventually ?_
    exact Eventually.of_forall fun Y => by
      simp [integrand, image_eq_zero_of_notMem_tsupport ht]
  rw [ContinuousMultilinearMap.integral_apply hint]
  simp only [conv]
  congr 1
  funext t
  rw [iter_integrand_eq hf]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.mul_apply']
  rw [iteratedFDeriv_one_apply]
  rfl
end GlobalTheory.LeftSmoothing
