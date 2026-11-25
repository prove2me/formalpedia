-- Prove2me | solution 1 for GlobalTheory.HCA.integral_mul_sum_cons_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:14:48.366259+00:00
-- url     : https://prove2.me/submissions/d1f66620-a6be-460b-9f71-cec612800521

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsExpLieAlgebraComplexUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DixmierMalliavinFactorisationBasisStepStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousLeftTranslateBoundedDerivFunctional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDixmierMalliavinDecompProdExp
import Theorems.Thm_GlobalTheory_HCA_integrable_integral_fin_cons
import Theorems.Thm_GlobalTheory_HCA_prodExp_fin_succ
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_continuous_prodExp
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conjCME_apply
import Theorems.Thm_GroundTheory_Automorphic_integral_fin_succ_cons
import Theorems.Thm_GroundTheory_Automorphic_tsupport_cons_kernel
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
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.HCA
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
namespace GlobalTheory.HCA
theorem _root_.solution (h : IsExpLieAlgebra G 𝔤) {n N : ℕ} (X : Fin (n + 1) → 𝔤) {ε : ℝ}
    (hε : 0 ≤ ε) {u : ℝ → ℂ} (hu : Continuous u) (hus : tsupport u ⊆ Set.Icc (-ε) ε)
    {κ : Fin N → (Fin n → ℝ) → ℂ} (hκ : ∀ m, Continuous (κ m))
    (hκs : ∀ m, tsupport (κ m) ⊆ Metric.closedBall 0 ε) {Φ : Fin N → G → ℂ}
    (hΦ : ∀ m, Continuous (Φ m)) (Ψ : ℝ → ℂ)
    (hΨ : ∀ s, Ψ s = ∑ m, ∫ t', κ m t' * Φ m (h.expG (s • X 0) * h.prodExp (Fin.tail X) t')) :
    ∫ s, u s * Ψ s = ∑ m, ∫ t, u (t 0) * κ m (Fin.tail t) * Φ m (h.prodExp X t) := by
  have hF : ∀ m, Integrable (fun t : Fin (n + 1) → ℝ => u (t 0) * κ m (Fin.tail t) * Φ m (h.prodExp X t)) := by
    intro m
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hu.comp (continuous_apply 0)).mul
        ((hκ m).comp (continuous_pi fun j => continuous_apply j.succ))).mul
        ((hΦ m).comp (h.continuous_prodExp X))
    · exact HasCompactSupport.mul_right (f := fun t : Fin (n + 1) → ℝ => u (t 0) * κ m (Fin.tail t))
        ((isCompact_closedBall 0 ε).of_isClosed_subset (isClosed_tsupport _)
          (tsupport_cons_kernel hε hus (hκs m)))
  have heq : ∀ m s, u s * ∫ t', κ m t' * Φ m (h.expG (s • X 0) * h.prodExp (Fin.tail X) t') =
      ∫ t', u ((Fin.cons s t' : Fin (n + 1) → ℝ) 0) * κ m (Fin.tail (Fin.cons s t' : Fin (n + 1) → ℝ)) *
        Φ m (h.prodExp X (Fin.cons s t')) := by
    intro m s
    rw [← integral_const_mul]
    congr 1; funext t'
    simp only [Fin.cons_zero, Fin.tail_cons, prodExp_fin_succ h X, mul_assoc]
  simp_rw [hΨ, Finset.mul_sum]
  rw [integral_finsetSum _ (fun m _ => by
    simp_rw [heq m]; exact integrable_integral_fin_cons (hF m))]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp_rw [heq m]
  exact (integral_fin_succ_cons (hF m)).symm
end GlobalTheory.HCA
