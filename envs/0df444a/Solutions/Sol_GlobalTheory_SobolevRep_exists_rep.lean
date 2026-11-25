-- Prove2me | solution 1 for GlobalTheory.SobolevRep.exists_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:49:55.268069+00:00
-- url     : https://prove2.me/submissions/d3bfad5b-b3fc-4c19-9ee9-70a1daf6a754

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivExpGLineEqRightDerivPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValueAtZeroEqSumIntegralKernelIteratedDerivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSobolevRepresentationProdExp
import Theorems.Thm_GlobalTheory_SobolevRep_isSmoothFun_foldr
import Theorems.Thm_GlobalTheory_SobolevRep_continuous_of_isSmoothFun
import Theorems.Thm_GlobalTheory_SobolevRep_sum_integral_cons
import Theorems.Thm_GlobalTheory_T_exists_kernels_eval_zero_eq_sum_integral_iteratedDeriv
import Theorems.Thm_GlobalTheory_T_iteratedDeriv_expG_line_eq_foldr_rightDeriv
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conjCME_apply
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
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory
open GlobalTheory.SobolevRep
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
namespace GlobalTheory.SobolevRep
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) : ∀ (n : ℕ) (X : Fin n → 𝔤),
    ∃ (N : ℕ) (l : Fin N → List 𝔤) (κ : Fin N → (Fin n → ℝ) → ℂ),
      (∀ i, Continuous (κ i) ∧ tsupport (κ i) ⊆ Metric.closedBall 0 ε) ∧
      ∀ f : G → ℂ, h.IsSmoothFun f → ∀ g,
        f g = ∑ i, ∫ t, κ i t * (l i).foldr h.rightDeriv f (g * h.prodExp X t)
  | 0, X => by
    refine ⟨1, fun _ => [], fun _ _ => 1, fun _ => ⟨continuous_const, ?_⟩, fun f _ g => ?_⟩
    · intro t _
      rw [Subsingleton.elim t 0]; exact Metric.mem_closedBall_self hε.le
    · have hv : (volume : Measure (Fin 0 → ℝ)).real Set.univ = 1 := by
        simp [Measure.real, MeasureTheory.volume_pi]
      simp [IsExpLieAlgebra.prodExp, hv]
  | d + 1, X => by
    obtain ⟨N, l, K, hK, hrep⟩ := solution hε d (Fin.tail X)
    obtain ⟨a, ha, hu⟩ := GlobalTheory.T.exists_kernels_eval_zero_eq_sum_integral_iteratedDeriv ε hε
    refine ⟨3 * N,
      fun j => l (finProdFinEquiv.symm j).2 ++ List.replicate (finProdFinEquiv.symm j).1 (X 0),
      fun j t => a (finProdFinEquiv.symm j).1 (t 0) * K (finProdFinEquiv.symm j).2 (Fin.tail t),
      fun j => ⟨?_, tsupport_cons_kernel hε.le (ha _).2 (hK _).2⟩, fun f hf g => ?_⟩
    · exact ((ha _).1.comp (continuous_apply 0)).mul
        ((hK _).1.comp (continuous_pi fun j => continuous_apply j.succ))
    · rw [← finProdFinEquiv.sum_comp]
      simp only [Equiv.symm_apply_apply, List.foldr_append]
      rw [Fintype.sum_prod_type]
      have h0 := hu _ (GlobalTheory.T.iteratedDeriv_expG_line_eq_foldr_rightDeriv 𝔸 G 𝔤 h f hf (X 0) g 0).1
      simp only [zero_smul, h.expG_zero, mul_one] at h0
      rw [h0]
      refine Finset.sum_congr rfl fun p _ => ?_
      have hp := isSmoothFun_foldr h hf (List.replicate p (X 0))
      rw [sum_integral_cons h X hε.le (ha p).1 (ha p).2 (fun i => (hK i).1) (fun i => (hK i).2)
        (fun i => continuous_of_isSmoothFun h (isSmoothFun_foldr h hp (l i))) (hrep _ hp) g]
      congr 1; funext s
      rw [(GlobalTheory.T.iteratedDeriv_expG_line_eq_foldr_rightDeriv 𝔸 G 𝔤 h f hf (X 0) g p).2 s]
end GlobalTheory.SobolevRep
