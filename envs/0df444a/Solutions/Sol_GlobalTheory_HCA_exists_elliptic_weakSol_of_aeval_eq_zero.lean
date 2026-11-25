-- Prove2me | solution 1 for GlobalTheory.HCA.exists_elliptic_weakSol_of_aeval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:13:34.364803+00:00
-- url     : https://prove2.me/submissions/ffe0a195-0fe6-459d-971b-371b6bcb08d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftInvariantVectorFieldsExpCoordsSmoothFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSumSquaresRightDerivPowDifferentialOperatoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftTranslateSmoothCommuteLeftInvariantOpsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsApOpAddSmulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeakSolutionOfSmoothSolutionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEllipticWeakSolOfPolynomialLaplacianZero
import Theorems.Thm_GlobalTheory_HCA_exists_apOp_add_lower_sum
import Theorems.Thm_GlobalTheory_T_exists_sumSquaresRightDeriv_pow_differentialOperator
import Theorems.Thm_GlobalTheory_T_leftInvariantVectorFields_expCoords_smooth_frame
import Theorems.Thm_GlobalTheory_T_leftTranslate_smooth_commute_leftInvariantOps
import Theorems.Thm_GlobalTheory_T_weakSolution_of_smooth_solution
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_contDiff_comp_coordEquiv
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conjCME_apply
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
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.HCA
namespace GlobalTheory.HCA
theorem _root_.solution : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∃ r > 0, ∃ (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ), (∀ n w, ContDiffOn ℝ ∞ (a n w) (Metric.ball 0 r)) ∧ (∀ x ∈ Metric.ball (0 : E d) r, ∀ ξ : E d, ξ ≠ 0 → symb m a x ξ ≠ 0) ∧ ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P f = 0 → ∀ g : G, WeakSol (oneSys m a) (Metric.ball 0 r) (fun y => (f : G → ℂ) (g * h.expG (coordEquiv b (y)))) := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b P hP
  obtain ⟨r, hr, c, hc, hspan, hder⟩ := GlobalTheory.T.leftInvariantVectorFields_expCoords_smooth_frame 𝔸 G 𝔤 h d b
  choose A hAs hAsymb hAop using GlobalTheory.T.exists_sumSquaresRightDeriv_pow_differentialOperator 𝔸 G 𝔤 h d b r c ⟨hc, hspan, hder⟩
  obtain ⟨a, ha, hsa, hopa⟩ := exists_apOp_add_lower_sum (Metric.ball (0 : E d) r) P.natDegree A
    (fun i => hAs i) (fun i => P.coeff i) P.natDegree le_rfl
  refine ⟨r, hr, 2 * P.natDegree, a, ha, ?_, ?_⟩
  · intro x hx ξ hξ
    rw [hsa, hAsymb]
    obtain ⟨i, hi⟩ := hspan x hx ξ hξ
    have hpos : 0 < ∑ i, (∑ j, c (b i) j x * ξ j) ^ 2 :=
      lt_of_lt_of_le (by positivity : 0 < (∑ j, c (b i) j x * ξ j) ^ 2)
        (Finset.single_le_sum (f := fun i => (∑ j, c (b i) j x * ξ j) ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ i))
    exact_mod_cast (pow_pos hpos P.natDegree).ne'
  · intro f hf g
    obtain ⟨f', hf'1, hf'2⟩ := GlobalTheory.T.leftTranslate_smooth_commute_leftInvariantOps 𝔸 G 𝔤 h f g
    set Δ := ∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i) with hΔdef
    have hΔ : Δ ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) :=
      Subalgebra.sum_mem _ (fun i _ => Subalgebra.mul_mem _
        (Algebra.subset_adjoin ⟨b i, rfl⟩) (Algebra.subset_adjoin ⟨b i, rfl⟩))
    have hmem : Polynomial.aeval Δ P ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 hΔ) (Polynomial.aeval_mem_adjoin_singleton ℂ Δ)
    have hzero : ∀ y, (Polynomial.aeval Δ P f' : G → ℂ) y = 0 := by
      intro y; rw [hf'2 _ hmem y, hf]; rfl
    have hu : (fun y : E d => (f : G → ℂ) (g * h.expG (coordEquiv b y))) =
        fun y => (f' : G → ℂ) (h.expG (coordEquiv b y)) := by
      funext y; rw [hf'1]
    refine GlobalTheory.T.weakSolution_of_smooth_solution d (2 * P.natDegree) (Metric.ball 0 r) Metric.isOpen_ball a ha _
      (h.contDiff_comp_coordEquiv f.2 g b).contDiffOn ?_
    intro x hx
    rw [hopa, hu]
    have key := hzero (h.expG (coordEquiv b x))
    rw [Polynomial.aeval_eq_sum_range] at key
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, LinearMap.sum_apply, LinearMap.smul_apply] at key
    rw [← key, Finset.sum_range_succ _ P.natDegree, hP.coeff_natDegree, one_mul, add_comm]
    congr 1
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [hAop i f' x hx]
    · rw [hAop P.natDegree f' x hx]
end GlobalTheory.HCA
