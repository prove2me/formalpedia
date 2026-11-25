-- Prove2me | solution 1 for GlobalTheory.HCA.exists_apOp_add_lower_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:36:07.866177+00:00
-- url     : https://prove2.me/submissions/94462075-e24b-4e9d-be85-0958dbe4fe9b

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
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conjCME_apply
import Theorems.Thm_P2M_GlobalTheory_T_exists_apOp_add_smul__30a907229398
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
theorem _root_.solution {d : ℕ} (U : Set (E d)) (k : ℕ)
    (A : ℕ → (n : ℕ) → (Fin n → Fin d) → E d → ℂ)
    (hA : ∀ i n w, ContDiffOn ℝ ∞ (A i n w) U) (t : ℕ → ℂ) :
    ∀ N ≤ k, ∃ a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a n w) U) ∧
      (∀ x ξ : E d, symb (2 * k) a x ξ = symb (2 * k) (A k) x ξ) ∧
      ∀ (u : E d → ℂ) (x : E d), apOp (2 * k) a u x =
        apOp (2 * k) (A k) u x + ∑ i ∈ Finset.range N, t i * apOp (2 * i) (A i) u x := by
  intro N
  induction N with
  | zero => intro _; exact ⟨A k, hA k, fun _ _ => rfl, fun u x => by simp⟩
  | succ N ih =>
    intro hN
    obtain ⟨a, ha, hs, hop⟩ := ih (by omega)
    obtain ⟨a'', h1, h2, h3⟩ :=
      GlobalTheory.T.exists_apOp_add_smul' d (2 * k) (2 * N) U a (A N) (t N) (by omega) ha (hA N)
    refine ⟨a'', h1, fun x ξ => ?_, fun u x => ?_⟩
    · rw [h2, if_neg (by omega), add_zero, hs]
    · rw [h3, hop, Finset.sum_range_succ]; ring
end GlobalTheory.HCA
