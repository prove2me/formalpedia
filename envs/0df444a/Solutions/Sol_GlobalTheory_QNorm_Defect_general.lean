-- Prove2me | solution 1 for GlobalTheory.QNorm.Defect.general
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:10:39.434402+00:00
-- url     : https://prove2.me/submissions/663d9f6b-eb5f-4828-b81e-fd771159153d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsGlobalUniformizerResidueRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSubSqLtOneOfTwoLtOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EvenOrderNormsOneAddFourMulOfNoRootStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitMulSqQuadraticDefectStepStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNormalFormNonsquareAdicCompletion
import Theorems.Thm_GlobalTheory_QNorm_Defect_exists_exp
import Theorems.Thm_GlobalTheory_QNorm_Defect_not_isSquare_mul_sq
import Theorems.Thm_GlobalTheory_QNorm_Defect_unit_case
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
open GlobalTheory.QNorm.Defect
variable {K : Type} [Field K] (w : Valuation K ℤᵐ⁰)
namespace GlobalTheory.QNorm.Defect
theorem _root_.solution (h2 : (2 : K) ≠ 0) (π : K) (hπ : w π = WithZero.exp (-1))
    (hsq : ∀ x : K, w (x - 1) < w 4 → IsSquare x)
    (hres : w 2 < 1 → ∀ x : K, w x ≤ 1 → ∃ y : K, w y ≤ 1 ∧ w (x - y ^ 2) < 1)
    (δ : K) (hδ : δ ≠ 0) (hns : ¬ IsSquare δ) :
    ∃ c : K, c ≠ 0 ∧ ((∃ n : ℤ, w (δ * c ^ 2) = WithZero.exp (2 * n + 1)) ∨
      (w (δ * c ^ 2) = 1 ∧ w 4 < w (δ * c ^ 2 - 1) ∧
        ∃ n : ℤ, w (δ * c ^ 2 - 1) = WithZero.exp (2 * n + 1)) ∨ EvenNorms w (δ * c ^ 2)) := by
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  obtain ⟨m, hm⟩ := exists_exp w h4
  obtain ⟨d, hd⟩ := exists_exp w hδ
  rcases Int.even_or_odd' d with ⟨k, hk | hk⟩
  · have hπ0 : π ≠ 0 := by
      intro h0; rw [h0] at hπ; simp at hπ; exact WithZero.exp_ne_zero hπ.symm
    have hc0 : π ^ k ≠ 0 := zpow_ne_zero _ hπ0
    have hu : w (δ * (π ^ k) ^ 2) = 1 := by
      rw [map_mul, map_pow, map_zpow₀, hπ, hd, ← WithZero.exp_zsmul, ← WithZero.exp_nsmul,
        ← WithZero.exp_add, ← WithZero.exp_zero]
      congr 1
      simp [hk]
    obtain ⟨c', hc', H⟩ := unit_case w h2 π hπ hsq hres m hm (-m).toNat _ hu
      (not_isSquare_mul_sq hc0 hns) (by
        refine (w.map_sub_le hu.le (by simp)).trans ?_
        rw [← WithZero.exp_zero, WithZero.exp_le_exp]
        omega)
    refine ⟨π ^ k * c', mul_ne_zero hc0 hc', Or.inr ?_⟩
    have : δ * (π ^ k * c') ^ 2 = δ * (π ^ k) ^ 2 * c' ^ 2 := by ring
    rw [this]; exact H
  · refine ⟨1, one_ne_zero, Or.inl ⟨k, ?_⟩⟩
    rw [one_pow, mul_one, hd, hk]
end GlobalTheory.QNorm.Defect
