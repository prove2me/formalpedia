-- Prove2me | solution 1 for GlobalTheory.QNorm.Defect.unit_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:22:24.504849+00:00
-- url     : https://prove2.me/submissions/60d3721e-5a2c-4d86-b4c1-3b49ea462552

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsGlobalUniformizerResidueRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSubSqLtOneOfTwoLtOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EvenOrderNormsOneAddFourMulOfNoRootStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitMulSqQuadraticDefectStepStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNormalFormNonsquareAdicCompletion
import Theorems.Thm_GlobalTheory_QNorm_Defect_exists_exp
import Theorems.Thm_GlobalTheory_QNorm_Defect_map_two_le
import Theorems.Thm_GlobalTheory_QNorm_Defect_evenNorms_of_le_four
import Theorems.Thm_GlobalTheory_QNorm_Defect_not_isSquare_mul_sq
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_T_exists_unit_mul_sq_quadratic_defect_step
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
    (m : ℤ) (hm : w 4 = WithZero.exp m) (N : ℕ) :
    ∀ δ : K, w δ = 1 → ¬ IsSquare δ → w (δ - 1) ≤ WithZero.exp (m + N) →
      ∃ c : K, c ≠ 0 ∧ ((w (δ * c ^ 2) = 1 ∧ w 4 < w (δ * c ^ 2 - 1) ∧
        ∃ n : ℤ, w (δ * c ^ 2 - 1) = WithZero.exp (2 * n + 1)) ∨ EvenNorms w (δ * c ^ 2)) := by
  induction N with
  | zero =>
    intro δ hδ hns h
    refine ⟨1, one_ne_zero, Or.inr ?_⟩
    rw [one_pow, mul_one]
    exact evenNorms_of_le_four w h2 hsq δ hδ hns (by simpa [hm] using h)
  | succ N ih =>
    intro δ hδ hns h
    by_cases h4 : w (δ - 1) ≤ w 4
    · refine ⟨1, one_ne_zero, Or.inr ?_⟩
      rw [one_pow, mul_one]
      exact evenNorms_of_le_four w h2 hsq δ hδ hns h4
    rw [not_le] at h4
    have hne : δ - 1 ≠ 0 := by
      intro h0; rw [h0] at h4; simp at h4
    obtain ⟨d, hd⟩ := exists_exp w hne
    have hle : w (δ - 1) ≤ 1 := w.map_sub_le hδ.le (by simp)
    have hd0 : d ≤ 0 := by
      rw [hd, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle; exact hle
    rcases Int.even_or_odd' d with ⟨k, hk | hk⟩
    · have hw2 : w 2 < 1 := by
        refine lt_of_le_of_ne (map_two_le w) fun h1 => ?_
        have : w 4 = 1 := by
          have : (4 : K) = 2 * 2 := by norm_num
          rw [this, map_mul, h1, one_mul]
        rw [this] at h4
        exact absurd hle (not_le.2 h4)
      obtain ⟨c, hc, hlt⟩ := GlobalTheory.T.exists_unit_mul_sq_quadratic_defect_step K w δ π (-k).toNat hπ (hres hw2) hδ h4 (by
        rw [hd]; congr 1; omega)
      have hc0 : c ≠ 0 := by
        intro h0; rw [h0] at hc; simp at hc
      have hb : w (δ * c ^ 2 - 1) ≤ WithZero.exp (m + N) := by
        by_cases h0 : δ * c ^ 2 - 1 = 0
        · rw [h0]; simp
        obtain ⟨e, he⟩ := exists_exp w h0
        have := hlt.trans_le h
        rw [he, WithZero.exp_lt_exp] at this
        rw [he, WithZero.exp_le_exp]
        push_cast at this
        omega
      obtain ⟨c', hc', H⟩ := ih (δ * c ^ 2) (by simp [hδ, hc]) (not_isSquare_mul_sq hc0 hns) hb
      refine ⟨c * c', mul_ne_zero hc0 hc', ?_⟩
      have : δ * (c * c') ^ 2 = δ * c ^ 2 * c' ^ 2 := by ring
      rw [this]; exact H
    · refine ⟨1, one_ne_zero, Or.inl ?_⟩
      rw [one_pow, mul_one]
      exact ⟨hδ, h4, k, by rw [hd, hk]⟩
end GlobalTheory.QNorm.Defect
