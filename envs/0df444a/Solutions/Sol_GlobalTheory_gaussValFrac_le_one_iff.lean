-- Prove2me | solution 1 for GlobalTheory.gaussValFrac_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T13:02:00.243385+00:00
-- url     : https://prove2.me/submissions/6aecef20-b557-4bc7-8cba-2f0c00ba6fc4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
open MvPolynomial
variable {K Γ₀ σ τ : Type*} [Field K]
variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
variable {F : Type*} [Field F] [Algebra (MvPolynomial σ K) F]
  [IsFractionRing (MvPolynomial σ K) F]

private lemma exists_gaussVal_eq (f : MvPolynomial σ K) : ∃ c : K, gaussVal v f = v c := by
  by_cases hf : f = 0
  · refine ⟨0, ?_⟩
    simp [hf]
  · have hc : AddMonoidAlgebra.coeff f ≠ 0 :=
      AddMonoidAlgebra.coeff_eq_zero.not.mpr hf
    obtain ⟨m, -, hm⟩ := exists_mem_support_coeffSup_eq (N := v) hc
    refine ⟨coeff m f, ?_⟩
    simpa [gaussVal, gaussValAlg, MvPolynomial.coeff] using hm

theorem solution {x : F} :
    gaussValFrac v σ F x ≤ 1 ↔ ∃ f g : MvPolynomial σ K, gaussVal v f ≤ 1 ∧ gaussVal v g = 1 ∧
      x = algebraMap _ F f / algebraMap _ F g := by
  constructor
  · intro hx
    obtain ⟨f, g, rfl⟩ :=
      IsLocalization.exists_mk'_eq (nonZeroDivisors (MvPolynomial σ K)) x
    rw [IsFractionRing.mk'_eq_div, Valuation.map_div, gaussValFrac_algebraMap,
      gaussValFrac_algebraMap] at hx
    obtain ⟨b, hb⟩ := exists_gaussVal_eq v (g : MvPolynomial σ K)
    have hg_ne : gaussVal v (g : MvPolynomial σ K) ≠ 0 :=
      (gaussVal_eq_zero_iff v).not.mpr (nonZeroDivisors.ne_zero g.2)
    have hg0 : 0 < gaussVal v (g : MvPolynomial σ K) :=
      lt_of_le_of_ne (zero_le : 0 ≤ gaussVal v (g : MvPolynomial σ K)) hg_ne.symm
    have hb0 : b ≠ 0 := by
      intro h0
      apply hg_ne
      simp [hb, h0]
    have hle : gaussVal v f ≤ v b := by
      have := (div_le_one₀ hg0).mp hx
      rwa [hb] at this
    have hb_ne : v b ≠ 0 := by rwa [← hb]
    refine ⟨C b⁻¹ * f, C b⁻¹ * (g : MvPolynomial σ K), ?_, ?_, ?_⟩
    · have heq : gaussVal v (C b⁻¹ * f) = (v b)⁻¹ * gaussVal v f := by
        rw [map_mul, gaussVal_C, Valuation.map_inv]
      rw [heq]
      have : (v b)⁻¹ * gaussVal v f ≤ (v b)⁻¹ * v b :=
        mul_le_mul_of_nonneg_left hle (zero_le : 0 ≤ (v b)⁻¹)
      exact this.trans (inv_mul_cancel₀ hb_ne).le
    · have heq : gaussVal v (C b⁻¹ * (g : MvPolynomial σ K)) =
          (v b)⁻¹ * v b := by
        rw [map_mul, gaussVal_C, Valuation.map_inv, hb]
      rw [heq, inv_mul_cancel₀ hb_ne]
    · simp [IsFractionRing.mk'_eq_div, map_mul, map_C]
      have hC : algebraMap (MvPolynomial σ K) F (C b⁻¹) ≠ 0 := by
        simp [hb0]
      field [hC]
  · rintro ⟨f, g, hf1, hg1, rfl⟩
    simp [gaussValFrac_algebraMap, hf1, hg1]
