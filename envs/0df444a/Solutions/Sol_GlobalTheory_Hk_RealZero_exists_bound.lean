-- Prove2me | solution 1 for GlobalTheory.Hk.RealZero.exists_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:27:53.203856+00:00
-- url     : https://prove2.me/submissions/334951e5-045c-44f6-93d9-a6c072e100bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionLogDerivLocalFormulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyLogDerivPositivityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionUniqueSimpleExceptionalZero
import Theorems.Thm_GlobalTheory_Hk_RealZero_re_le_one
import Theorems.Thm_GlobalTheory_T_rayClassFamily_logDeriv_re_gt_one
import Theorems.Thm_GlobalTheory_T_rayClassLFunction_logDeriv_local_formula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
namespace GlobalTheory.Hk.RealZero
private lemma sum_real_zeros_div_sub_le_re_finsum_div_sub (m : ℂ → ℕ) (σ : ℝ) (S : Set ℂ) (hS : S.Finite) (T : Finset ℝ)
    (hTS : ∀ β ∈ T, (β : ℂ) ∈ S) (hre : ∀ w ∈ S, w.re < σ) :
    ∑ β ∈ T, (m β : ℝ) / (σ - β) ≤ (∑ᶠ w ∈ S, (m w : ℂ) / ((σ : ℂ) - w)).re := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, Complex.re_sum]
  have hnn : ∀ w ∈ hS.toFinset, 0 ≤ ((m w : ℂ) / ((σ : ℂ) - w)).re := by
    intro w hw
    rw [Set.Finite.mem_toFinset] at hw
    have h1 := hre w hw
    rw [Complex.div_re]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero,
      Complex.sub_re, Complex.ofReal_re]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (Complex.normSq_nonneg _)
  have himg : ∑ β ∈ T, (m β : ℝ) / (σ - β)
      = ∑ w ∈ T.image (fun β : ℝ => (β : ℂ)), ((m w : ℂ) / ((σ : ℂ) - w)).re := by
    rw [Finset.sum_image (fun a _ b _ h => Complex.ofReal_injective h)]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    have e : (m β : ℂ) / ((σ : ℂ) - β) = (((m β : ℝ) / (σ - β) : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_natCast]
    rw [e, Complex.ofReal_re]
  rw [himg]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun w hw _ => hnn w hw)
  intro w hw
  rw [Finset.mem_image] at hw
  obtain ⟨β, hβ, rfl⟩ := hw
  rw [Set.Finite.mem_toFinset]
  exact hTS β hβ
private lemma neg_re_le_neg_add_of_norm_sub_le_of_le_re (A B : ℂ) (x y : ℝ) (h : ‖A - B‖ ≤ x) (hy : y ≤ B.re) :
    -A.re ≤ -y + x := by
  have h1 := Complex.re_le_norm (B - A)
  rw [norm_sub_rev, Complex.sub_re] at h1
  linarith
end GlobalTheory.Hk.RealZero
end

set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RealZero
namespace GlobalTheory.Hk.RealZero
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ),
    ∀ σ : ℝ, 1 < σ → σ ≤ 7 / 4 → ∀ T : Finset ℝ,
    (∀ β ∈ T, 3 / 4 ≤ β ∧ 𝓕.F χ β = 0) →
    (LSeries (𝓕.lamChi χ) σ).re ≤ (if χ = 1 then 1 / (σ - 1) else 0) + C * 𝓕.ell 0
      - ∑ β ∈ T, (analyticOrderNatAt (𝓕.F χ) β : ℝ) / (σ - β) := by
  obtain ⟨C, hC, hmain⟩ := GlobalTheory.T.rayClassLFunction_logDeriv_local_formula
  refine ⟨C, hC, fun 𝓕 χ σ hσ1 hσ2 T hT => ?_⟩
  obtain ⟨hfin, -, happ⟩ := hmain 𝓕 χ 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hfin happ
  have hs1 : 1 < (σ : ℂ).re := by simpa using hσ1
  obtain ⟨-, -, hFs, hL⟩ := GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ σ hs1
  have hnear : ‖(σ : ℂ) - 5 / 4‖ ≤ 1 / 2 := by
    have e : (σ : ℂ) - 5 / 4 = ((σ - 5 / 4 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hE := happ σ hnear hFs
  have hsum := sum_real_zeros_div_sub_le_re_finsum_div_sub (analyticOrderNatAt (𝓕.F χ)) σ _ hfin T ?_ ?_
  · have h2 := neg_re_le_neg_add_of_norm_sub_le_of_le_re _ _ _ _ hE hsum
    rw [← hL, Complex.add_re, Complex.neg_re]
    split_ifs with h1
    · have e : (1 / ((σ : ℂ) - 1)).re = 1 / (σ - 1) := by
        rw [show (1 : ℂ) / ((σ : ℂ) - 1) = ((1 / (σ - 1) : ℝ) : ℂ) by
          rw [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one], Complex.ofReal_re]
      rw [e]
      linarith
    · rw [Complex.zero_re]
      linarith
  · intro β hβ
    obtain ⟨h34, hz⟩ := hT β hβ
    have hb1 : β ≤ 1 := by simpa using re_le_one 𝓕 χ hz
    refine ⟨?_, hz⟩
    have e : (β : ℂ) - 5 / 4 = ((β - 5 / 4 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  · intro w hw
    have := re_le_one 𝓕 χ hw.2
    linarith
end GlobalTheory.Hk.RealZero
