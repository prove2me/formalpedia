-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.FactorBound.norm_iteratedFDeriv_fourierFactor_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:10:20.022306+00:00
-- url     : https://prove2.me/submissions/0a148e81-c2dd-4804-9a4d-a7257de89417

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivHeckeFourierFactorLe
import Theorems.Thm_GlobalTheory_HeckeTwo_FactorBound_norm_iteratedFDeriv_le_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.FactorBound
namespace GlobalTheory.HeckeTwo.FactorBound
theorem _root_.solution :
    (∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ j : ℕ, ∃ s : ℕ, ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖iteratedDeriv j (hTrans σ ν) y‖ ≤ C * (|y| + |y|⁻¹) ^ s / (1 + |ν * y|) ^ N) →
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ c c' : ℝ, 0 < c → ∀ k : ℕ, ∃ m : ℕ, ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν β : ℝ, ν ≠ 0 → β ≠ 0 → ∀ w : ℂ, c ≤ w.im → w.im ≤ c' →
      ‖iteratedFDeriv ℝ k (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((ν * β * w.re : ℝ) : ℂ)) *
          hTrans σ ν (β * w.im)) w‖ ≤ C * (|β| + |β|⁻¹) ^ m / (1 + |ν * β|) ^ N := by
  intro H K hK hKH c c' hc k
  choose s hs using H K hK hKH
  refine ⟨k + ∑ j ∈ Finset.range (k + 1), s j, fun N => ?_⟩
  choose C hC using fun j => hs j (N + k)
  set M : ℝ := max c' c⁻¹ with hMdef
  set μ : ℝ := min 1 c with hμdef
  have hM : 0 < M := lt_of_lt_of_le (inv_pos.2 hc) (le_max_right _ _)
  have hμ : 0 < μ := lt_min one_pos hc
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (2 * Real.pi) ^ i *
      (|C (k - i)| * M ^ s (k - i) / μ ^ (N + k)), ?_⟩
  intro σ hσ ν β hν hβ w hw1 hw2
  have hσH : σ ∈ halfPlane := hKH hσ
  have ht : 0 < w.im := lt_of_lt_of_le hc hw1
  set t := w.im with htdef
  set B : ℝ := |β| + |β|⁻¹ with hBdef
  set A : ℝ := 1 + |ν * β| with hAdef
  have hβp : 0 < |β| := abs_pos.2 hβ
  have hB1 : 1 ≤ B := by
    rcases le_total 1 |β| with h | h
    · have := inv_nonneg.2 hβp.le; linarith
    · have := (one_le_inv₀ hβp).2 h; linarith
  have hA1 : 1 ≤ A := by have := abs_nonneg (ν * β); linarith
  have hApos : 0 < A := by linarith
  have hy : β * t ≠ 0 := mul_ne_zero hβ ht.ne'
  have hyB : |β * t| + |β * t|⁻¹ ≤ M * B := by
    rw [abs_mul, abs_of_pos ht, mul_inv, hBdef, mul_add]
    have h1 : |β| * t ≤ M * |β| := by
      rw [mul_comm M]; exact mul_le_mul_of_nonneg_left (hw2.trans (le_max_left _ _)) hβp.le
    have h2 : |β|⁻¹ * t⁻¹ ≤ M * |β|⁻¹ := by
      rw [mul_comm M]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hβp.le)
      exact (inv_anti₀ hc hw1).trans (le_max_right _ _)
    linarith
  have hyA : μ * A ≤ 1 + |ν * (β * t)| := by
    rw [← mul_assoc, abs_mul (ν * β), abs_of_pos ht, hAdef, mul_add, mul_one]
    have h1 : μ ≤ 1 := min_le_left _ _
    have h2 : μ ≤ t := (min_le_right _ _).trans hw1
    have h3 : μ * |ν * β| ≤ |ν * β| * t := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    linarith
  have hh : ∀ j, ‖iteratedDeriv j (hTrans σ ν) (β * t)‖ ≤
      |C j| * (M * B) ^ s j / (μ * A) ^ (N + k) := by
    intro j
    refine (hC j σ hσ ν (β * t) hν hy).trans ?_
    have hX : 0 ≤ (|β * t| + |β * t|⁻¹) ^ s j := by positivity
    calc C j * (|β * t| + |β * t|⁻¹) ^ s j / (1 + |ν * (β * t)|) ^ (N + k)
        ≤ |C j| * (|β * t| + |β * t|⁻¹) ^ s j / (1 + |ν * (β * t)|) ^ (N + k) := by
          gcongr
          exact le_abs_self _
      _ ≤ |C j| * (M * B) ^ s j / (μ * A) ^ (N + k) := by
          gcongr
  refine (norm_iteratedFDeriv_le_sum σ hσH ν β hβ k w ht).trans ?_
  rw [mul_div_assoc, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  set j := k - i with hjdef
  have hjk : j ≤ k := Nat.sub_le _ _
  have hsj : s j ≤ ∑ j ∈ Finset.range (k + 1), s j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_of_le hjk))
  have hd : (2 * Real.pi * |ν * β|) ^ i ≤ (2 * Real.pi) ^ i * A ^ k := by
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc |ν * β| ^ i ≤ A ^ i := pow_le_pow_left₀ (abs_nonneg _) (by linarith) i
      _ ≤ A ^ k := pow_le_pow_right₀ hA1 hik
  have he : |β| ^ j ≤ B ^ k :=
    (pow_le_pow_left₀ hβp.le (by have := inv_nonneg.2 hβp.le; linarith) j).trans (pow_le_pow_right₀ hB1 hjk)
  calc (k.choose i : ℝ) * (2 * Real.pi * |ν * β|) ^ i * (‖iteratedDeriv j (hTrans σ ν) (β * t)‖ * |β| ^ j)
      ≤ (k.choose i : ℝ) * ((2 * Real.pi) ^ i * A ^ k) *
          ((|C j| * (M * B) ^ s j / (μ * A) ^ (N + k)) * B ^ k) := by
        gcongr
        exact hh j
    _ = (k.choose i : ℝ) * (2 * Real.pi) ^ i * (|C j| * M ^ s j / μ ^ (N + k)) * (B ^ (k + s j) / A ^ N) := by
        have hA0 : A ≠ 0 := hApos.ne'
        have hμ0 : μ ≠ 0 := hμ.ne'
        rw [mul_pow, mul_pow, pow_add, pow_add]
        field_simp
        rw [mul_pow, mul_pow, pow_add]
        ring
    _ ≤ (k.choose i : ℝ) * (2 * Real.pi) ^ i * (|C j| * M ^ s j / μ ^ (N + k)) *
          (B ^ (k + ∑ j ∈ Finset.range (k + 1), s j) / A ^ N) := by
        gcongr
        all_goals first | exact hB1 | omega
end GlobalTheory.HeckeTwo.FactorBound
