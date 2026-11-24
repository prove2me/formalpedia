-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.TermBoundDeriv.iteratedDeriv_hTrans_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:40:20.228734+00:00
-- url     : https://prove2.me/submissions/7a3d923e-e8ce-47f6-ad4e-f490815feee9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivHeckePhiFourierTransformBound
import Theorems.Thm_GlobalTheory_HeckeTwo_TermBoundDeriv_rpow_le_add_inv_pow

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
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermBoundDeriv
namespace GlobalTheory.HeckeTwo.TermBoundDeriv
theorem _root_.solution :
    (∀ j : ℕ, ∃ (S : Finset (ℕ × ℕ × ℕ)) (P : ℕ × ℕ × ℕ → Polynomial ℂ),
    (∀ p ∈ S, 2 ≤ p.1 + 2 * p.2.1 ∧ p.1 + 2 * p.2.1 = p.2.2 + 2 + j) ∧
    ∀ σ ∈ halfPlane, ∀ ν y : ℝ, y ≠ 0 →
      iteratedDeriv j (hTrans σ ν) y = ∑ p ∈ S, (P p).eval σ * GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y) → (∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ a b m : ℕ, 2 ≤ a + 2 * b → ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖GlobalTheory.HeckeTwo.TermSmooth.intT σ ν a b m y‖ ≤ C * |y| ^ ((m : ℝ) + 1 - a - 2 * b - 2 * σ.re) / (1 + |ν * y|) ^ N) →
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ j : ℕ, ∃ s : ℕ, ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖iteratedDeriv j (hTrans σ ν) y‖ ≤ C * (|y| + |y|⁻¹) ^ s / (1 + |ν * y|) ^ N := by
  intro hder hint K hK hKH j
  obtain ⟨S, P, hS, hEq⟩ := hder j
  obtain ⟨R, hR⟩ : ∃ R, ∀ σ ∈ K, ‖σ‖ ≤ R := hK.isBounded.exists_norm_le
  refine ⟨⌈1 + (j : ℝ) + 2 * R⌉₊, fun N => ?_⟩
  have hCex : ∀ p : ℕ × ℕ × ℕ, ∃ C : ℝ, 0 ≤ C ∧ (p ∈ S → ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y‖ ≤
        C * |y| ^ ((p.2.2 : ℝ) + 1 - p.1 - 2 * p.2.1 - 2 * σ.re) / (1 + |ν * y|) ^ N) := by
    intro p
    by_cases hp : p ∈ S
    · obtain ⟨C, hC⟩ := hint K hK hKH p.1 p.2.1 p.2.2 (hS p hp).1 N
      refine ⟨max C 0, le_max_right _ _, fun _ σ hσ ν y hν hy => (hC σ hσ ν y hν hy).trans ?_⟩
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)
    · exact ⟨0, le_rfl, fun h => absurd h hp⟩
  choose Cp hCp0 hCp using hCex
  have hBex : ∀ p : ℕ × ℕ × ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ σ ∈ K, ‖(P p).eval σ‖ ≤ B := by
    intro p
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (P p).continuous.continuousOn
    exact ⟨max B 0, le_max_right _ _, fun σ hσ => (hB σ hσ).trans (le_max_left _ _)⟩
  choose B hB0 hB using hBex
  refine ⟨∑ p ∈ S, B p * Cp p, fun σ hσ ν y hν hy => ?_⟩
  have hy' : 0 < |y| := abs_pos.mpr hy
  have hD : 0 < (1 + |ν * y|) ^ N := by positivity
  have hre : |σ.re| ≤ R := (Complex.abs_re_le_norm σ).trans (hR σ hσ)
  rw [hEq σ (hKH hσ) ν y hy]
  calc ‖∑ p ∈ S, (P p).eval σ * GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y‖
      ≤ ∑ p ∈ S, ‖(P p).eval σ * GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y‖ :=
        norm_sum_le _ _
    _ ≤ ∑ p ∈ S, B p * (Cp p * (|y| + |y|⁻¹) ^ ⌈1 + (j : ℝ) + 2 * R⌉₊ / (1 + |ν * y|) ^ N) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [norm_mul]
        apply mul_le_mul (hB p σ hσ) _ (norm_nonneg _) (hB0 p)
        refine (hCp p hp σ hσ ν y hν hy).trans ?_
        apply div_le_div_of_nonneg_right _ hD.le
        apply mul_le_mul_of_nonneg_left _ (hCp0 p)
        apply rpow_le_add_inv_pow hy'
        have hc : (p.1 : ℝ) + 2 * p.2.1 = p.2.2 + 2 + j := by exact_mod_cast (hS p hp).2
        have he : (p.2.2 : ℝ) + 1 - p.1 - 2 * p.2.1 - 2 * σ.re = -(1 + j + 2 * σ.re) := by
          linarith
        rw [he, abs_neg]
        refine le_trans ?_ (Nat.le_ceil _)
        have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        calc |1 + (j : ℝ) + 2 * σ.re| ≤ |1 + (j : ℝ)| + |2 * σ.re| := abs_add_le _ _
          _ = 1 + j + 2 * |σ.re| := by
              rw [abs_of_nonneg (by linarith), abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
          _ ≤ 1 + j + 2 * R := by linarith
    _ = (∑ p ∈ S, B p * Cp p) * (|y| + |y|⁻¹) ^ ⌈1 + (j : ℝ) + 2 * R⌉₊ / (1 + |ν * y|) ^ N := by
        rw [Finset.sum_mul, Finset.sum_div]
        refine Finset.sum_congr rfl fun p _ => ?_
        ring
end GlobalTheory.HeckeTwo.TermBoundDeriv
