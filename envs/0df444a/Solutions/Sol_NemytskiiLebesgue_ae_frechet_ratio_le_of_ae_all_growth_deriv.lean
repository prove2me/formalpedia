-- Prove2me | solution 1 for NemytskiiLebesgue.ae_frechet_ratio_le_of_ae_all_growth_deriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:37:58.116434+00:00
-- url     : https://prove2.me/submissions/81e18710-d1e7-4dca-8196-f483615d715a

module
public import Mathlib.Analysis.Calculus.MeanValue
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet
public import Theorems.Thm_NemytskiiLebesgue_frechet_remainder_le_of_all_in_set_icc_zero_one_norm_le
section
public section
namespace NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped ENNReal Topology
private lemma ae_norm_frechet_remainder_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ^k)}
    (hf' : ∀ᵐ ω : Ω ∂μ, Continuous (f' ω))
    (hff' : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (f ω) (f' ω ξ) ξ)
    {C : ℝ} (hC : 0 < C)
    {α : ℝ} (hα : 0 ≤ α)
    {b : Ω → ℝ} (h0b : 0 ≤ᵐ[μ] b)
    (hf'bCα : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ α)
    (u l : Ω → ℝ^m) :
    ∀ᵐ ω : Ω ∂μ,
      ‖f ω (u ω + l ω) - f ω (u ω) - f' ω (u ω) (l ω)‖ ≤
      (2 * b ω + C * (‖u ω‖ + ‖l ω‖) ^ α + C * ‖u ω‖ ^ α) * ‖l ω‖ := by
  filter_upwards [hff', hf', h0b, hf'bCα] with ω hω₁ hω₂ hω₃ hω₄
  apply frechet_remainder_le_of_all_in_set_icc_zero_one_norm_le hω₁
  intro t ht
  apply le_trans (norm_sub_le _ _)
  apply le_trans (add_le_add (hω₄ _) (hω₄ _))
  nlinarith [show ‖u ω + t • l ω‖ ^ α ≤ (‖u ω‖ + ‖l ω‖) ^ α from
    Real.rpow_le_rpow (norm_nonneg _) (by
      simpa [norm_smul, abs_of_nonneg ht.left] using
        le_trans (norm_add_le (u ω) (t • l ω)) <| by
          simpa [norm_smul, abs_of_nonneg ht.left] using
            mul_le_mul_of_nonneg_right ht.right (norm_nonneg (l ω)))
      hα]
end NemytskiiLebesgue
end
end

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped ENNReal Topology
namespace NemytskiiLebesgue
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ^k)}
    (hf' : ∀ᵐ ω : Ω ∂μ, Continuous (f' ω))
    (hff' : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (f ω) (f' ω ξ) ξ)
    {C : ℝ} (hC : 0 < C)
    {p : ℝ} (h1p : 1 ≤ p)
    {r : ℝ} (h1r : 1 ≤ r)
    {b : Ω → ℝ} (h0b : 0 ≤ᵐ[μ] b)
    (hf'bCpr : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ (p / r))
    {g : Ω → ℝ} (h0g : 0 ≤ᵐ[μ] g)
    {v : Ω → ℝ^m} (hvg : ∀ᵐ ω : Ω ∂μ, ‖v ω‖ ≤ g ω)
    (u : Ω → ℝ^m) :
    ∀ᵐ ω : Ω ∂μ,
      ‖f ω (u ω + v ω) - f ω (u ω) - f' ω (u ω) (v ω)‖ / ‖v ω‖ ≤
      2 * b ω + C * (‖u ω‖ + g ω) ^ (p / r) + C * ‖u ω‖ ^ (p / r) := by
  have remainder_bound :
    ∀ᵐ ω : Ω ∂μ,
      ‖f ω (u ω + v ω) - f ω (u ω) - f' ω (u ω) (v ω)‖ ≤
      (2 * b ω + C * (‖u ω‖ + ‖v ω‖) ^ (p / r) + C * ‖u ω‖ ^ (p / r)) * ‖v ω‖ := by
    apply_rules [ae_norm_frechet_remainder_le]
    positivity
  filter_upwards [remainder_bound, hvg, h0b, h0g] with ω hω₁ hω₂ hω₃ hω₄
  apply div_le_of_le_mul₀ <;> simp_all only [Pi.zero_apply,
      norm_nonneg]
  · positivity
  · exact hω₁.trans
      (mul_le_mul_of_nonneg_right (add_le_add_three le_rfl
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow
            (add_nonneg (norm_nonneg (u ω)) (norm_nonneg (v ω)))
            ((add_le_add_iff_left ‖u ω‖).← hω₂) (by positivity))
        hC.le)
      le_rfl) (norm_nonneg (v ω)))
end NemytskiiLebesgue
