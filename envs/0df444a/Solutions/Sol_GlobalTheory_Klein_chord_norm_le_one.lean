-- Prove2me | solution 1 for GlobalTheory.Klein.chord_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:05:10.78729+00:00
-- url     : https://prove2.me/submissions/495e38ed-40bb-4b2a-8fd1-cf0ec121c31e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ReductionSetSubgroup
import Theorems.Thm_GlobalTheory_latticePointEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.latticePointEquiv_mk


section
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators
namespace GlobalTheory.Klein
private theorem ultra_add_le {K : Type*} [NormedField K] [IsUltrametricDist K] {x y : K} {C : ℝ}
    (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C) : ‖x + y‖ ≤ C :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
private theorem mul_le_of {K : Type*} [NormedField K] {x y : K} {C D : ℝ}
    (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ D) : ‖x * y‖ ≤ C * D := by
  rw [norm_mul]
  exact mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx)
private theorem cubic_le {K : Type*} [NormedField K] [IsUltrametricDist K] {x k₂ k₁ k₀ : K} {ρ : ℝ}
    (h2 : ‖(2 : K)‖ = 1) (hρ : 1 ≤ ρ) (hx : ‖x‖ ≤ ρ) (hk₂ : ‖k₂‖ ≤ 1) (hk₁ : ‖k₁‖ ≤ 1) (hk₀ : ‖k₀‖ ≤ 1) :
    ‖2 * 2 * (x * x * x) + k₂ * (x * x) + k₁ * x + k₀‖ ≤ ρ * ρ * ρ := by
  have h1 : 1 ≤ ρ * ρ := by nlinarith
  refine ultra_add_le (ultra_add_le (ultra_add_le ?_ ?_) ?_) ?_
  · simpa using mul_le_of (mul_le_of h2.le h2.le) (mul_le_of (mul_le_of hx hx) hx)
  · exact (mul_le_of hk₂ (mul_le_of hx hx)).trans (by nlinarith)
  · exact (mul_le_of hk₁ hx).trans (by nlinarith)
  · exact hk₀.trans (by nlinarith)
private theorem le_of_mul_self_le_mul_self' {x y : ℝ} (h : x * x ≤ y * y) (hy : 0 ≤ y) : x ≤ y :=
  (abs_le_of_sq_le_sq' (by simpa only [sq] using h) hy).2
variable {p : ℕ} [Fact p.Prime]
end GlobalTheory.Klein
end

set_option autoImplicit false
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators
open GlobalTheory GlobalTheory.Klein
namespace GlobalTheory.Klein
theorem _root_.solution {K : Type*} [NormedField K] [IsUltrametricDist K] {a b A B X k₂ k₁ k₀ : K}
    (h2 : ‖(2 : K)‖ = 1) (ha : 1 < ‖a‖) (hb : ‖b‖ ≤ 1) (hk₂ : ‖k₂‖ ≤ 1) (hk₁ : ‖k₁‖ ≤ 1) (hk₀ : ‖k₀‖ ≤ 1)
    (hA : A ^ 2 = 4 * a ^ 3 + k₂ * a ^ 2 + k₁ * a + k₀)
    (hB : B ^ 2 = 4 * b ^ 3 + k₂ * b ^ 2 + k₁ * b + k₀)
    (hX : 4 * (a - b) ^ 2 * X = (A - B) ^ 2 - (4 * (a + b) + k₂) * (a - b) ^ 2) : ‖X‖ ≤ 1 := by
  set ρ := ‖a‖ with hρ
  have haa : ‖a‖ ≤ ρ := le_rfl
  have hab : ‖a - b‖ = ρ := by
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; linarith),
      norm_neg, max_eq_left (by linarith)]
  have hA' : ‖A‖ * ‖A‖ ≤ ρ * ρ * ρ := by
    rw [← norm_mul, show A * A = 2 * 2 * (a * a * a) + k₂ * (a * a) + k₁ * a + k₀ by
      linear_combination hA]
    exact cubic_le h2 ha.le haa hk₂ hk₁ hk₀
  have hB' : ‖B‖ * ‖B‖ ≤ 1 * 1 * 1 := by
    rw [← norm_mul, show B * B = 2 * 2 * (b * b * b) + k₂ * (b * b) + k₁ * b + k₀ by
      linear_combination hB]
    exact cubic_le h2 le_rfl hb hk₂ hk₁ hk₀
  have h1 : 1 ≤ ρ * ρ := by nlinarith
  have hρρ : ρ ≤ ρ * ρ := by nlinarith
  have hA1 : ‖A‖ ≤ ρ * ρ := by
    exact le_of_mul_self_le_mul_self' (hA'.trans (by nlinarith)) (by linarith)
  have hB1 : ‖B‖ ≤ 1 := by
    exact le_of_mul_self_le_mul_self' (hB'.trans (by norm_num)) (by linarith)
  have hN : 2 * 2 * ((a - b) * (a - b)) * X =
      2 * 2 * b * (a * (a + b)) + 2 * k₂ * b * a + k₁ * (a + b) + 2 * k₀ + 2 * B * (-A) := by
    linear_combination hX + hA + hB
  have hs : ‖a + b‖ ≤ ρ := ultra_add_le haa (by linarith)
  have hn : ‖2 * 2 * b * (a * (a + b)) + 2 * k₂ * b * a + k₁ * (a + b) + 2 * k₀ + 2 * B * (-A)‖
      ≤ ρ * ρ := by
    refine ultra_add_le (ultra_add_le (ultra_add_le (ultra_add_le ?_ ?_) ?_) ?_) ?_
    · simpa using mul_le_of (mul_le_of (mul_le_of h2.le h2.le) hb) (mul_le_of haa hs)
    · exact (mul_le_of (mul_le_of (mul_le_of h2.le hk₂) hb) haa).trans (by linarith)
    · exact (mul_le_of hk₁ hs).trans (by linarith)
    · exact (mul_le_of h2.le hk₀).trans (by linarith)
    · exact (mul_le_of (mul_le_of h2.le hB1) ((norm_neg A).le.trans hA1)).trans (by linarith)
  rw [← hN, norm_mul, norm_mul, norm_mul, norm_mul, h2, hab] at hn
  by_contra hc
  push_neg at hc
  nlinarith
end GlobalTheory.Klein
