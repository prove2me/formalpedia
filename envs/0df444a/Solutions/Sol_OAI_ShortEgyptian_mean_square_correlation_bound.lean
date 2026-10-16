-- Prove2me | solution 1 for OAI.ShortEgyptian.mean_square_correlation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:36:39.153831+00:00
-- url     : https://prove2.me/submissions/29b38700-a7cc-4ca8-9632-6f785590d61f

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/HammingDistance.lean:L87-L119
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.mean_square_correlation_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance

-- ---- from OAI.NumberTheory.ShortEgyptian.PrimeProducts ----
namespace OAI

universe uJ uA uB uE uK

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

lemma expect_prod_pi {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A] (f : J → A → ℝ) :
    (𝔼 x : J → A, ∏ j, f j (x j)) = ∏ j, 𝔼 a : A, f j a := by
  simp only [Fintype.expect_eq_sum_div_card,prod_div_distrib,prod_const,card_univ,
    Fintype.card_fun,Nat.cast_pow]
  congr 1
  simpa using (prod_univ_sum (fun _ : J => (univ : Finset A)) f).symm

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.HammingDistance ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uJ uA

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

lemma hamming_weight {J : Type uJ} [Fintype J] (I K : J → Bool) :
    (1/2:ℝ)^hammingDistance I K = ∏ j, if I j = K j then (1:ℝ) else 1/2 := by
  rw [prod_ite]
  simp only [prod_const_one,one_mul,prod_const,hammingDistance]

lemma hamming_moment {J : Type uJ} [Fintype J] (I : J → Bool) :
    (𝔼 K : J → Bool, (1/2:ℝ)^hammingDistance I K) = (3/4:ℝ)^Fintype.card J := by
  simp_rw [hamming_weight]
  rw [expect_prod_pi (fun j x => if I j = x then (1:ℝ) else 1/2)]
  have hh (j : J) : (𝔼 x : Bool, if I j = x then (1:ℝ) else 1/2) = 3/4 := by
    cases I j <;> norm_num [Finset.expect_eq_sum_div_card]
  simp only [hh,prod_const,card_univ]

lemma hamming_tail {J : Type uJ} [Fintype J] (I : J → Bool) (k : ℕ) :
    (𝔼 K : J → Bool, if hammingDistance I K < k then (1:ℝ) else 0) ≤
      (2:ℝ)^k*(3/4:ℝ)^Fintype.card J := by
  have hpoint (K : J → Bool) : (if hammingDistance I K < k then (1:ℝ) else 0) ≤
      (2:ℝ)^k*(1/2:ℝ)^hammingDistance I K := by
    split_ifs with h
    · have hp : (1/2:ℝ)^k ≤ (1/2:ℝ)^hammingDistance I K :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) h.le
      have hh := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (2:ℝ)^k)
      have heq : (2:ℝ)^k*(1/2:ℝ)^k = 1 := by rw [← mul_pow]; norm_num
      rwa [heq] at hh
    · positivity
  calc
    _ ≤ 𝔼 K : J → Bool, (2:ℝ)^k*(1/2:ℝ)^hammingDistance I K := expect_le_expect (fun K _ => hpoint K)
    _ = _ := by rw [← mul_expect,hamming_moment]

lemma complex_expect_re {A : Type uA} [Fintype A] (f : A → ℂ) :
    (𝔼 a, f a).re = 𝔼 a, (f a).re := by
  simp only [Fintype.expect_eq_sum_div_card,Complex.div_re,Complex.re_sum,Complex.natCast_re,
    Complex.natCast_im,mul_zero,sum_div,Complex.normSq_natCast]
  by_cases hc : Fintype.card A = 0
  · simp [hc]
  · have hcR : (Fintype.card A:ℝ) ≠ 0 := by exact_mod_cast hc
    apply sum_congr rfl
    intro a _
    field_simp
    ring

lemma complex_expect_norm_sq {A : Type uA} [Fintype A] (f : A → ℂ) :
    ‖𝔼 a, f a‖^2 = 𝔼 a, 𝔼 b, (f a*(starRingEnd ℂ) (f b)).re := by
  have hh : ‖∑ a, f a‖^2 = ∑ a, ∑ b, (f a*(starRingEnd ℂ) (f b)).re := by
    rw [← Complex.normSq_eq_norm_sq,← Complex.ofReal_re (Complex.normSq _),← Complex.mul_conj]
    simp only [map_sum,sum_mul,mul_sum,Complex.re_sum]
    exact sum_comm
  simp only [Fintype.expect_eq_sum_div_card,norm_div,Complex.norm_natCast,div_pow,hh,← sum_div]
  ring

lemma mean_square_correlation_bound {A : Type uA} {J : Type uJ} [Fintype A] [Nonempty A] [Fintype J]
    (F : (J → Bool) → A → ℂ) (hnorm : ∀ I a, ‖F I a‖ ≤ 1)
    (k : ℕ) (epsilon : ℝ) (heps : 0 ≤ epsilon)
    (hcorr : ∀ I K, k ≤ hammingDistance I K →
      ‖𝔼 a, F I a*(starRingEnd ℂ) (F K a)‖ ≤ epsilon) :
    (𝔼 a, ‖𝔼 I : J → Bool, F I a‖^2) ≤
      (2:ℝ)^k*(3/4:ℝ)^Fintype.card J+epsilon := by
  have hpoint I K : (𝔼 a, (F I a*(starRingEnd ℂ) (F K a)).re) ≤
      (if hammingDistance I K < k then (1:ℝ) else 0)+epsilon := by
    rw [← complex_expect_re]
    apply (Complex.re_le_norm _).trans
    by_cases h : hammingDistance I K < k
    · rw [ite_eq_left h]
      apply ((RCLike.norm_expect_le (K := ℂ)).trans (expect_le univ_nonempty (fun a _ => ?_))).trans (by linarith : (1:ℝ)≤1+epsilon)
      rw [norm_mul,Complex.norm_conj]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hnorm I a)).trans (hnorm K a)
    · rw [ite_eq_right h,zero_add]
      exact hcorr I K (Nat.le_of_not_gt h)
  simp_rw [complex_expect_norm_sq]
  rw [expect_comm]
  calc
    _ = 𝔼 I : J → Bool, 𝔼 K : J → Bool, 𝔼 a, (F I a*(starRingEnd ℂ) (F K a)).re := by
      apply expect_congr rfl
      intro I _
      exact expect_comm _ _ _
    _ ≤ 𝔼 I : J → Bool, 𝔼 K : J → Bool,
      ((if hammingDistance I K < k then (1:ℝ) else 0)+epsilon) :=
      expect_le_expect (fun I _ => expect_le_expect (fun K _ => hpoint I K))
    _ ≤ _ := by
      apply expect_le univ_nonempty
      intro I _
      rw [expect_add_distrib,Fintype.expect_const]
      linarith [hamming_tail I k]

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution.{uJ,uA} : type_of% @_root_.OAI.ShortEgyptian.mean_square_correlation_bound.{uJ,uA} := @_root_.OAI.ShortEgyptian.mean_square_correlation_bound.{uJ,uA}
