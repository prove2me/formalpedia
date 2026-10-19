-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Nibble.noHit_mean_error
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:41:40.220226+00:00
-- url     : https://prove2.me/submissions/2d420b11-c83e-4676-a597-8531b8bfa4da

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/ProductProbability.lean:L262-L289
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Nibble.noHit_mean_error. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Nibble_expectation_noHit

-- ---- from OAI.Analysis.Littlewood.ProductProbability ----
namespace OAI

universe uE uI

namespace AsymptoticallyMinimalLittlewood
namespace Nibble
open scoped BigOperators
open Finset

section ProductSpace
variable {E : Type uE} [Fintype E] [DecidableEq E]

lemma expectation_sum {I : Type uI} (p : ℝ) (S : Finset I) (f : I → (E → Bool) → ℝ) :
    expectation p (fun s ↦ ∑ i ∈ S, f i s) = ∑ i ∈ S, expectation p (f i) := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

lemma one_sub_pow_le {p : ℝ} (_hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    1 - (1 - p) ^ n ≤ n * p := by
  have h := one_add_mul_le_pow (by linarith : -2 ≤ -p) n
  simp only [← sub_eq_add_neg] at h
  linarith

lemma pow_bonferroni {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (1 - p) ^ n - (1 - n * p) ≤ (n * p) ^ 2 / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hl := one_sub_pow_le hp hp1 n
    have hstep := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hp1)
    have he := mul_nonneg hp (sq_nonneg ((n : ℝ) * p))
    rw [pow_succ]
    push_cast
    nlinarith [sq_nonneg p]

lemma noHit_mean_error {I : Type uI} {p M B L : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hL : 0 ≤ L)
    (S : Finset I) (A : I → Finset E)
    (hcard : ∀ i ∈ S, |((A i).card : ℝ) - M| ≤ B)
    (hupper : ∀ i ∈ S, ((A i).card : ℝ) ≤ L) :
    |expectation p (fun s ↦ ∑ i ∈ S, noHit (A i) s) - S.card * (1 - p * M)| ≤
      S.card * (p * B + (p * L)^2 / 2) := by
  rw [expectation_sum]
  have hc : (S.card : ℝ) * (1 - p * M) = ∑ _i ∈ S, (1 - p * M) := by simp; ring
  rw [hc, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ S, |expectation p (noHit (A i)) - (1 - p * M)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ S, (p * B + (p * L)^2/2) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [expectation_noHit]
      have hbon := pow_bonferroni hp hp1 (A i).card
      have hlo := one_sub_pow_le hp hp1 (A i).card
      have herr := hcard i hi
      have hbound := hupper i hi
      have hpv : 0 ≤ ((A i).card : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
      have hpl : ((A i).card : ℝ) * p ≤ L * p := mul_le_mul_of_nonneg_right hbound hp
      have hsq : (((A i).card : ℝ) * p)^2 ≤ (L*p)^2 := sq_le_sq₀ hpv (mul_nonneg hL hp) |>.mpr hpl
      have hm := mul_le_mul_of_nonneg_left (abs_le.mp herr).1 hp
      have hM := mul_le_mul_of_nonneg_left (abs_le.mp herr).2 hp
      apply abs_le.mpr
      constructor <;> nlinarith [sq_nonneg (p*L)]
    _ = _ := by simp; ring

end ProductSpace

end Nibble
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Nibble
open scoped BigOperators
open Finset


theorem solution.{uE,uI} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Nibble.noHit_mean_error.{uE,uI} := @_root_.OAI.AsymptoticallyMinimalLittlewood.Nibble.noHit_mean_error.{uE,uI}
