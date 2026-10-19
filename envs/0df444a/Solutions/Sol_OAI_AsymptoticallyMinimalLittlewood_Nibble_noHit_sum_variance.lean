-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Nibble.noHit_sum_variance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:40:08.043808+00:00
-- url     : https://prove2.me/submissions/1ecc9e37-ede0-46c2-b4b2-f4d6ed3a5a1e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/ProductProbability.lean:L157-L214
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Nibble.noHit_sum_variance. The node keeps its source
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

lemma expectation_prod (p : ℝ) (g : E → Bool → ℝ) :
    expectation p (fun s ↦ ∏ e, g e (s e)) =
      ∏ e, (p * g e true + (1 - p) * g e false) := by
  dsimp [expectation, coinWeight]
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun e b ↦ (if b then p else 1 - p) * g e b)]
  simp

lemma coinWeight_sum (p : ℝ) : (∑ s : E → Bool, coinWeight p s) = 1 := by
  have h := expectation_prod (E := E) p (fun _ _ ↦ 1)
  simpa [expectation] using h

lemma expectation_const (p c : ℝ) : expectation (E := E) p (fun _ ↦ c) = c := by
  simp only [expectation, ← Finset.sum_mul, coinWeight_sum, one_mul]

lemma expectation_add (p : ℝ) (f g : (E → Bool) → ℝ) :
    expectation p (fun s ↦ f s + g s) = expectation p f + expectation p g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

lemma expectation_sub (p : ℝ) (f g : (E → Bool) → ℝ) :
    expectation p (fun s ↦ f s - g s) = expectation p f - expectation p g := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

lemma expectation_mul_const (p : ℝ) (f : (E → Bool) → ℝ) (c : ℝ) :
    expectation p (fun s ↦ f s * c) = expectation p f * c := by
  simp [expectation, ← mul_assoc, Finset.sum_mul]

lemma expectation_const_mul (p c : ℝ) (f : (E → Bool) → ℝ) :
    expectation p (fun s ↦ c * f s) = c * expectation p f := by
  simpa only [mul_comm c] using expectation_mul_const p f c

lemma expectation_sum {I : Type uI} (p : ℝ) (S : Finset I) (f : I → (E → Bool) → ℝ) :
    expectation p (fun s ↦ ∑ i ∈ S, f i s) = ∑ i ∈ S, expectation p (f i) := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

lemma noHit_eq (A : Finset E) (s : E → Bool) :
    noHit A s = if ∀ e ∈ A, s e = false then 1 else 0 := by
  dsimp [noHit]
  split_ifs with h
  · apply Finset.prod_eq_one
    intro e he
    simp [h e he]
  · push Not at h
    obtain ⟨e, he, hs⟩ := h
    apply Finset.prod_eq_zero he
    cases hh : s e <;> simp_all

lemma noHit_union (A B : Finset E) (s : E → Bool) :
    noHit (A ∪ B) s = noHit A s * noHit B s := by
  simp only [noHit_eq, Finset.mem_union, or_imp, forall_and]
  split_ifs <;> simp_all

lemma one_sub_pow_le {p : ℝ} (_hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    1 - (1 - p) ^ n ≤ n * p := by
  have h := one_add_mul_le_pow (by linarith : -2 ≤ -p) n
  simp only [← sub_eq_add_neg] at h
  linarith

lemma noHit_covariance_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (A B : Finset E) :
    expectation p (fun s ↦ noHit A s * noHit B s) -
      expectation p (noHit A) * expectation p (noHit B) ≤ p * (A ∩ B).card := by
  simp_rw [← noHit_union, expectation_noHit]
  rw [← pow_add]
  have hc := Finset.card_union_add_card_inter A B
  rw [← hc, pow_add]
  have hq : 0 ≤ 1 - p := by linarith
  have hq1 : 1 - p ≤ 1 := by linarith
  have hpow : (1 - p) ^ (A ∪ B).card ≤ 1 := pow_le_one₀ hq hq1
  have hdec : 0 ≤ 1 - (1 - p) ^ (A ∩ B).card := by
    linarith [pow_le_one₀ hq hq1 (n := (A ∩ B).card)]
  have hmul := mul_le_mul_of_nonneg_right hpow hdec
  have hh := one_sub_pow_le hp hp1 (A ∩ B).card
  nlinarith

/-- The second-moment estimate used for every residual degree. Each test set
has size at most L and each independent edge-bit occurs in at most K tests. -/
lemma noHit_sum_variance {I : Type uI} [DecidableEq I] {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset I) (A : I → Finset E)
    {K L : ℝ} (hK0 : 0 ≤ K) (hL : ∀ i ∈ S, ((A i).card : ℝ) ≤ L)
    (hK : ∀ e, ((S.filter fun i ↦ e ∈ A i).card : ℝ) ≤ K) :
    let Y : (E → Bool) → ℝ := fun s ↦ ∑ i ∈ S, noHit (A i) s
    expectation p (fun s ↦ (Y s - expectation p Y) ^ 2) ≤
      p * S.card * L * K := by
  classical
  dsimp only
  let Y : (E → Bool) → ℝ := fun s ↦ ∑ i ∈ S, noHit (A i) s
  change expectation p (fun s ↦ (Y s - expectation p Y) ^ 2) ≤ _
  have hid : expectation p (fun s ↦ (Y s - expectation p Y) ^ 2) =
      expectation p (fun s ↦ Y s ^ 2) - expectation p Y ^ 2 := by
    simp_rw [sub_sq]
    rw [expectation_add, expectation_sub, expectation_const,
      expectation_mul_const, expectation_const_mul]
    ring
  rw [hid]
  have hsq (s : E → Bool) : Y s ^ 2 = ∑ i ∈ S, ∑ j ∈ S, noHit (A i) s * noHit (A j) s := by
    dsimp [Y]
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  simp_rw [hsq, expectation_sum]
  have hmean : expectation p Y ^ 2 =
      ∑ i ∈ S, ∑ j ∈ S, expectation p (noHit (A i)) * expectation p (noHit (A j)) := by
    dsimp [Y]
    rw [expectation_sum, pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  rw [hmean, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, p * ((A i ∩ A j).card : ℝ) :=
      Finset.sum_le_sum fun i hi ↦ Finset.sum_le_sum fun j hj ↦ noHit_covariance_le hp hp1 _ _
    _ ≤ ∑ i ∈ S, p * (L * K) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ hp
      have hid' : (∑ j ∈ S, (A i ∩ A j).card) =
          ∑ e ∈ A i, (S.filter fun j ↦ e ∈ A j).card := by
        simp only [← Finset.filter_mem_eq_inter, Finset.card_eq_sum_ones, Finset.sum_filter]
        rw [Finset.sum_comm]
      have hb : (∑ j ∈ S, ((A i ∩ A j).card : ℝ)) ≤ L * K := by
        have hcast : (∑ j ∈ S, ((A i ∩ A j).card : ℝ)) =
            ∑ e ∈ A i, ((S.filter fun j ↦ e ∈ A j).card : ℝ) := by exact_mod_cast hid'
        rw [hcast]
        calc
          _ ≤ ∑ _e ∈ A i, K := Finset.sum_le_sum fun e _ ↦ hK e
          _ = (A i).card * K := by simp
          _ ≤ _ := mul_le_mul_of_nonneg_right (hL i hi) hK0
      exact hb
    _ = _ := by simp; ring

end ProductSpace

end Nibble
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Nibble
open scoped BigOperators
open Finset


theorem solution.{uE,uI} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Nibble.noHit_sum_variance.{uE,uI} := @_root_.OAI.AsymptoticallyMinimalLittlewood.Nibble.noHit_sum_variance.{uE,uI}
