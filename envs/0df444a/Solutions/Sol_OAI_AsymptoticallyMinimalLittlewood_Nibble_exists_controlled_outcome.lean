-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Nibble.exists_controlled_outcome
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:43:08.24771+00:00
-- url     : https://prove2.me/submissions/01b64a54-d4c2-4656-af14-96b2d5a8e5c1

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/ProductProbability.lean:L323-L364
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Nibble.exists_controlled_outcome. The node keeps its source
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

omit [DecidableEq E] in
lemma coinWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (s : E → Bool) :
    0 ≤ coinWeight p s := by
  apply Finset.prod_nonneg
  intro e he
  split_ifs <;> linarith

lemma expectation_const (p c : ℝ) : expectation (E := E) p (fun _ ↦ c) = c := by
  simp only [expectation, ← Finset.sum_mul, coinWeight_sum, one_mul]

lemma expectation_add (p : ℝ) (f g : (E → Bool) → ℝ) :
    expectation p (fun s ↦ f s + g s) = expectation p f + expectation p g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

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

lemma expectation_mono {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : (E → Bool) → ℝ} (h : ∀ s, f s ≤ g s) : expectation p f ≤ expectation p g := by
  exact Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left (h s) (coinWeight_nonneg hp hp1 s)

lemma exists_le_expectation {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (E → Bool) → ℝ) : ∃ s, f s ≤ expectation p f := by
  by_contra h
  push Not at h
  have hh : expectation (E := E) p (fun _ ↦ expectation p f) < expectation p f := by
    apply Finset.sum_lt_sum
    · intro s hs
      exact mul_le_mul_of_nonneg_left (h s).le (coinWeight_nonneg hp hp1 s)
    · have hex : ∃ s : E → Bool, 0 < coinWeight p s := by
        by_contra hn
        push Not at hn
        have hz : (∑ s : E → Bool, coinWeight p s) ≤ 0 := Finset.sum_nonpos fun s _ ↦ hn s
        rw [coinWeight_sum] at hz
        linarith
      obtain ⟨s, hs⟩ := hex
      exact ⟨s, Finset.mem_univ s, mul_lt_mul_of_pos_left (h s) hs⟩
  rw [expectation_const] at hh
  exact (lt_irrefl _ hh)

lemma markov_indicator {p t : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (_ht : 0 ≤ t)
    (f : (E → Bool) → ℝ) (hf : ∀ s, 0 ≤ f s) :
    t * expectation p (fun s ↦ if t < f s then 1 else 0) ≤ expectation p f := by
  rw [← expectation_const_mul]
  apply expectation_mono hp hp1
  intro s
  split_ifs with h <;> simp_all
  exact h.le

lemma chebyshev_indicator {p t : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (ht : 0 ≤ t)
    (f : (E → Bool) → ℝ) :
    t ^ 2 * expectation p (fun s ↦ if t < |f s - expectation p f| then 1 else 0) ≤
      expectation p (fun s ↦ (f s - expectation p f) ^ 2) := by
  rw [← expectation_const_mul]
  apply expectation_mono hp hp1
  intro s
  split_ifs with h
  · simp only [mul_one]
    nlinarith [sq_abs (f s - expectation p f)]
  · simp only [mul_zero]
    positivity

lemma exists_of_three_bad_bounds {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (P Q R : (E → Bool) → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R]
    (hP : expectation p (fun s ↦ if P s then 1 else 0) ≤ 1 / 4)
    (hQ : expectation p (fun s ↦ if Q s then 1 else 0) ≤ 1 / 4)
    (hR : expectation p (fun s ↦ if R s then 1 else 0) ≤ 1 / 4) :
    ∃ s, ¬ P s ∧ ¬ Q s ∧ ¬ R s := by
  obtain ⟨s, hs⟩ := exists_le_expectation hp hp1 (fun s ↦
    (if P s then (1 : ℝ) else 0) + (if Q s then 1 else 0) + (if R s then 1 else 0))
  rw [expectation_add, expectation_add] at hs
  refine ⟨s, ?_, ?_, ?_⟩ <;> intro h
  all_goals split_ifs at hs <;> linarith

/-- Simultaneous second-moment control of many local tests, one global test,
and a nonnegative collision count. No randomness remains in the conclusion. -/
lemma exists_controlled_outcome {I : Type uI} [DecidableEq I] {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (U : Finset I)
    (Y : I → (E → Bool) → ℝ) (Z W : (E → Bool) → ℝ)
    {V Vz M t b u c : ℝ} (ht : 0 < t) (hb : 0 < b) (hu : 0 < u) (hc : 0 < c)
    (hY : ∀ i ∈ U, expectation p (fun s ↦ (Y i s - expectation p (Y i))^2) ≤ V)
    (hZ : expectation p (fun s ↦ (Z s - expectation p Z)^2) ≤ Vz)
    (hW0 : ∀ s, 0 ≤ W s) (hW : expectation p W ≤ M)
    (hV : 4 * U.card * V ≤ t^2*b) (hVz : 4*Vz ≤ u^2) (hM : 4*M ≤ c) :
    ∃ s, (((U.filter fun i ↦ t < |Y i s - expectation p (Y i)|).card : ℝ) ≤ b) ∧
      |Z s - expectation p Z| ≤ u ∧ W s ≤ c := by
  classical
  let B : (E → Bool) → ℝ := fun s ↦
    ((U.filter fun i ↦ t < |Y i s - expectation p (Y i)|).card : ℝ)
  have hB0 (s : E → Bool) : 0 ≤ B s := Nat.cast_nonneg _
  have hB : t^2 * expectation p B ≤ U.card*V := by
    have heq : B = fun s ↦ ∑ i ∈ U, if t < |Y i s - expectation p (Y i)| then (1 : ℝ) else 0 := by
      funext s
      simp only [B, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
        Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [heq, expectation_sum, Finset.mul_sum]
    calc
      _ ≤ ∑ _i ∈ U, V := Finset.sum_le_sum fun i hi ↦
        (chebyshev_indicator hp hp1 ht.le (Y i)).trans (hY i hi)
      _ = _ := by simp
  have hP : expectation p (fun s ↦ if b < B s then 1 else 0) ≤ 1/4 := by
    have hm := markov_indicator hp hp1 hb.le B hB0
    have he := mul_le_mul_of_nonneg_left hm (sq_nonneg t)
    have hpos : 0 < t^2*b := mul_pos (sq_pos_of_pos ht) hb
    nlinarith
  have hQ : expectation p (fun s ↦ if u < |Z s - expectation p Z| then 1 else 0) ≤ 1/4 := by
    have hh := (chebyshev_indicator hp hp1 hu.le Z).trans hZ
    have hpos := sq_pos_of_pos hu
    nlinarith
  have hR : expectation p (fun s ↦ if c < W s then 1 else 0) ≤ 1/4 := by
    have hh := (markov_indicator hp hp1 hc.le W hW0).trans hW
    nlinarith
  obtain ⟨s, hsP, hsQ, hsR⟩ := exists_of_three_bad_bounds hp hp1
    (fun s ↦ b < B s) (fun s ↦ u < |Z s - expectation p Z|) (fun s ↦ c < W s)
    hP hQ hR
  exact ⟨s, le_of_not_gt hsP, le_of_not_gt hsQ, le_of_not_gt hsR⟩

end ProductSpace

end Nibble
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Nibble
open scoped BigOperators
open Finset


theorem solution.{uE,uI} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Nibble.exists_controlled_outcome.{uE,uI} := @_root_.OAI.AsymptoticallyMinimalLittlewood.Nibble.exists_controlled_outcome.{uE,uI}
