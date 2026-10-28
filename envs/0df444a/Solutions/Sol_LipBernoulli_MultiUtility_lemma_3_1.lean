-- Prove2me | solution 1 for LipBernoulli.MultiUtility.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:39:44.363643+00:00
-- url     : https://prove2.me/submissions/f65fe6a8-925c-4cf8-ad54-4bddf7d493ba

import Mathlib
import Definitions.Def_LipBernoulli_MultiUtility_Setting

open MeasureTheory
open scoped ENNReal NNReal

namespace Aux_LBMU31

open LipBernoulli.MultiUtility

lemma mix_zero {X : Type*} [MeasurableSpace X] (p q : Measure X) : mix 0 p q = p := by
  simp [mix]

lemma mix_one {X : Type*} [MeasurableSpace X] (p q : Measure X) : mix 1 p q = q := by
  simp [mix]

lemma mix_swap {X : Type*} [MeasurableSpace X] (t : ℝ) (r a : Measure X) :
    mix t r a = mix (1 - t) a r := by
  simp only [mix, sub_sub_cancel]
  rw [add_comm]

end Aux_LBMU31

open LipBernoulli.MultiUtility Aux_LBMU31 in
theorem solution {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (S : Set (Measure X)) (hS : ∀ p ∈ S, IsProbabilityMeasure p) (hconv : IsConvexSet S)
    (hne : S.Nonempty) (R : Measure X → Measure X → Prop) (hpre : IsPreorderOn S R)
    (hwa : IsWeaklyAffine S R) :
    ∀ p ∈ S, ∀ p' ∈ S, ∀ q ∈ S, ∀ q' ∈ S, ∀ r ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (R p q → R (mix t r p) (mix t r q)) ∧
      (R p q → R p' q' → R (mix t p p') (mix t q q')) := by
  have P1 : ∀ a ∈ S, ∀ b ∈ S, ∀ r ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → R a b →
      R (mix t r a) (mix t r b) := by
    intro a ha b hb r hr t ht0 ht1 hab
    rcases eq_or_lt_of_le ht0 with h | h
    · subst h
      rw [mix_zero, mix_zero]
      exact hpre.1 r hr
    · rw [mix_swap t r a, mix_swap t r b]
      exact hwa a ha b hb r hr (1 - t) (by linarith) (by linarith) hab
  intro p hp p' hp' q hq q' hq' r hr t ht0 ht1
  refine ⟨P1 p hp q hq r hr t ht0 ht1, fun hpq hpq' => ?_⟩
  rcases eq_or_lt_of_le ht1 with h | h
  · subst h
    rw [mix_one, mix_one]
    exact hpq'
  · have h1 : R (mix t p p') (mix t q p') := hwa p hp q hq p' hp' t ht0 h hpq
    have h2 : R (mix t q p') (mix t q q') := P1 p' hp' q' hq' q hq t ht0 ht1 hpq'
    exact hpre.2 _ (hconv p hp p' hp' t ht0 ht1) _ (hconv q hq p' hp' t ht0 ht1) _
      (hconv q hq q' hq' t ht0 ht1) h1 h2
