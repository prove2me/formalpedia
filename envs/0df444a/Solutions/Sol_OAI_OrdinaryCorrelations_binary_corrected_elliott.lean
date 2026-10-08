-- Prove2me | solution 1 for OAI.OrdinaryCorrelations.binary_corrected_elliott
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T04:04:04.653989+00:00
-- url     : https://prove2.me/submissions/731dad9f-ac27-4a0f-b32d-31e9224529ff

import Mathlib
import Definitions.Def_OrdinaryElliott
import Theorems.Thm_OAI_OrdinaryTwoPointCorrelations_binary_corrected_elliott

/-!
`OAI.OrdinaryCorrelations.binary_corrected_elliott` (OpenAI's `OrdinaryElliott` comparator) from the
published `OAI.OrdinaryTwoPointCorrelations.binary_corrected_elliott`. The two comparators state the
same theorem with different conventions: here `OneBounded` asks `‖f n‖ ≤ 1` for every `n`, and
uniform nonpretentiousness says the infimum of the distance over `|t| ≤ N` tends to infinity.
-/

open Filter

namespace OAIChowlaBridge

theorem filter_prime_eq (N : ℕ) :
    (Finset.Icc 2 ⌊(N : ℝ)⌋₊).filter Nat.Prime = OAI.TwoPointCorrelations.primesUpTo N := by
  ext p
  simp only [OAI.TwoPointCorrelations.primesUpTo, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_range, Nat.floor_natCast]
  constructor
  · rintro ⟨⟨_, h⟩, hp⟩; exact ⟨by omega, hp⟩
  · rintro ⟨h, hp⟩; exact ⟨⟨hp.two_le, by omega⟩, hp⟩

theorem distanceSq_eq (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (N : ℕ) :
    OAI.OrdinaryCorrelations.distanceSq f χ t (N : ℝ) =
      OAI.TwoPointCorrelations.squaredDistance f (OAI.TwoPointCorrelations.characterTwist χ t) N := by
  unfold OAI.OrdinaryCorrelations.distanceSq OAI.TwoPointCorrelations.squaredDistance
  rw [filter_prime_eq]
  rfl

theorem uniformlyNonpretentious_transfer (f : ℕ → ℂ)
    (h : OAI.OrdinaryCorrelations.UniformlyNonpretentious f) :
    OAI.TwoPointCorrelations.UniformlyNonpretentious f := by
  intro q hq χ K
  filter_upwards [(h q hq χ).eventually (eventually_ge_atTop (Real.sqrt (max K 0) + 1))]
    with N hN t ht
  have ht' := abs_le.mp ht
  have hmem : OAI.OrdinaryCorrelations.distance f χ t (N : ℝ) ∈
      (fun s : ℝ => OAI.OrdinaryCorrelations.distance f χ s (N : ℝ)) ''
        Set.Icc (-(N : ℝ)) (N : ℝ) := ⟨t, ⟨ht'.1, ht'.2⟩, rfl⟩
  have hbdd : BddBelow ((fun s : ℝ => OAI.OrdinaryCorrelations.distance f χ s (N : ℝ)) ''
      Set.Icc (-(N : ℝ)) (N : ℝ)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨s, _, rfl⟩
    exact Real.sqrt_nonneg _
  have h1 := le_trans hN (csInf_le hbdd hmem)
  unfold OAI.OrdinaryCorrelations.distance at h1
  rw [distanceSq_eq] at h1
  set D := OAI.TwoPointCorrelations.squaredDistance f
    (OAI.TwoPointCorrelations.characterTwist χ t) N
  have hpos : 0 < Real.sqrt D := by
    have := Real.sqrt_nonneg (max K 0); linarith
  have hD : 0 ≤ D := le_of_lt (Real.sqrt_pos.mp hpos)
  have h2 : Real.sqrt (max K 0) ≤ Real.sqrt D := by linarith
  rw [Real.sqrt_le_sqrt_iff hD] at h2
  exact le_trans (le_max_left K 0) h2

end OAIChowlaBridge

theorem solution
    (f₁ f₂ : ℕ → ℂ) (hf₁ : OAI.OrdinaryCorrelations.OneBounded f₁)
    (hf₂ : OAI.OrdinaryCorrelations.OneBounded f₂)
    (hm₁ : OAI.OrdinaryCorrelations.Multiplicative f₁)
    (hm₂ : OAI.OrdinaryCorrelations.Multiplicative f₂)
    (hNP : OAI.OrdinaryCorrelations.UniformlyNonpretentious f₁ ∨
      OAI.OrdinaryCorrelations.UniformlyNonpretentious f₂)
    (h₁ h₂ : ℕ) (hne : h₁ ≠ h₂) :
    Tendsto (OAI.OrdinaryCorrelations.shiftAverage f₁ f₂ h₁ h₂) atTop (nhds 0) := by
  have key := OAI.OrdinaryTwoPointCorrelations.binary_corrected_elliott f₁ f₂ hm₁ hm₂
    (fun n _ => hf₁ n) (fun n _ => hf₂ n)
    (hNP.imp (OAIChowlaBridge.uniformlyNonpretentious_transfer f₁)
      (OAIChowlaBridge.uniformlyNonpretentious_transfer f₂)) h₁ h₂ hne
  refine key.congr (fun N => ?_)
  simp only [OAI.OrdinaryCorrelations.shiftAverage, OAI.TwoPointCorrelations.correlationSum,
    div_eq_inv_mul]
