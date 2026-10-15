-- Prove2me | solution 1 for OAI.BufferedIsing.mixture_ratio_of_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:39:52.485183+00:00
-- url     : https://prove2.me/submissions/36acc275-0103-4699-be09-31525376fdd0

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/Marginals.lean:L239-L275
-- (upload_full_project.md Phase 4): solution for node OAI.BufferedIsing.mixture_ratio_of_pointwise. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals

-- ---- from OAI.Probability.Ising.Marginals ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

lemma positive_average {B : Type*} [Fintype B] (p μ : B → ℝ)
    (hp : ∀ b, 0 < p b) (hμ : ∀ b, 0 ≤ μ b) (hμsum : ∑ b, μ b = 1) :
    0 < ∑ b, μ b * p b := by
  classical
  have hex : ∃ b, 0 < μ b := by
    by_contra hn
    push Not at hn
    have hz : ∀ b, μ b = 0 := fun b => le_antisymm (hn b) (hμ b)
    simp [hz] at hμsum
  obtain ⟨b, hb⟩ := hex
  exact lt_of_lt_of_le (mul_pos hb (hp b))
    (Finset.single_le_sum (fun c _ => mul_nonneg (hμ c) (hp c).le) (Finset.mem_univ b))

/-- Multiplicative pointwise control survives arbitrary mixtures on both
sides. The proof uses the original constants without a second loss. -/
lemma mixture_ratio_of_pointwise {B : Type*} [Fintype B]
    (p : B → ℝ) (hp : ∀ b, 0 < p b) (L U : ℝ)
    (hbound : ∀ b b', L ≤ p b / p b' ∧ p b / p b' ≤ U)
    (μ ν : B → ℝ) (hμ : ∀ b, 0 ≤ μ b) (hν : ∀ b, 0 ≤ ν b)
    (hμsum : ∑ b, μ b = 1) (hνsum : ∑ b, ν b = 1) :
    L ≤ (∑ b, μ b * p b) / (∑ b, ν b * p b) ∧
      (∑ b, μ b * p b) / (∑ b, ν b * p b) ≤ U := by
  have havg := positive_average p ν hp hν hνsum
  have honeL : ∀ b, L * (∑ c, ν c * p c) ≤ p b := by
    intro b
    calc
      L * (∑ c, ν c * p c) = ∑ c, ν c * (L * p c) := by
        simp only [Finset.mul_sum]; congr 1; ext c; ring
      _ ≤ ∑ c, ν c * p b := Finset.sum_le_sum fun c _ =>
        mul_le_mul_of_nonneg_left ((le_div_iff₀ (hp c)).mp (hbound b c).1) (hν c)
      _ = p b := by rw [← Finset.sum_mul, hνsum, one_mul]
  have honeU : ∀ b, p b ≤ U * (∑ c, ν c * p c) := by
    intro b
    calc
      p b = ∑ c, ν c * p b := by rw [← Finset.sum_mul, hνsum, one_mul]
      _ ≤ ∑ c, ν c * (U * p c) := Finset.sum_le_sum fun c _ =>
        mul_le_mul_of_nonneg_left ((div_le_iff₀ (hp c)).mp (hbound b c).2) (hν c)
      _ = U * (∑ c, ν c * p c) := by
        simp only [Finset.mul_sum]; congr 1; ext c; ring
  constructor
  · apply (le_div_iff₀ havg).mpr
    calc
      _ = ∑ b, μ b * (L * ∑ c, ν c * p c) := by
        rw [← Finset.sum_mul, hμsum, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (honeL b) (hμ b)
  · apply (div_le_iff₀ havg).mpr
    calc
      _ ≤ ∑ b, μ b * (U * ∑ c, ν c * p c) :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (honeU b) (hμ b)
      _ = _ := by rw [← Finset.sum_mul, hμsum, one_mul]

end BufferedIsing

end OAI

-- ---- platform node ----
open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem solution {B : Type*} [Fintype B]
    (p : B → ℝ) (hp : ∀ b, 0 < p b) (L U : ℝ)
    (hbound : ∀ b b', L ≤ p b / p b' ∧ p b / p b' ≤ U)
    (μ ν : B → ℝ) (hμ : ∀ b, 0 ≤ μ b) (hν : ∀ b, 0 ≤ ν b)
    (hμsum : ∑ b, μ b = 1) (hνsum : ∑ b, ν b = 1) :
    L ≤ (∑ b, μ b * p b) / (∑ b, ν b * p b) ∧
      (∑ b, μ b * p b) / (∑ b, ν b * p b) ≤ U := by
  first
    | exact OAI.BufferedIsing.mixture_ratio_of_pointwise p hp L U hbound μ ν hμ hν hμsum hνsum
    | exact OAI.BufferedIsing.mixture_ratio_of_pointwise
    | (apply OAI.BufferedIsing.mixture_ratio_of_pointwise <;> assumption)
    | (intros; apply OAI.BufferedIsing.mixture_ratio_of_pointwise <;> assumption)
