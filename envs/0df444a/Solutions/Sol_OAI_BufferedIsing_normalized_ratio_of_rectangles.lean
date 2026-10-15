-- Prove2me | solution 1 for OAI.BufferedIsing.normalized_ratio_of_rectangles
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:38:23.56264+00:00
-- url     : https://prove2.me/submissions/5782ff4d-d254-41c5-ba2f-f71477a48cb3

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/Marginals.lean:L104-L145
-- (upload_full_project.md Phase 4): solution for node OAI.BufferedIsing.normalized_ratio_of_rectangles. The node keeps its source
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

/-- A general normalization lemma. Rectangle control on unnormalized positive
weights bounds the ACTUAL normalized pointwise ratio, not merely its odds. -/
lemma normalized_ratio_of_rectangles {A B : Type*} [Fintype A]
    (p : A → B → ℝ) (hp : ∀ a b, 0 < p a b) (L : ℝ)
    (hrect : ∀ a a' b b',
      |Real.log (p a b) + Real.log (p a' b') - Real.log (p a b') -
        Real.log (p a' b)| ≤ L) (a : A) (b b' : B) :
    Real.exp (-L) ≤ (p a b / ∑ x, p x b) / (p a b' / ∑ x, p x b') ∧
      (p a b / ∑ x, p x b) / (p a b' / ∑ x, p x b') ≤ Real.exp L := by
  classical
  have : Nonempty A := ⟨a⟩
  have hsum : ∀ c, 0 < ∑ x, p x c := fun c =>
    Finset.sum_pos (fun x _ => hp x c) Finset.univ_nonempty
  have hu : p a b * (∑ x, p x b') ≤ (Real.exp L * p a b') * ∑ x, p x b := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    have H := (abs_le.mp (hrect a x b b')).2
    have H' : Real.log (p a b) + Real.log (p x b') ≤
        L + Real.log (p a b') + Real.log (p x b) := by linarith
    have H'' := Real.exp_le_exp.mpr H'
    simpa only [Real.exp_add, Real.exp_log (hp a b), Real.exp_log (hp x b'),
      Real.exp_log (hp a b'), Real.exp_log (hp x b)] using H''
  have hl : (Real.exp (-L) * p a b') * (∑ x, p x b) ≤ p a b * ∑ x, p x b' := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    have H := (abs_le.mp (hrect a x b b')).1
    have H' : -L + Real.log (p a b') + Real.log (p x b) ≤
        Real.log (p a b) + Real.log (p x b') := by linarith
    have H'' := Real.exp_le_exp.mpr H'
    simpa only [Real.exp_add, Real.exp_log (hp a b), Real.exp_log (hp x b'),
      Real.exp_log (hp a b'), Real.exp_log (hp x b)] using H''
  have heq : (p a b / ∑ x, p x b) / (p a b' / ∑ x, p x b') =
      (p a b * ∑ x, p x b') / (p a b' * ∑ x, p x b) := by
    field_simp
  rw [heq]
  constructor
  · apply (le_div_iff₀ (mul_pos (hp a b') (hsum b))).mpr
    simpa only [mul_assoc] using hl
  · apply (div_le_iff₀ (mul_pos (hp a b') (hsum b))).mpr
    simpa only [mul_assoc] using hu

end BufferedIsing

end OAI

-- ---- platform node ----
open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem solution {A B : Type*} [Fintype A]
    (p : A → B → ℝ) (hp : ∀ a b, 0 < p a b) (L : ℝ)
    (hrect : ∀ a a' b b',
      |Real.log (p a b) + Real.log (p a' b') - Real.log (p a b') -
        Real.log (p a' b)| ≤ L) (a : A) (b b' : B) :
    Real.exp (-L) ≤ (p a b / ∑ x, p x b) / (p a b' / ∑ x, p x b') ∧
      (p a b / ∑ x, p x b) / (p a b' / ∑ x, p x b') ≤ Real.exp L := by
  first
    | exact OAI.BufferedIsing.normalized_ratio_of_rectangles p hp L hrect a b b'
    | exact OAI.BufferedIsing.normalized_ratio_of_rectangles
    | (apply OAI.BufferedIsing.normalized_ratio_of_rectangles <;> assumption)
    | (intros; apply OAI.BufferedIsing.normalized_ratio_of_rectangles <;> assumption)
