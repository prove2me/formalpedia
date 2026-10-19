-- Prove2me | solution 1 for OAI.EntropyRateDimension.RandomGrid.refinement_entropy_hit_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:45:41.476385+00:00
-- url     : https://prove2.me/submissions/776eaf87-e9bf-4f15-8f6f-585e4ea5566c

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/GridCoupling.lean:L239-L284
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.RandomGrid.refinement_entropy_hit_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Theorems.Thm_OAI_EntropyRateDimension_RandomGrid_refinement_entropy_bound

-- ---- from OAI.MeasureTheory.SelfSimilar.GridCoupling ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace RandomGrid

attribute [local instance] unitCircleProbability
theorem hit_nonneg (c : AddCircle (1 : ℝ)) (r : ℝ) (u : AddCircle (1 : ℝ)) :
    0 ≤ hit c r u := by unfold hit; split_ifs <;> norm_num

theorem refinement_entropy_hit_bound {α : Type uα} (s : Finset α) (p : α → ℝ)
    (k : ℕ) (hk : 1 ≤ k) (v : α → Fin k → ℝ) (m : Fin k → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (u : AddCircle (1 : ℝ))
    (hp : ∀ x ∈ s, 0 ≤ p x) (hp1 : ∑ x ∈ s, p x = 1)
    (hv : ∀ x ∈ s, ∀ i, |v x i-m i| ≤ 4*δ)
    (hind : ∀ a : ℝ, ∀ i j : Fin k, i ≠ j →
      (∑ x ∈ s, if a/(4*k) ≤ |v x i-m i| ∧ a/(4*k) ≤ |v x j-m j| then p x else 0) =
      (∑ x ∈ s, if a/(4*k) ≤ |v x i-m i| then p x else 0) *
      (∑ x ∈ s, if a/(4*k) ≤ |v x j-m j| then p x else 0)) :
    FiniteEntropy.conditionalEntropy s p (fun x i => cell δ u (v x i)) (fun x => ∑ i, v x i) ≤
      11*k*(∑ x ∈ s, p x * ∑ i, ∑ j,
        hit (-(m j/δ : ℝ) : AddCircle (1 : ℝ)) (4*k*|v x i-m i|/δ) u)*Real.log 2 := by
  classical
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  let d : Fin k → ℝ := fun i => dist u (-(m i/δ : ℝ) : AddCircle (1 : ℝ))
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0,by omega⟩,Finset.mem_univ _⟩
  obtain ⟨j₀, _, hj₀⟩ := Finset.exists_min_image Finset.univ d hne
  let a := δ*d j₀
  have ha : ∀ i, a ≤ δ*d i := fun i => mul_le_mul_of_nonneg_left (hj₀ i (Finset.mem_univ i)) hδ.le
  have h := refinement_entropy_bound s p k hk v m δ hδ u a ha hp hp1 hv (hind a)
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (11 : ℝ)*k)
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases he : a/(4*k) ≤ |v x i-m i|
  · rw [ite_eq_left he]
    have hdist : d j₀ ≤ 4*k*|v x i-m i|/δ := by
      apply (le_div_iff₀ hδ).mpr
      have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < 4*k)).mp he
      dsimp only [a] at hh
      nlinarith
    have hone : hit (-(m j₀/δ : ℝ) : AddCircle (1 : ℝ)) (4*k*|v x i-m i|/δ) u = 1 :=
      ite_eq_left hdist
    have hs : 1 ≤ ∑ j, hit (-(m j/δ : ℝ) : AddCircle (1 : ℝ)) (4*k*|v x i-m i|/δ) u := by
      have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Fin k))) (f := fun j =>
        hit (-(m j/δ : ℝ) : AddCircle (1 : ℝ)) (4*k*|v x i-m i|/δ) u)
        (fun j _ => hit_nonneg _ _ _) (Finset.mem_univ j₀)
      simpa only [hone] using hh
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hs (hp x hx)
  · rw [ite_eq_right he]
    exact mul_nonneg (hp x hx) (Finset.sum_nonneg (fun j _ => hit_nonneg _ _ _))

end RandomGrid

end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.RandomGrid
open scoped BigOperators ENNReal
open MeasureTheory
attribute [local instance] unitCircleProbability


theorem solution.{uα} : type_of% @_root_.OAI.EntropyRateDimension.RandomGrid.refinement_entropy_hit_bound.{uα} := @_root_.OAI.EntropyRateDimension.RandomGrid.refinement_entropy_hit_bound.{uα}
