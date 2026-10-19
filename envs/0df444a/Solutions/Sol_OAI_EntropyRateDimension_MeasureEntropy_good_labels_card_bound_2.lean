-- Prove2me | solution 2 for OAI.EntropyRateDimension.MeasureEntropy.good_labels_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:04:00.041998+00:00
-- url     : https://prove2.me/submissions/6719a4a5-5ddc-40fb-bf2c-d674a6fee550

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/LocalEntropy.lean:L152-L180
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.MeasureEntropy.good_labels_card_bound. The node keeps its source
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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset

-- ---- from OAI.MeasureTheory.SelfSimilar.LocalEntropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension

namespace FiniteEntropy

end FiniteEntropy

namespace MeasureEntropy

theorem card_mul_mass_le_one {α : Type uα} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s : Finset α) (x : α → ℝ) {r q : ℝ}
    (hd : (↑s : Set α).PairwiseDisjoint (fun i => Metric.ball (x i) r))
    (hq : ∀ i ∈ s, q ≤ μ.real (Metric.ball (x i) r)) :
    (s.card : ℝ)*q ≤ 1 := by
  calc
    (s.card : ℝ)*q = ∑ i ∈ s, q := by simp
    _ ≤ ∑ i ∈ s, μ.real (Metric.ball (x i) r) := Finset.sum_le_sum hq
    _ = μ.real (⋃ i ∈ s, Metric.ball (x i) r) :=
      (measureReal_biUnion_finset hd (fun _ _ => measurableSet_ball)).symm
    _ ≤ 1 := (measureReal_mono (Set.subset_univ _)).trans_eq (by simp)

theorem label_ball_disjoint {s u x y : ℝ} (hs : 0 < s)
    (hne : label s u x ≠ label s u y) (hmod : label s u x % 3=label s u y % 3) :
    Disjoint (Metric.ball x (s/2)) (Metric.ball y (s/2)) := by
  have hd : s ≤ dist x y := by
    rw [Real.dist_eq]
    have hx1 := Int.floor_le (x/s+u)
    have hx2 := Int.lt_floor_add_one (x/s+u)
    have hy1 := Int.floor_le (y/s+u)
    have hy2 := Int.lt_floor_add_one (y/s+u)
    have hdiff : label s u x+3 ≤ label s u y ∨ label s u y+3 ≤ label s u x := by omega
    rcases hdiff with h | h
    · have h' : (label s u x : ℝ)+3 ≤ (label s u y : ℝ) := by exact_mod_cast h
      change (⌊x/s+u⌋ : ℝ)+3 ≤ (⌊y/s+u⌋ : ℝ) at h'
      have hxy : 2 < y/s-x/s := by linarith
      have hmul := (lt_div_iff₀ hs).mp (by simpa only [← sub_div] using hxy)
      rw [abs_of_nonpos (by linarith : x-y ≤ 0)]
      linarith
    · have h' : (label s u y : ℝ)+3 ≤ (label s u x : ℝ) := by exact_mod_cast h
      change (⌊y/s+u⌋ : ℝ)+3 ≤ (⌊x/s+u⌋ : ℝ) at h'
      have hxy : 2 < x/s-y/s := by linarith
      have hmul := (lt_div_iff₀ hs).mp (by simpa only [← sub_div] using hxy)
      rw [abs_of_nonneg (by linarith : 0 ≤ x-y)]
      linarith
  apply Set.disjoint_left.mpr
  intro z hz hzy
  have hz1 := Metric.mem_ball.mp hz
  have hz2 := Metric.mem_ball.mp hzy
  have ht := dist_triangle_left x y z
  linarith

theorem good_labels_card_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s u q : ℝ} (hs : 0 < s) (a : Finset ℤ) (x : ℤ → ℝ)
    (hx : ∀ i ∈ a, label s u (x i)=i)
    (hq : ∀ i ∈ a, q ≤ μ.real (Metric.ball (x i) (s/2))) :
    (a.card : ℝ)*q ≤ 3 := by
  let color : ℤ → Fin 3 := fun i => ⟨(i%3).toNat, by omega⟩
  have hc : ∀ c : Fin 3,
      (((a.filter (fun i => color i=c)).card : ℕ) : ℝ)*q ≤ 1 := by
    intro c
    apply card_mul_mass_le_one μ _ x
    · intro i hi j hj hij
      have hia := (Finset.mem_filter.mp hi).1
      have hja := (Finset.mem_filter.mp hj).1
      apply label_ball_disjoint hs
      · rwa [hx i hia,hx j hja]
      · rw [hx i hia,hx j hja]
        have he := congrArg Fin.val ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
        dsimp [color] at he
        omega
    · intro i hi
      exact hq i (Finset.mem_filter.mp hi).1
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun c _ => hc c)
  have he : ∑ c : Fin 3, (((a.filter (fun i => color i=c)).card : ℕ) : ℝ) = (a.card : ℝ) := by
    simp only [← Nat.cast_sum]
    congr 1
    simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using
      (Finset.sum_fiberwise a color (fun _ => (1 : ℕ)))
  rw [← Finset.sum_mul,he] at hsum
  simpa using hsum

end MeasureEntropy
end EntropyRateDimension

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.MeasureEntropy.good_labels_card_bound := @_root_.OAI.EntropyRateDimension.MeasureEntropy.good_labels_card_bound
