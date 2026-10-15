-- Prove2me | solution 1 for OAI.ThorpCompatibility.clump_subset_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:52:12.295979+00:00
-- url     : https://prove2.me/submissions/6ab599da-637b-44d5-802b-f43e372ddce0

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/BinomialBounds.lean:L97-L112
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.clump_subset_sum. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
import Definitions.Def_OAI_Probability_ThorpCompatibility_RankLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Model
import Definitions.Def_OAI_Probability_ThorpCompatibility_EntropyChain
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridExposure
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpCost
import Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability
import Definitions.Def_OAI_Probability_ThorpCompatibility_ListIncidence
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpMoments

-- ---- from OAI.Probability.ThorpCompatibility.BinomialBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
open Finset
lemma sum_finset_card {α : Type*} [Fintype α] (f : ℕ → ℝ) :
    (∑ s : Finset α, f s.card) =
      ∑ h ∈ Finset.range (Fintype.card α + 1), (Nat.choose (Fintype.card α) h : ℝ) * f h := by
  have hmap : ∀ s ∈ (Finset.univ : Finset (Finset α)),
      s.card ∈ Finset.range (Fintype.card α + 1) := by
    intro s _
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ s))
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun s => f s.card)]
  apply Finset.sum_congr rfl
  intro h _
  have hfilter : Finset.univ.filter (fun s : Finset α => s.card = h) =
      Finset.powersetCard h (Finset.univ : Finset α) := by
    ext s
    simp [Finset.mem_powersetCard]
  calc
    _ = ∑ s ∈ Finset.univ.filter (fun s : Finset α => s.card = h), f h := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [(Finset.mem_filter.mp hs).2]
    _ = _ := by simp [hfilter, Finset.card_powersetCard]

lemma clumpWeight_eq_card {α : Type*} (H z : ℝ) (s : Finset α) :
    clumpWeight H z s =
      if s.card = 0 then 1 else if H < s.card then Real.exp (z * s.card) else 0 := by
  by_cases hs : s = ∅
  · simp [hs, clumpWeight]
  · have hc : s.card ≠ 0 := fun h => hs (Finset.card_eq_zero.mp h)
    simp [clumpWeight, hs, hc]

lemma clump_subset_sum {α : Type*} [Fintype α] (H z ρ : ℝ) :
    (∑ s : Finset α, clumpWeight H z s * ρ ^ s.card) =
      ∑ h ∈ Finset.range (Fintype.card α + 1),
        if h = 0 then 1 else if H < h then
          (Nat.choose (Fintype.card α) h : ℝ) * (Real.exp z * ρ) ^ h else 0 := by
  simp_rw [clumpWeight_eq_card]
  rw [sum_finset_card (α := α) (fun h =>
    (if h = 0 then (1 : ℝ) else if H < h then Real.exp (z * h) else 0) * ρ ^ h)]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hz : h = 0
  · simp [hz]
  · by_cases hh : H < h
    · simp only [ite_eq_right hz, ite_eq_left hh]
      rw [mul_comm z (h : ℝ), Real.exp_nat_mul, mul_pow]
    · simp [hz, hh]

end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset
open Finset

theorem solution {α : Type*} [Fintype α] (H z ρ : ℝ) :
    (∑ s : Finset α, clumpWeight H z s * ρ ^ s.card) =
      ∑ h ∈ Finset.range (Fintype.card α + 1),
        if h = 0 then 1 else if H < h then
          (Nat.choose (Fintype.card α) h : ℝ) * (Real.exp z * ρ) ^ h else 0 := by
  first
    | exact OAI.ThorpCompatibility.clump_subset_sum H z ρ
    | exact OAI.ThorpCompatibility.clump_subset_sum
    | (apply OAI.ThorpCompatibility.clump_subset_sum <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.clump_subset_sum <;> assumption)
