-- Prove2me | solution 1 for OAI.EntropyRateDimension.FairPairs.sum_refinementCost_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:26:37.049982+00:00
-- url     : https://prove2.me/submissions/1bf9793d-77bc-4464-a70d-0abc7e63e61b

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FairPairs
universe uβ
open scoped BigOperators ENNReal
open MeasureTheory
open FiniteEntropy
theorem h41n_geom_key {x ρ : ℝ} (hx : 0 < x) (hρ : 0 < ρ) (J : ℕ) :
    (∑ h ∈ Finset.range J, if x ≤ ρ/4^h then 2*x*4^h/ρ else 0) ≤
      if x ≤ 2*ρ then (8/3 : ℝ) else 0 := by
  classical
  rw [← Finset.sum_filter]
  set H := (Finset.range J).filter (fun h => x ≤ ρ/4^h) with hH
  rcases H.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty]
    split_ifs <;> norm_num
  · obtain ⟨h1, hh1⟩ := hne
    have hxρ : x ≤ ρ := by
      have := (Finset.mem_filter.mp hh1).2
      have h4 : ρ / 4^h1 ≤ ρ := div_le_self hρ.le (one_le_pow₀ (by norm_num))
      linarith
    rw [if_pos (by linarith)]
    set h0 := H.max' ⟨h1, hh1⟩
    have hh0 : h0 ∈ H := H.max'_mem _
    have hx0 : x * 4^h0 ≤ ρ := by
      have := (Finset.mem_filter.mp hh0).2
      rwa [le_div_iff₀ (by positivity)] at this
    have hsub : H ⊆ Finset.range (h0+1) := by
      intro h hh
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (H.le_max' h hh)
    calc ∑ h ∈ H, 2*x*4^h/ρ ≤ ∑ h ∈ Finset.range (h0+1), 2*x*4^h/ρ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun h _ _ => by positivity)
      _ = 2*x/ρ * ∑ h ∈ Finset.range (h0+1), (4:ℝ)^h := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro h _
          ring
      _ = 2*x/ρ * ((4^(h0+1) - 1)/3) := by
          rw [geom_sum_eq (by norm_num : (4:ℝ) ≠ 1)]
          norm_num
      _ ≤ 8/3 := by
          rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by norm_num)]
          rw [pow_succ]
          nlinarith [pow_pos (by norm_num : (0:ℝ) < 4) h0]

theorem solution (ν : Law) (k : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (J : ℕ) :
    (∑ h ∈ Finset.range J, ν.refinementCost k (ρ/4^h)) ≤
      60000*k^4*Real.log 2 * ∑ ℓ ∈ ν.bandSupport.filter (fun ℓ => (2 : ℝ)^(-ℓ) ≤ 2*ρ),
        capacity ν ℓ := by
  have hcap : ∀ ℓ, 0 ≤ capacity ν ℓ := fun ℓ =>
    Real.sSup_nonneg (fun t ⟨w, hw, ht⟩ => ht ▸ Finset.sum_nonneg (fun e _ => hw.1 e))
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hzp : ∀ ℓ : ℤ, (2:ℝ)^(1-ℓ) = 2 * (2:ℝ)^(-ℓ) := fun ℓ => by
    rw [sub_eq_add_neg, zpow_add₀ two_ne_zero, zpow_one]
  unfold Law.refinementCost Law.bandCost
  simp only [Finset.sum_filter]
  have hK : (0:ℝ) ≤ k^4 := by positivity
  calc (∑ h ∈ Finset.range J, 352 * (k:ℝ)^4 / (ρ/4^h) *
        (∑ ℓ ∈ ν.bandSupport, if (2:ℝ)^(-ℓ) ≤ ρ/4^h then (2:ℝ)^(1-ℓ) * capacity ν ℓ else 0) *
          Real.log 2)
      = ∑ ℓ ∈ ν.bandSupport, (352 * (k:ℝ)^4 * Real.log 2 * capacity ν ℓ) *
          ∑ h ∈ Finset.range J, (if (2:ℝ)^(-ℓ) ≤ ρ/4^h then 2*(2:ℝ)^(-ℓ)*4^h/ρ else 0) := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro ℓ _
        apply Finset.sum_congr rfl
        intro h _
        split_ifs
        · rw [hzp, div_div_eq_mul_div]
          ring
        · simp
    _ ≤ ∑ ℓ ∈ ν.bandSupport, (352 * (k:ℝ)^4 * Real.log 2 * capacity ν ℓ) *
          (if (2:ℝ)^(-ℓ) ≤ 2*ρ then (8/3 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro ℓ _
        apply mul_le_mul_of_nonneg_left (h41n_geom_key (zpow_pos two_pos _) hρ J)
        have := hcap ℓ
        positivity
    _ ≤ 60000 * (k:ℝ)^4 * Real.log 2 *
          ∑ ℓ ∈ ν.bandSupport, if (2:ℝ)^(-ℓ) ≤ 2*ρ then capacity ν ℓ else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro ℓ _
        have := hcap ℓ
        split_ifs
        · have : 0 ≤ (k:ℝ)^4 * Real.log 2 * capacity ν ℓ := by positivity
          nlinarith
        · simp

