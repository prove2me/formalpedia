-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.MainProofs.bohman_limit_fraction_graphs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:05:37.667061+00:00
-- url     : https://prove2.me/submissions/96fca556-d5cf-47f3-8a4e-7e59d9c42740

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
import Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_subgroup_capacity_limit
import Theorems.Thm_GroupTheoreticShannonCapacity_addSubgroupShannonCapacity_le_shannonCapacity
import Theorems.Thm_GroupTheoreticShannonCapacity_shannonCapacity_fractionGraph_eq_of_eq
import Theorems.Thm_GroupTheoreticShannonCapacity_shannonCapacity_fractionGraph_le


set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice
namespace GroupTheoreticShannonCapacity.MainProofs
theorem _root_.solution :
    ∀ ε > 0, ∃ M : ℝ, ∀ p q : ℕ, [NeZero p] → (q : ℝ) > 0 → (p : ℝ) / q > M →
      |(p : ℝ) / q - shannonCapacity (fractionGraph p q)| < ε := by
  intro ε hε
  -- Get threshold M₀ from subgroup_capacity_limit
  obtain ⟨M₀, hM⟩ := subgroup_capacity_limit ε hε
  -- Use max 5 M₀ to ensure p/q > 5 > 1, so q ≤ p
  use max 5 M₀
  intro p q hp_ne hq_pos hpq_large
  haveI : NeZero p := hp_ne
  have hp_ne' : p ≠ 0 := NeZero.ne p
  have hq_pos' : 0 < q := by exact_mod_cast hq_pos
  -- p/q > M₀ (since p/q > max 5 M₀ ≥ M₀)
  have hpq_large' : (p : ℝ) / q > M₀ := calc
    (p : ℝ) / q > max 5 M₀ := hpq_large
    _ ≥ M₀ := le_max_right _ _
  -- Get (a, b) from subgroup_capacity_limit with a/b = p/q
  obtain ⟨a, b, ha_ne, hab_eq, h_subgroup_gap⟩ := hM p q hp_ne' hq_pos' hpq_large'
  haveI : NeZero a := ha_ne
  -- Key: Θ(E_{a/b}) = Θ(E_{p/q}) since a/b = p/q
  have hb_pos : 0 < b := by
    by_contra h
    push_neg at h
    interval_cases b
    -- If b = 0, then a/b = a/0, but hab_eq says a/0 = p/q with q > 0, contradiction
    simp only [Nat.cast_zero, div_zero] at hab_eq
    have hq_ne : (q : ℚ) ≠ 0 := by positivity
    have : (p : ℚ) / q = 0 := hab_eq.symm
    rw [div_eq_zero_iff] at this
    rcases this with hp0 | hq0
    · exact hp_ne' (Nat.cast_eq_zero.mp hp0)
    · exact hq_ne hq0
  have h_cap_eq : shannonCapacity (fractionGraph a b) = shannonCapacity (fractionGraph p q) :=
    shannonCapacity_fractionGraph_eq_of_eq a b p q hb_pos hq_pos' hab_eq
  -- Key chain: Θ_g(E_{a/b}) ≤ Θ(E_{a/b}) = Θ(E_{p/q}) ≤ p/q
  have h_subgroup_le : addSubgroupShannonCapacity (fractionGraph a b) ≤
      shannonCapacity (fractionGraph a b) :=
    addSubgroupShannonCapacity_le_shannonCapacity (fractionGraph a b)
  -- Upper bound: Θ(E_{p/q}) ≤ p/q
  -- Since p/q > max 5 M₀ ≥ 5 > 1, we have q < p
  have hpq_le : q ≤ p := by
    have h1 : (p : ℝ) / q > 1 := calc
      (p : ℝ) / q > max 5 M₀ := hpq_large
      _ ≥ 5 := le_max_left _ _
      _ > 1 := by norm_num
    have h2 : (q : ℝ) < p := by
      rwa [gt_iff_lt, one_lt_div (by positivity : (0 : ℝ) < q)] at h1
    exact_mod_cast le_of_lt h2
  have h_upper : shannonCapacity (fractionGraph p q) ≤ (p : ℝ) / q :=
    shannonCapacity_fractionGraph_le p q hq_pos' hpq_le
  -- Since Θ_g ≤ Θ ≤ p/q, we have p/q - Θ ≤ p/q - Θ_g < ε
  have h_gap_nonneg : 0 ≤ (p : ℝ) / q - shannonCapacity (fractionGraph p q) := by linarith
  rw [abs_of_nonneg h_gap_nonneg]
  -- Need: p/q - Θ(E_{p/q}) < ε
  -- Have: p/q - Θ_g(E_{a/b}) < ε  and  Θ_g(E_{a/b}) ≤ Θ(E_{a/b}) = Θ(E_{p/q})
  calc (p : ℝ) / q - shannonCapacity (fractionGraph p q)
      = (p : ℝ) / q - shannonCapacity (fractionGraph a b) := by rw [h_cap_eq]
    _ ≤ (p : ℝ) / q - addSubgroupShannonCapacity (fractionGraph a b) := by linarith [h_subgroup_le]
    _ < ε := h_subgroup_gap
end GroupTheoreticShannonCapacity.MainProofs
