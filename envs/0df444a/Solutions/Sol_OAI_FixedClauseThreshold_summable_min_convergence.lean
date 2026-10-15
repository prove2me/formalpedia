-- Prove2me | solution 1 for OAI.FixedClauseThreshold.summable_min_convergence
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:59:34.497981+00:00
-- url     : https://prove2.me/submissions/b1e0bb93-d628-4587-acad-defad1d3a008

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/Convergence.lean:L141-L173
-- (upload_full_project.md Phase 4): solution for node OAI.FixedClauseThreshold.summable_min_convergence. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess
import Definitions.Def_OAI_Probability_RandomSAT_Binomial
import Definitions.Def_OAI_Probability_RandomSAT_Forcing
import Definitions.Def_OAI_Probability_RandomSAT_Variance
import Definitions.Def_OAI_Probability_RandomSAT_Concentration
import Definitions.Def_OAI_Probability_RandomSAT_CenterBounds
import Definitions.Def_OAI_Probability_RandomSAT_Interpolation
import Definitions.Def_OAI_Probability_RandomSAT_Transfer
import Definitions.Def_OAI_Probability_RandomSAT_CenterComparison
import Definitions.Def_OAI_Probability_RandomSAT_Convergence
import Theorems.Thm_OAI_FixedClauseThreshold_balanced_blocks_bound

-- ---- from OAI.Probability.RandomSAT.Convergence ----
namespace OAI

/-!
A balanced-block geometric potential proves convergence from boundedness and
summable-min comparisons, including block counts that are not powers of two.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem balanceConstant_pos {β : ℝ} (hβ : 0 < β) : 0 < balanceConstant β :=
  div_pos (Real.rpow_pos_of_pos (by norm_num) _) (sub_pos.mpr (Real.one_lt_rpow (by norm_num) hβ))

theorem balanced_tail_bound (u : ℕ → ℝ) {A β : ℝ} (hA : 0 ≤ A) (hβ : 0 < β)
    {N s : ℕ} (hsN : N ≤ s) (hs : 0 < s)
    (hadd : ∀ r ≥ N, ∀ t ≥ N,
      min (u r) (u t) - A * (min r t : ℝ)^(-β) ≤ u (r + t))
    (hnext : u s - A * (s : ℝ)^(-β) ≤ u (s + 1)) :
    ∀ n ≥ s * s,
      u s - A * (1 + balanceConstant β) * (s : ℝ)^(-β) ≤ u n := by
  intro n hn
  have hq : s ≤ n / s := (Nat.le_div_iff_mul_le hs).mpr hn
  have hr : n % s ≤ n / s := (Nat.mod_lt n hs).le.trans hq
  have hb := balanced_blocks_bound u hA hβ hsN hs hadd hnext (n / s) (by omega) (n % s) hr
  rw [Nat.mul_comm (n / s) s, Nat.div_add_mod] at hb
  have hcoef : 0 ≤ A * balanceConstant β * (s : ℝ)^(-β) * ((n / s : ℕ) : ℝ)^(-β) := by
    have hB := (balanceConstant_pos hβ).le
    exact mul_nonneg (mul_nonneg (mul_nonneg hA hB) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  nlinarith

theorem summable_min_convergence (u : ℕ → ℝ) {A β : ℝ} (hA : 0 ≤ A) (hβ : 0 < β)
    (hUpper : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u)
    (hLower : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop u)
    (hcompare : ∃ N : ℕ,
      (∀ r ≥ N, ∀ s ≥ N, min (u r) (u s) - A * (min r s : ℝ)^(-β) ≤ u (r + s)) ∧
      (∀ s ≥ N, u s - A * (s : ℝ)^(-β) ≤ u (s + 1))) :
    Filter.Tendsto u Filter.atTop (nhds (Filter.limsup u Filter.atTop)) := by
  obtain ⟨N, hadd, hnext⟩ := hcompare
  let α := Filter.limsup u Filter.atTop
  apply tendsto_order.mpr
  constructor
  · intro a ha
    let ε := (α - a) / 3
    have hε : 0 < ε := by dsimp [ε, α]; linarith
    have ht := (tendsto_rpow_neg_atTop hβ).comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have hcost : Filter.Tendsto (fun s : ℕ => A * (1 + balanceConstant β) * (s : ℝ)^(-β))
        Filter.atTop (nhds 0) := by
      simpa only [Function.comp_apply, mul_zero] using ht.const_mul (A * (1 + balanceConstant β))
    have hsmall := hcost.eventually_lt_const hε
    have hhigh : ∃ᶠ s : ℕ in Filter.atTop, α - ε < u s :=
      Filter.frequently_lt_of_lt_limsup hLower.isCoboundedUnder_le (by change α - ε < α; linarith)
    have hgood : ∀ᶠ s : ℕ in Filter.atTop,
        N ≤ s ∧ 0 < s ∧ A * (1 + balanceConstant β) * (s : ℝ)^(-β) < ε := by
      filter_upwards [Filter.eventually_ge_atTop (max N 1), hsmall] with s hs he
      exact ⟨by omega, by omega, he⟩
    obtain ⟨s, hsHigh, hsN, hs, hsSmall⟩ := (hhigh.and_eventually hgood).exists
    have htail := balanced_tail_bound u hA hβ hsN hs hadd (hnext s hsN)
    filter_upwards [Filter.eventually_ge_atTop (s * s)] with n hn
    have hh := htail n hn
    dsimp [ε] at hsHigh hsSmall
    linarith
  · intro a ha
    exact Filter.eventually_lt_of_limsup_lt ha hUpper

end

end FixedClauseThreshold

end OAI

-- ---- platform node ----
open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.FixedClauseThreshold.summable_min_convergence := @_root_.OAI.FixedClauseThreshold.summable_min_convergence
