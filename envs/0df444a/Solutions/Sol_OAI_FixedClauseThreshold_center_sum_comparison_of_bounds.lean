-- Prove2me | solution 1 for OAI.FixedClauseThreshold.center_sum_comparison_of_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:53:57.230816+00:00
-- url     : https://prove2.me/submissions/0f34df53-6529-41c1-9715-435d56d37819

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/CenterComparison.lean:L169-L229
-- (upload_full_project.md Phase 4): solution for node OAI.FixedClauseThreshold.center_sum_comparison_of_bounds. The node keeps its source
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
import Theorems.Thm_OAI_FixedClauseThreshold_auxiliary_interpolation_center_lower
import Theorems.Thm_OAI_FixedClauseThreshold_center_lower_of_auxiliary_probability

-- ---- from OAI.Probability.RandomSAT.Clauses ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Signed variable sets, clause cardinalities, and the exact probability of killing
a nonempty solution set.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem nonempty_properClause {n k : ℕ} (hkn : k ≤ n) :
    Nonempty (ProperClause n k) := by
  apply Fintype.card_pos_iff.mp
  rw [card_properClause]
  exact Nat.mul_pos (Nat.choose_pos hkn) (by positivity)

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.FiniteMean ----
namespace OAI

/-!
Uniform finite expectations and variances.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem uniformMean_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : uniformMean f ≤ uniformMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (Nat.cast_nonneg _)

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.ClauseProcess ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Coordinate erasure, independent clause averaging, survival probabilities, and
iterated replacement.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem alive_le_one {n : ℕ} (S : Finset (Assignment n)) : alive S ≤ 1 := by
  unfold alive
  split <;> norm_num

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.Variance ----
namespace OAI

/-!
Stopped satisfiable lifetimes, insertion delays, and the coordinate-omission
variance bound in terms of integrated forcing.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem lifetime_le {n k m : ℕ} (S : Finset (Assignment n)) (F : Formula n k m) :
    lifetime k m S F ≤ m := by
  induction m generalizing S with
  | zero => simp [lifetime]
  | succ m ih =>
    simp only [lifetime, Nat.cast_add, Nat.cast_one]
    linarith [alive_le_one (addClause S (F 0)), ih (addClause S (F 0)) (Fin.tail F)]

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.Concentration ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Normalized capped centers and polynomial concentration of the proper-clause
satisfiability probability.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem delta_pos {k : ℕ} (hk : 3 ≤ k) : 0 < delta k := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  unfold delta
  exact div_pos (by linarith) (by positivity)

theorem center_le_capMultiplier {n k : ℕ} (hkn : k ≤ n) (hn : 0 < n) :
    center n k ≤ capMultiplier k := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  have h := uniformMean_mono (fun F : Formula n k (mainCap n k) => lifetime_le Finset.univ F)
  rw [uniformMean_const] at h
  unfold center lifetimeMean
  rw [div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)]
  simpa [mainCap] using h

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.CenterComparison ----
namespace OAI

/-!
Partition interpolation and concentration yield summable-error comparisons
for centers of two blocks and of neighboring sizes.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem densityWindow_pos {n k : ℕ} (hn : 0 < n) : 0 < densityWindow n k :=
  Real.rpow_pos_of_pos (by exact_mod_cast hn) _

theorem fluctuationWindow_eq_mul {n k : ℕ} (hn : 0 < n) :
    fluctuationWindow n k = (n : ℝ) * densityWindow n k := by
  unfold fluctuationWindow densityWindow
  rw [sub_eq_add_neg, Real.rpow_add (by exact_mod_cast hn), Real.rpow_one]

theorem densityWindow_antitone {r s k : ℕ} (hk : 3 ≤ k) (hr : 0 < r) (hrs : r ≤ s) :
    densityWindow s k ≤ densityWindow r k :=
  Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hr) (by exact_mod_cast hrs)
    (neg_nonpos.mpr (delta_pos hk).le)

theorem center_sum_comparison_of_bounds {r s k : ℕ} (hk : 3 ≤ k)
    (hr : k + 1 ≤ r) (hs : k + 1 ≤ s)
    (hrrep : 2 * repeatPairs k ≤ r) (hsrep : 2 * repeatPairs k ≤ s)
    (hrerr : concentrationError r k ≤ 1 / 2) (hserr : concentrationError s k ≤ 1 / 2)
    (hrsample : samplingError r k ≤ 1 / 4) (hssample : samplingError s k ≤ 1 / 4)
    (hNerr : concentrationError (r + s) k < (transferLower k)^2 / 2)
    (hlow : 2 * densityWindow (min r s) k ≤ min (center r k) (center s k)) :
    min (center r k) (center s k) - 4 * densityWindow (min r s) k ≤ center (r + s) k := by
  have hr0 : 0 < r := by omega
  have hs0 : 0 < s := by omega
  have hu0 : 0 < min r s := lt_min hr0 hs0
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs0
  have hN' : (0 : ℝ) < (r : ℝ) + s := by positivity
  let c := min (center r k) (center s k) - 2 * densityWindow (min r s) k
  have hc0 : 0 ≤ c := sub_nonneg.mpr hlow
  have hcL : c ≤ capMultiplier k := by
    have hh := (min_le_left (center r k) (center s k)).trans (center_le_capMultiplier (by omega) hr0)
    dsimp [c]
    have hp := (densityWindow_pos (k := k) hu0).le
    linarith
  have hcr : c + 2 * densityWindow r k ≤ center r k := by
    have hd := densityWindow_antitone hk hu0 (min_le_left r s)
    have hh := min_le_left (center r k) (center s k)
    dsimp [c]
    linarith
  have hcs : c + 2 * densityWindow s k ≤ center s k := by
    have hd := densityWindow_antitone hk hu0 (min_le_right r s)
    have hh := min_le_right (center r k) (center s k)
    dsimp [c]
    linarith
  let m := ⌊c * ((r : ℝ) + s)⌋₊
  have hm : (m : ℝ) ≤ c * ((r : ℝ) + s) := Nat.floor_le (mul_nonneg hc0 hN'.le)
  have hmr : (m : ℝ) * ((r : ℝ) / (r + s)) ≤ c * r := by
    have hh := mul_le_mul_of_nonneg_right hm (show 0 ≤ (r : ℝ) / (r + s) by positivity)
    have he : c * ((r : ℝ) + s) * ((r : ℝ) / (r + s)) = c * r := by field_simp
    rwa [he] at hh
  have hms : (m : ℝ) * ((s : ℝ) / (r + s)) ≤ c * s := by
    have hh := mul_le_mul_of_nonneg_right hm (show 0 ≤ (s : ℝ) / (r + s) by positivity)
    have he : c * ((r : ℝ) + s) * ((s : ℝ) / (r + s)) = c * s := by field_simp
    rwa [he] at hh
  have hprob := auxiliary_interpolation_center_lower hk hr hs hrrep hsrep hrerr hserr
    (hm.trans (mul_le_mul_of_nonneg_right hcL hN'.le))
    (show (m : ℝ) * ((r : ℝ) / (r + s)) + 2 * fluctuationWindow r k ≤ (r : ℝ) * center r k by
      rw [fluctuationWindow_eq_mul hr0]
      have hh := mul_le_mul_of_nonneg_left hcr hr'.le
      nlinarith)
    (show (m : ℝ) * ((s : ℝ) / (r + s)) + 2 * fluctuationWindow s k ≤ (s : ℝ) * center s k by
      rw [fluctuationWindow_eq_mul hs0]
      have hh := mul_le_mul_of_nonneg_left hcs hs'.le
      nlinarith)
  have hhalf : (transferLower k)^2 / 2 ≤ auxiliaryProbability (r + s) k m := by
    have hh := mul_le_mul_of_nonneg_left (show (1 / 2 : ℝ) ≤ 1 - samplingError r k - samplingError s k by linarith)
      (sq_nonneg (transferLower k))
    nlinarith
  have hcN := center_lower_of_auxiliary_probability hk (by omega : k + 1 ≤ r + s) hc0 hcL
    (show concentrationError (r + s) k < auxiliaryProbability (r + s) k ⌊c * ((r + s : ℕ) : ℝ)⌋₊ by
      simpa only [Nat.cast_add, ← show ⌊c * ((r : ℝ) + s)⌋₊ = m from rfl] using hNerr.trans_le hhalf)
  have hd := densityWindow_antitone hk hu0 (show min r s ≤ r + s by omega)
  dsimp [c] at hcN
  linarith

end

end FixedClauseThreshold

end OAI

-- ---- platform node ----
open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.FixedClauseThreshold.center_sum_comparison_of_bounds := @_root_.OAI.FixedClauseThreshold.center_sum_comparison_of_bounds
