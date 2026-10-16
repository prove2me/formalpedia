-- Prove2me | solution 1 for OAI.RandomKSAT.deletionQ_sq_poly_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:29:48.978066+00:00
-- url     : https://prove2.me/submissions/80239823-487c-4cde-a731-709578ce73dd

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/WeightedRewards.lean:L400-L412
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.deletionQ_sq_poly_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiberRefresh
import Definitions.Def_OAI_Probability_SATVariance_PairEvolution
import Definitions.Def_OAI_Probability_SATVariance_HiddenTests
import Definitions.Def_OAI_Probability_SATVariance_WeightedRewards

-- ---- from OAI.Probability.SATVariance.MarkovReplacement ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma lifetimeBeta_succ {r : ℕ} (hr : 0 < r) : lifetimeBeta (r+1) = 1+(r : ℝ)⁻¹ := by
  simp only [lifetimeBeta, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have hr₀ : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  field_simp

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.WeightedRewards ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma lifetimeBeta_bounds {r : ℕ} (hr : 2 ≤ r) :
    1 ≤ lifetimeBeta (r+1) ∧ lifetimeBeta (r+1) ≤ (r : ℝ) ∧
      2*lifetimeBeta (r+1) ≤ 3 := by
  rw [lifetimeBeta_succ (by omega)]
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hi : (0 : ℝ) ≤ (r : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hj : (r : ℝ)⁻¹ ≤ 1/2 := by
    apply (inv_le_iff_one_le_mul₀ (by positivity)).2
    linarith
  constructor
  · linarith
  constructor <;> linarith

lemma deletionQ_sq_poly_bound {r Z : ℕ} (hr : 2 ≤ r) :
    (deletionQ (r+1) (max 1 Z))^2 ≤ (lifetimeC (r+1)+1)^2*(1+(Z : ℝ))^3 := by
  unfold deletionQ
  rw [mul_pow, ← Real.rpow_mul_natCast (by positivity)]
  have hb := lifetimeBeta_bounds hr
  have hd : (1 : ℝ) ≤ (max 1 Z : ℕ) := by exact_mod_cast le_max_left 1 Z
  have hd' : ((max 1 Z : ℕ) : ℝ) ≤ 1+(Z : ℝ) := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith [Nat.cast_nonneg (α := ℝ) Z]) (by linarith)
  have hp := Real.rpow_le_rpow_of_exponent_le hd (show lifetimeBeta (r+1)* (2 : ℝ) ≤ (3 : ℝ) by linarith)
  change _ ≤ ((max 1 Z : ℕ) : ℝ)^((3 : ℕ) : ℝ) at hp
  rw [Real.rpow_natCast] at hp
  exact mul_le_mul_of_nonneg_left (hp.trans (pow_le_pow_left₀ (by positivity) hd' 3)) (sq_nonneg _)

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.deletionQ_sq_poly_bound := @_root_.OAI.RandomKSAT.deletionQ_sq_poly_bound
