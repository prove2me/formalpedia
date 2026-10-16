-- Prove2me | solution 1 for OAI.RandomKSAT.deletionQ_poly_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:28:33.878984+00:00
-- url     : https://prove2.me/submissions/02cae2bf-b6ee-421a-9d92-9385ac75a4a1

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/WeightedRewards.lean:L386-L398
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.deletionQ_poly_bound. The node keeps its source
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

-- ---- from OAI.Probability.SATVariance.BlockKilling ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma replacementK_succ (r : ℕ) : replacementK (r+1) = ((2 : ℝ)^(r+1)*r)^r := by
  simp [replacementK]

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.MarkovReplacement ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma replacementK_one_le {r : ℕ} (hr : 1 ≤ r) : 1 ≤ replacementK (r+1) := by
  rw [replacementK_succ]
  apply one_le_pow₀
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (by exact_mod_cast hr)

lemma lifetimeBeta_succ {r : ℕ} (hr : 0 < r) : lifetimeBeta (r+1) = 1+(r : ℝ)⁻¹ := by
  simp only [lifetimeBeta, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have hr₀ : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  field_simp

lemma lifetimeC_pos {r : ℕ} (hr : 1 ≤ r) : 0 < lifetimeC (r+1) := by
  have hK := replacementK_one_le hr
  unfold lifetimeC
  exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (by linarith) _)

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

lemma deletionQ_poly_bound {r Z : ℕ} (hr : 2 ≤ r) :
    deletionQ (r+1) (max 1 Z) ≤ (lifetimeC (r+1)+1)*(1+(Z : ℝ))^2 := by
  unfold deletionQ
  have hb := lifetimeBeta_bounds hr
  have hd : (1 : ℝ) ≤ (max 1 Z : ℕ) := by exact_mod_cast le_max_left 1 Z
  have hd' : ((max 1 Z : ℕ) : ℝ) ≤ 1+(Z : ℝ) := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith [Nat.cast_nonneg (α := ℝ) Z]) (by linarith)
  have hp := Real.rpow_le_rpow_of_exponent_le hd (show lifetimeBeta (r+1) ≤ (2 : ℝ) by linarith)
  change _ ≤ ((max 1 Z : ℕ) : ℝ)^((2 : ℕ) : ℝ) at hp
  rw [Real.rpow_natCast] at hp
  apply mul_le_mul_of_nonneg_left (hp.trans (pow_le_pow_left₀ (by positivity) hd' 2))
  linarith [lifetimeC_pos (by omega : 1 ≤ r)]

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.deletionQ_poly_bound := @_root_.OAI.RandomKSAT.deletionQ_poly_bound
