-- Prove2me | solution 1 for OAI.RandomKSAT.exists_lower_scale
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:04:52.146391+00:00
-- url     : https://prove2.me/submissions/89522d15-f83f-4fff-bcb2-4d8f80d9646d

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/FailureWindows.lean:L162-L174
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.exists_lower_scale. The node keeps its source
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
import Definitions.Def_OAI_Probability_SATVariance_CountMoments
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_OmissionCompression
import Definitions.Def_OAI_Probability_SATVariance_CapBridge
import Definitions.Def_OAI_Probability_SATVariance_ShuffleAverages
import Definitions.Def_OAI_Probability_SATVariance_BystanderStops
import Definitions.Def_OAI_Probability_SATVariance_InsertionVariance
import Definitions.Def_OAI_Probability_SATVariance_IsolatedSupports
import Definitions.Def_OAI_Probability_SATVariance_BystanderVariance

-- ---- from OAI.Probability.SATVariance.Moments ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma real_rate_pos {k : ℕ} (hk : 1 ≤ k) : 0 < 1-((2 : ℝ)^k)⁻¹ := by
  have hp : (2 : ℝ) ≤ (2 : ℝ)^k := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk)
  exact sub_pos.mpr ((inv_lt_one₀ (by positivity)).mpr (by linarith))

lemma real_rate_lt_one (k : ℕ) : 1-((2 : ℝ)^k)⁻¹ < 1 := by
  have h : 0 < ((2 : ℝ)^k)⁻¹ := by positivity
  linarith

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.FailureWindows ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma eventual_geometric_small {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    {ε : ℝ} (hε : 0 < ε) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → r^n ≤ ε := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1
  have he : ∀ᶠ n : ℕ in Filter.atTop, r^n < ε := ht.eventually (gt_mem_nhds hε)
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp he
  exact ⟨N,fun n hn => (hN n hn).le⟩

lemma exists_lower_scale (k : ℕ) (hk : 1 ≤ k) :
    ∃ R : ℕ, 1 ≤ R ∧ U k ≤ 2*(R:ℝ) ∧ 2*(1-((2:ℝ)^k)⁻¹)^R < 1 := by
  obtain ⟨N,hN⟩ := eventual_geometric_small (real_rate_pos hk).le
    (real_rate_lt_one k) (by norm_num : (0:ℝ) < 1/4)
  obtain ⟨L,hL⟩ := exists_nat_gt (U k)
  let R := max N (max L 1)
  have hRN : N ≤ R := le_max_left _ _
  have hRL : L ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hR1 : 1 ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨R,hR1,?_,by linarith [hN R hRN]⟩
  have hLR : (L:ℝ) ≤ R := by exact_mod_cast hRL
  have hRR : (0:ℝ) ≤ R := by positivity
  linarith

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.exists_lower_scale := @_root_.OAI.RandomKSAT.exists_lower_scale
