-- Prove2me | solution 1 for OAI.RandomKSAT.floor_window_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:03:16.644783+00:00
-- url     : https://prove2.me/submissions/67e6af18-d6ca-455f-adab-7ae563753c5d

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/FailureWindows.lean:L98-L146
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.floor_window_bounds. The node keeps its source
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

lemma floor_window_bounds {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {n R : ℕ} (hR : 1 ≤ R) (hn : 8 ≤ a*n) :
    let Q := ⌊a*n/4⌋₊
    (a*n/8 ≤ (Q:ℝ)) ∧ ((Q:ℝ) ≤ a*n/4) ∧
      2*Q ≤ 2*R*n ∧ Q+R*n ≤ 2*R*n+1 ∧ Q ≤ 2*R*n ∧
      a/(16*((2*R:ℕ)+1:ℝ)^2) ≤
        (Q:ℝ)*((2*R*n:ℕ)+1-Q-R*n:ℝ)/((2*R*n:ℕ)+1:ℝ)^2 := by
  dsimp only
  let Q := ⌊a*n/4⌋₊
  have hn0 : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    norm_num [this] at hn
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  have hRR : (1:ℝ) ≤ R := by exact_mod_cast hR
  have hQup : (Q:ℝ) ≤ a*n/4 := Nat.floor_le (by positivity)
  have hQlo : a*n/8 ≤ (Q:ℝ) := by
    have hh := Nat.lt_floor_add_one (a*n/4)
    change a*n/4 < (Q:ℝ)+1 at hh
    linarith
  have haN := mul_le_mul_of_nonneg_right ha1 hnR.le
  have hRn : (n:ℝ) ≤ R*n := by nlinarith
  have h2Q : 2*Q ≤ 2*R*n := by
    have : 2*(Q:ℝ) ≤ 2*R*n := by nlinarith
    exact_mod_cast this
  have hQV : Q+R*n ≤ 2*R*n+1 := by
    have : (Q:ℝ)+R*n ≤ 2*R*n+1 := by nlinarith
    exact_mod_cast this
  refine ⟨hQlo,hQup,h2Q,hQV,by omega,?_⟩
  have hgap : (n:ℝ)/2 ≤ (2*R*n:ℕ)+1-Q-R*n := by
    push_cast
    nlinarith
  have hden : (2*R*n:ℕ)+1 ≤ ((2*R:ℕ)+1:ℝ)*n := by
    push_cast
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn0
    nlinarith
  have hd0 : (0:ℝ) < (2*R*n:ℕ)+1 := by positivity
  have hd1 : (0:ℝ) < ((2*R:ℕ)+1:ℝ) := by positivity
  have hnum : a*n^2/16 ≤ (Q:ℝ)*((2*R*n:ℕ)+1-Q-R*n:ℝ) := by
    have hh := mul_le_mul hQlo hgap (by positivity) (by positivity : (0:ℝ) ≤ Q)
    nlinarith
  have hsden : ((2*R*n:ℕ)+1:ℝ)^2 ≤ (((2*R:ℕ)+1:ℝ)*n)^2 :=
    pow_le_pow_left₀ hd0.le hden 2
  apply (le_div_iff₀ (sq_pos_of_pos hd0)).mpr
  have hcoef0 : 0 ≤ a/(16*((2*R:ℕ)+1:ℝ)^2) := by positivity
  apply le_trans (mul_le_mul_of_nonneg_left hsden hcoef0)
  calc
    a/(16*((2*R:ℕ)+1:ℝ)^2)*(((2*R:ℕ)+1:ℝ)*n)^2 = a*n^2/16 := by field_simp
    _ ≤ _ := hnum

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.floor_window_bounds := @_root_.OAI.RandomKSAT.floor_window_bounds
