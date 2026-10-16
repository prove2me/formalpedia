-- Prove2me | solution 1 for OAI.RandomKSAT.killRatio_limit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T15:41:10.750544+00:00
-- url     : https://prove2.me/submissions/087eb2a0-ae90-4b47-82e5-2431563386cb

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/SharpnessEstimates.lean:L58-L74
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.killRatio_limit. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATSharpness
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities
import Definitions.Def_OAI_Probability_SATVariance_Subcube
import Theorems.Thm_OAI_RandomKSAT_killRatio_succ

-- ---- from OAI.Probability.SATVariance.FrozenReplacement ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma killRatio_zero (u b : ℕ) : killRatio u b 0 = 1 := by
  simp [killRatio]

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.SharpnessEstimates ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace RandomKSAT

lemma tendsto_nat_pow_real (m : ℕ) (hm : 0 < m) :
    Tendsto (fun N : ℕ => (N : ℝ)^m) atTop atTop :=
  (tendsto_pow_atTop (Nat.ne_of_gt hm)).comp tendsto_natCast_atTop_atTop

lemma subcube_factor_limit {m : ℕ} (hm : 0 < m) (s : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) * ((N^m : ℕ) - (s : ℝ)) /
      (2 * ((N^(m+1) : ℕ) - (s : ℝ)))) atTop (𝓝 (1/2 : ℝ)) := by
  have h1 : Tendsto (fun N : ℕ => (1 : ℝ) - s/(N : ℝ)^m) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub ((tendsto_const_nhds (x := (s : ℝ))).div_atTop (tendsto_nat_pow_real m hm))
  have h2 : Tendsto (fun N : ℕ => (2 : ℝ) * (1 - s/(N : ℝ)^(m+1))) atTop (𝓝 2) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := (s : ℝ))).div_atTop (tendsto_nat_pow_real (m+1) (by omega))))
  apply (h1.div h2 (by norm_num)).congr'
  filter_upwards [eventually_ge_atTop (s+1)] with N hN
  have hN0 : 0 < N := by omega
  have hx : (N : ℝ) ≠ 0 := by positivity
  have hsN : s < N^(m+1) := lt_of_lt_of_le (by omega) (Nat.le_pow (by omega))
  have hden : (N : ℝ)^(m+1) - s ≠ 0 := by
    have hh : (s : ℝ) < (N^(m+1) : ℕ) := by exact_mod_cast hsN
    push_cast at hh
    linarith
  change (1 - (s : ℝ)/(N : ℝ)^m) / (2 * (1 - (s : ℝ)/(N : ℝ)^(m+1))) = _
  push_cast
  field_simp
  ring

lemma killRatio_limit {m : ℕ} (hm : 0 < m) (s : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ)^s * killRatio (N^(m+1)) (N^m) s)
      atTop (𝓝 (((2 : ℝ)^s)⁻¹)) := by
  induction s with
  | zero => simp [killRatio_zero]
  | succ s ih =>
    have hh := ih.mul (subcube_factor_limit hm s)
    have hc : ((2 : ℝ)^s)⁻¹ * (1/2) = ((2 : ℝ)^(s+1))⁻¹ := by
      rw [pow_succ, mul_inv_rev]
      ring
    rw [hc] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (s+1)] with N hN
    have hsb : s ≤ N^m := (by omega : s ≤ N).trans (Nat.le_pow hm)
    have hsu : s < N^(m+1) := lt_of_lt_of_le (by omega) (Nat.le_pow (by omega))
    rw [killRatio_succ hsu hsb, pow_succ]
    ring

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology


theorem solution : type_of% @_root_.OAI.RandomKSAT.killRatio_limit := @_root_.OAI.RandomKSAT.killRatio_limit
