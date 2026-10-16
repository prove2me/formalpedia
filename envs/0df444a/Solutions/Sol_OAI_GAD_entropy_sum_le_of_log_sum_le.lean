-- Prove2me | solution 1 for OAI.GAD.entropy_sum_le_of_log_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:36:04.58298+00:00
-- url     : https://prove2.me/submissions/57c72bc7-f160-4e4f-96dc-a3380d7098bf

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/LogDetEntropy.lean:L66-L94
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.entropy_sum_le_of_log_sum_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy

-- ---- from OAI.InformationTheory.AmplitudeDamping.LogDetEntropy ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder

open scoped BigOperators Topology
open Filter Set
namespace GAD

theorem logEntropyPrimitive_zero (a : ℝ) :
    logEntropyPrimitive a 0 = - Real.negMulLog a := by
  simp [logEntropyPrimitive, Real.negMulLog]

theorem continuousOn_logEntropyPrimitive (a : ℝ) :
    ContinuousOn (logEntropyPrimitive a) (Ici 0) := by
  have h₁ : Continuous (fun t : ℝ ↦ (t + a) * Real.log (t + a)) :=
    Real.continuous_mul_log.comp (continuous_id.add_const a)
  refine (h₁.continuousOn.sub Real.continuous_mul_log.continuousOn).sub ?_
  apply ContinuousOn.const_mul
  refine Real.continuousOn_log.comp (continuous_id.add_const 1).continuousOn ?_
  intro t ht
  change t + 1 ≠ 0
  have ht0 : 0 ≤ t := ht
  linarith

theorem hasDerivAt_logEntropyPrimitive {a t : ℝ} (ha : 0 ≤ a) (ht : 0 < t) :
    HasDerivAt (logEntropyPrimitive a)
      (Real.log (1 + a / t) - a / (t + 1)) t := by
  have hta : t + a ≠ 0 := by linarith
  have ht1 : t + 1 ≠ 0 := by linarith
  have h₁ := (Real.hasDerivAt_mul_log hta).comp t ((hasDerivAt_id t).add_const a)
  have h₂ := Real.hasDerivAt_mul_log ht.ne'
  have h₃ := ((Real.hasDerivAt_log ht1).comp t ((hasDerivAt_id t).add_const 1)).const_mul a
  convert! (h₁.sub h₂).sub h₃ using 1
  rw [one_add_div ht.ne', Real.log_div hta ht.ne']
  simp only [mul_one, div_eq_mul_inv]
  ring

theorem tendsto_logEntropyPrimitive (a : ℝ) :
    Tendsto (logEntropyPrimitive a) atTop (𝓝 a) := by
  have hdiff := (Real.tendsto_log_comp_add_sub_log a).sub
    (Real.tendsto_log_comp_add_sub_log 1)
  have h := (Real.tendsto_mul_log_one_add_div_atTop a).add (hdiff.const_mul a)
  simp only [sub_zero, mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop (-a)] with t ht hta
  have hne : t + a ≠ 0 := by linarith
  simp only [logEntropyPrimitive, one_add_div ht.ne',
    Real.log_div hne ht.ne']
  ring

theorem entropy_sum_le_of_log_sum_le {ι : Type u_1} [Fintype ι]
    (c a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (htrace : ∑ i, c i * a i = 0)
    (hlog : ∀ t : ℝ, 0 < t → ∑ i, c i * Real.log (1 + a i / t) ≤ 0) :
    ∑ i, c i * Real.negMulLog (a i) ≤ 0 := by
  let H : ℝ → ℝ := fun t ↦ ∑ i, c i * logEntropyPrimitive (a i) t
  have hcont : ContinuousOn H (Ici 0) :=
    continuousOn_finsetSum _ (fun i _ ↦ (continuousOn_logEntropyPrimitive (a i)).const_mul _)
  have hd (t : ℝ) (ht : 0 < t) :
      HasDerivAt H (∑ i, c i * Real.log (1 + a i / t)) t := by
    have h := HasDerivAt.sum (u := Finset.univ) (fun i _ ↦
      (hasDerivAt_logEntropyPrimitive (ha i) ht).const_mul (c i))
    convert! h using 1
    · ext t
      simp only [H, Finset.sum_apply]
    · simp only [mul_sub, Finset.sum_sub_distrib, ← mul_div_assoc, ← Finset.sum_div,
        htrace, zero_div, sub_zero]
  have hanti : AntitoneOn H (Ici 0) :=
    antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont
      (fun t ht ↦ (hd t (by simpa using ht)).differentiableAt.differentiableWithinAt)
      (fun t ht ↦ by rw [(hd t (by simpa using ht)).deriv]; exact hlog t (by simpa using ht))
  have hlim : Tendsto H atTop (𝓝 0) := by
    have h := tendsto_finsetSum Finset.univ (fun i _ ↦
      (tendsto_logEntropyPrimitive (a i)).const_mul (c i))
    simpa only [htrace] using h
  have hzero : 0 ≤ H 0 := le_of_tendsto hlim (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hanti (by simp) ht ht)
  simpa only [H, logEntropyPrimitive_zero, mul_neg, Finset.sum_neg_distrib,
    neg_nonneg] using hzero
end GAD

open scoped BigOperators ComplexOrder MatrixOrder Topology
open Matrix
namespace GAD
variable {ι : Type u_2} [Fintype ι] [DecidableEq ι]

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set


theorem solution : type_of% @_root_.OAI.GAD.entropy_sum_le_of_log_sum_le := @_root_.OAI.GAD.entropy_sum_le_of_log_sum_le
