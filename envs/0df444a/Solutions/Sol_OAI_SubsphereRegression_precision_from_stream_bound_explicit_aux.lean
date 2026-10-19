-- Prove2me | solution 1 for OAI.SubsphereRegression.precision_from_stream_bound_explicit_aux
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:33:53.101041+00:00
-- url     : https://prove2.me/submissions/3b0bcac6-a7bf-48d0-a458-445c5ded8c59

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Estimates/Numerics.lean:L13-L96
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereRegression.precision_from_stream_bound_explicit_aux. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks
import Definitions.Def_OAI_Probability_Subsphere_Regression_Streaming

-- ---- from OAI.Probability.Subsphere.Estimates.Numerics ----
namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereRegression

lemma precision_from_stream_bound_explicit_aux {d M T a q : ℕ} {ε A : ℝ}
    (hd : 32 ≤ d) (hT : d ≤ 4*T) (hq : 0 < q) (hdq : d ≤ 8*q)
    (ha : d ≤ 4*a) (hM : (M : ℝ) ≤ A * (d : ℝ)^2) (hA : 0 < A)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hbound : (2/3 : ℝ) ≤ ((T : ℝ)+1) * ((3 : ℝ)*4^d * ε^a) *
      ((32768 : ℝ)^d * ((2 : ℝ)^M)^(1/(q : ℝ)))^(T/q+1)) :
    (1 / (4*(256+128*A))) * (d : ℝ) * Real.log (1/ε) ≤ (T : ℝ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hdp : (d : ℝ) ≤ 4*T := by exact_mod_cast hT
  have hdqp : (d : ℝ) ≤ 8*q := by exact_mod_cast hdq
  have hap : (d : ℝ) ≤ 4*a := by exact_mod_cast ha
  have hB : ((T/q+1 : ℕ) : ℝ) * d ≤ 12*T := by
    have hbd : (T/q+1)*d ≤ 12*T := by
      have hmul := Nat.div_mul_le_self T q
      calc
        (T/q+1)*d = (T/q)*d+d := by ring
        _ ≤ (T/q)*(8*q)+d := Nat.add_le_add_right (Nat.mul_le_mul_left _ hdq) _
        _ = 8*((T/q)*q)+d := by ring
        _ ≤ 8*T+d := Nat.add_le_add_right (Nat.mul_le_mul_left 8 hmul) _
        _ ≤ 12*T := by omega
    exact_mod_cast hbd
  have hMq : (M : ℝ) / q ≤ 8*A*d := by
    apply (div_le_iff₀ hq0).2
    calc
      (M : ℝ) ≤ A*d^2 := hM
      _ ≤ A*d*(8*q) := by nlinarith [mul_le_mul_of_nonneg_left hdqp (by positivity : 0 ≤ A*d)]
      _ = 8*A*d*q := by ring
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2/3) hbound
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_rpow (by positivity), Real.log_pow] at hlog
  have hlogε : Real.log (1/ε) = -Real.log ε := by simp
  have hlogε0 : 0 ≤ Real.log (1/ε) := Real.log_nonneg ((le_div_iff₀ hε).2 (by simpa using hε1))
  have heq : (1/(q : ℝ)) * ((M : ℝ)*Real.log 2) = ((M : ℝ)/q)*Real.log 2 := by ring
  rw [heq] at hlog
  have hlT : Real.log ((T : ℝ)+1) ≤ T := by
    simpa using Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < T+1)
  have hl3 : Real.log (3 : ℝ) ≤ 3 := Real.log_le_self (by norm_num)
  have hl4 : Real.log (4 : ℝ) ≤ 4 := Real.log_le_self (by norm_num)
  have hl32 : Real.log (32768 : ℝ) ≤ 15 := by
    have hpow : (32768 : ℝ) = 2 ^ (15 : ℕ) := by norm_num
    rw [hpow, Real.log_pow]
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h2 ⊢
    linarith
  have hl2 : Real.log (2 : ℝ) ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1; norm_num
  have hl23 : -(1 : ℝ) ≤ Real.log (2/3 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2/3)
    norm_num at h
    linarith
  have hinside : (d : ℝ)*Real.log 32768 + ((M : ℝ)/q)*Real.log 2 ≤
      (15+8*A)*d := by
    have hm0 : (0 : ℝ) ≤ (M : ℝ)/q := by positivity
    have h1 := mul_le_mul_of_nonneg_left hl32 hd0.le
    have h2 := mul_le_mul_of_nonneg_left hl2 hm0
    nlinarith
  have hfull : ((T/q+1 : ℕ) : ℝ) *
      ((d : ℝ)*Real.log 32768 + ((M : ℝ)/q)*Real.log 2) ≤
      12*T*(15+8*A) := by
    calc
      _ ≤ ((T/q+1 : ℕ) : ℝ) * ((15+8*A)*d) :=
        mul_le_mul_of_nonneg_left hinside (Nat.cast_nonneg _)
      _ = (15+8*A)*(((T/q+1 : ℕ) : ℝ)*d) := by ring
      _ ≤ (15+8*A)*(12*T) := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = _ := by ring
  have hd4 : (4 : ℝ) ≤ d := by exact_mod_cast (by omega : 4 ≤ d)
  have hlogbound : (a : ℝ)*Real.log (1/ε) ≤ (256+128*A)*T := by
    have h4 := mul_le_mul_of_nonneg_left hl4 hd0.le
    rw [hlogε]
    nlinarith [mul_nonneg hA.le hT0]
  have hmain : (d : ℝ)*Real.log (1/ε) ≤ 4*(256+128*A)*T := by
    have ham := mul_le_mul_of_nonneg_right hap hlogε0
    linarith
  have hden : (0 : ℝ) < 4*(256+128*A) := by positivity
  calc
    _ = ((d : ℝ)*Real.log (1/ε))/(4*(256+128*A)) := by ring
    _ ≤ T := (div_le_iff₀ hden).2 (by nlinarith [hmain])

end SubsphereRegression
end
end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.SubsphereRegression.precision_from_stream_bound_explicit_aux := @_root_.OAI.SubsphereRegression.precision_from_stream_bound_explicit_aux
