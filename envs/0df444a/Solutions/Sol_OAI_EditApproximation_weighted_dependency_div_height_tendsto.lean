-- Prove2me | solution 1 for OAI.EditApproximation.weighted_dependency_div_height_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:31:38.753886+00:00
-- url     : https://prove2.me/submissions/a0cf2f91-5a2b-457f-9f0d-b8c898c3fdb1

import Mathlib
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_OAIQ361V3Ea001

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_TreeAccounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Finite comparison-tree accounting

A complete tree is indexed by its physical depth and child labels. Terminal
comparison costs may be carried forward, with zero costs in the other child
slots. The identities apply to that representation without any probability
or sampling hypothesis.
-/

namespace EditApproximation

open Finset

/-- The explicit small-growth bound used for the comparison frontiers. -/
theorem small_growth_pow {x : ℝ} (n : ℕ) (hx : 0 ≤ x)
    (hsmall : (n : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ n ≤ 1 + 2 * n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (n : ℝ) * x ≤ 1 / 2 := by
      push_cast at hsmall
      nlinarith
    have hprev := mul_le_mul_of_nonneg_right (ih hn) (by positivity : 0 ≤ 1 + x)
    rw [pow_succ]
    apply hprev.trans
    push_cast
    have hprod : 0 ≤ x * (1 - 2 * n * x) := by
      apply mul_nonneg hx
      nlinarith
    nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterSlack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Explicit slack at the large-input cutoff

The cutoff is handled symbolically: no expression with an astronomically
large exponent is expanded. The small-growth estimate supplies the
induction step. This proves the generous polynomial-versus-binary bound
used throughout the manuscript's numerical estimates.
-/

namespace EditApproximation

theorem polynomial_binary_growth_step (degree m : ℕ)
    (hsize : 4 * degree ≤ 2 * m + 1) :
    (2 * (m : ℝ) + 3) ^ degree ≤ 2 * (2 * (m : ℝ) + 1) ^ degree := by
  let d : ℝ := 2 * m + 1
  have hd : 0 < d := by dsimp [d] <;> positivity
  have hsizeR : 4 * (degree : ℝ) ≤ d := by
    dsimp only [d]
    exact_mod_cast hsize
  have hsmall : (degree : ℝ) * (2 / d) ≤ 1 / 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).2
    nlinarith
  have hbound : (1 + 2 / d) ^ degree ≤ 2 :=
    (small_growth_pow degree (by positivity) hsmall).trans (by nlinarith)
  have hrew : 2 * (m : ℝ) + 3 = d * (1 + 2 / d) := by
    dsimp [d]
    field_simp
    ring
  rw [hrew, mul_pow]
  have hmul := mul_le_mul_of_nonneg_left hbound (pow_nonneg hd.le degree)
  simpa only [d, mul_comm] using hmul

theorem astronomical_polynomial_bound (ell : ℕ) (hell : 2 ^ 1000 ≤ ell) :
    (ell : ℝ) ^ 20000 ≤ (2 : ℝ) ^ (ell / 2) := by
  let m0 : ℕ := 2 ^ 999
  have hbaseSize : (2 * (m0 : ℝ) + 1) ≤ (2 : ℝ) ^ 1001 := by
    have hm0 : (m0 : ℝ) = (2 : ℝ) ^ 999 := by
      simp only [m0, Nat.cast_pow, Nat.cast_ofNat]
    have hone : (1 : ℝ) ≤ m0 := by rw [hm0]; exact one_le_pow₀ (by norm_num)
    have hbig : (2 : ℝ) ^ 1001 = 4 * (m0 : ℝ) := by
      rw [show 1001 = 999 + 2 by decide, pow_add, ← hm0]
      norm_num only [pow_two]
      ring
    rw [hbig]
    calc
      2 * (m0 : ℝ) + 1 ≤ 2 * (m0 : ℝ) + m0 := add_le_add le_rfl hone
      _ = 3 * (m0 : ℝ) := by ring
      _ ≤ 4 * (m0 : ℝ) := mul_le_mul_of_nonneg_right (by norm_num)
        ((by norm_num : (0 : ℝ) ≤ 1).trans hone)
  have hbasePower := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * (m0 : ℝ) + 1)
    hbaseSize 20000
  rw [← pow_mul] at hbasePower
  have hexponent : 1001 * 20000 ≤ m0 := by
    have hsmall : 1001 * 20000 ≤ (2 : ℕ) ^ 25 := by norm_num
    exact hsmall.trans (pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (by decide : 25 ≤ 999))
  have hbase : (2 * (m0 : ℝ) + 1) ^ 20000 ≤ (2 : ℝ) ^ m0 :=
    hbasePower.trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexponent)
  have hgrowth : ∀ m : ℕ, m0 ≤ m → (2 * (m : ℝ) + 1) ^ 20000 ≤ (2 : ℝ) ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hbase
    | succ m hm ih =>
      have hsize0 : 4 * 20000 ≤ 2 * m0 + 1 := by omega
      have hstep := polynomial_binary_growth_step 20000 m (by omega)
      calc
        (2 * ((m + 1 : ℕ) : ℝ) + 1) ^ 20000 = (2 * (m : ℝ) + 3) ^ 20000 := by
          congr 1
          push_cast
          ring
        _ ≤ 2 * (2 * (m : ℝ) + 1) ^ 20000 := hstep
        _ ≤ 2 * (2 : ℝ) ^ m := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 : ℝ) ^ (m + 1) := by rw [pow_succ]; ring
  have hcutoff : 2 ^ 1000 = 2 * m0 := by
    dsimp only [m0]
    rw [show 1000 = 999 + 1 by decide, pow_succ]
    exact Nat.mul_comm _ _
  have hm : m0 ≤ ell / 2 := by omega
  have hellR : (ell : ℝ) ≤ 2 * ((ell / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show ell ≤ 2 * (ell / 2) + 1 by omega)
  exact (pow_le_pow_left₀ (Nat.cast_nonneg ell) hellR 20000).trans (hgrowth _ hm)

theorem astronomical_parameter_slack (ell : ℕ) (H : ℝ)
    (hell : 2 ^ 1000 ≤ ell) (hH : (2 : ℝ) ^ (ell / 2) ≤ H) :
    (ell : ℝ) ^ 20000 ≤ H :=
  (astronomical_polynomial_bound ell hell).trans hH

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Integer-computed parameters

The logarithms and fourth roots in Section 2 are computed by natural bit
lengths and nested integer square roots. No real arithmetic oracle is
used to form the algorithm's parameters.
-/

namespace EditApproximation
















theorem inputSmallLog_bounds (N : ℕ) (hN : 0 < N) :
    heightExponent N ≤ inputSmallLog N ∧ inputSmallLog N < 2 * heightExponent N := by
  have hpos := heightExponent_pos N hN
  have hone : 1 ≤ heightExponent N := hpos
  have hrange := rejectionWord_range (heightExponent N) hpos
  simpa only [inputSmallLog, smallLogExponent, rejectionBitCount, max_eq_right hone] using hrange

theorem inputHeight_binary_slack (N : ℕ) (hN : 0 < N) :
    (2 : ℝ) ^ (inputSmallLog N / 2) ≤ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hexponent : inputSmallLog N / 2 ≤ heightExponent N := by omega
  have hpower := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexponent
  simpa only [inputHeight, Nat.cast_pow, Nat.cast_ofNat] using hpower

theorem inputHeight_polynomial_slack (N : ℕ) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) :
    (inputSmallLog N : ℝ) ^ 20000 ≤ inputHeight N :=
  astronomical_parameter_slack _ _ hell (inputHeight_binary_slack N hN)

theorem coarseExponent_fourth_power (ell : ℕ) :
    coarseExponent ell ^ 4 ≤ Nat.log 2 ell := by
  have ha := Nat.sqrt_le' (Nat.sqrt (Nat.log 2 ell))
  have hb := Nat.sqrt_le' (Nat.log 2 ell)
  have hsq := Nat.pow_le_pow_left ha 2
  rw [← pow_mul] at hsq
  exact hsq.trans hb

theorem coarseExponent_maximal (ell p : ℕ) (hp : p ^ 4 ≤ Nat.log 2 ell) :
    p ≤ coarseExponent ell := by
  apply Nat.le_sqrt'.2
  apply Nat.le_sqrt'.2
  simpa only [← pow_mul] using hp

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_AccuracyCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A computable fixed-accuracy cutoff. The algorithm tests the small-log
conditions directly; it does not construct the double exponential bound. -/

namespace EditApproximation





theorem heightExponent_above_double_power (N exponent : ℕ) (h : 2 ^ (2 ^ exponent) ≤ N) :
    exponent ≤ heightExponent N := by
  have hfirst := Nat.clog_mono_right 2 (h.trans (Nat.le_add_right N 2))
  rw [Nat.clog_pow _ _ (by decide : 1 < (2 : ℕ))] at hfirst
  have hsecond := Nat.clog_mono_right 2 hfirst
  simpa only [Nat.clog_pow _ _ (by decide : 1 < (2 : ℕ)), heightExponent] using hsecond

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Growth of the computed parameters

These are scalar estimates for the literal integer parameters of Section 10.
They do not assert an evaluator cost: the recursive-input and charged local
work bounds must be connected to these estimates separately.
-/

namespace EditApproximation

open Filter
open scoped Topology

theorem heightExponent_tendsto : Tendsto heightExponent atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_ge_atTop (2 ^ (2 ^ b))] with N hN
  exact heightExponent_above_double_power N b hN

theorem inputSmallLog_tendsto : Tendsto inputSmallLog atTop atTop := by
  apply tendsto_atTop_mono' atTop _ heightExponent_tendsto
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (inputSmallLog_bounds N hN).1

theorem smallLogExponent_tendsto : Tendsto smallLogExponent atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [inputSmallLog_tendsto.eventually (eventually_ge_atTop (2 ^ b))]
    with N hN
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hN

theorem inputSmallLog_log_two (N : ℕ) :
    Nat.log 2 (inputSmallLog N) = smallLogExponent N := by
  exact Nat.log_pow (by decide : 1 < (2 : ℕ)) _

theorem coarseExponent_tendsto :
    Tendsto (fun N => coarseExponent (inputSmallLog N)) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [smallLogExponent_tendsto.eventually (eventually_ge_atTop (b ^ 4))]
    with N hN
  exact coarseExponent_maximal _ b ((inputSmallLog_log_two N).symm ▸ hN)

theorem coarseExponent_real_tendsto :
    Tendsto (fun N => (coarseExponent (inputSmallLog N) : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp coarseExponent_tendsto

theorem inputSmallLog_real_log (N : ℕ) :
    Real.log (inputSmallLog N : ℝ) = (smallLogExponent N : ℝ) * Real.log 2 := by
  simp only [inputSmallLog, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

theorem shifted_square_log_bound (p f : ℝ) (hpR : 1 ≤ p) (hfour : p ^ 4 ≤ f) :
    (p + 1) ^ 2 / (f * Real.log 2) ≤ 4 / (Real.log 2 * p ^ 2) := by
  have hsquare : (p + 1) ^ 2 ≤ 4 * p ^ 2 := by nlinarith
  have hproduct : (p + 1) ^ 2 * p ^ 2 ≤ 4 * f := by
    have hm := mul_le_mul_of_nonneg_right hsquare (sq_nonneg p)
    nlinarith
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hf : 0 < f := by nlinarith [sq_nonneg (p ^ 2)]
  apply (div_le_div_iff₀ (mul_pos hf hlogtwo)
    (mul_pos hlogtwo (sq_pos_of_pos (by linarith : 0 < p)))).2
  nlinarith [mul_le_mul_of_nonneg_right hproduct hlogtwo.le]

theorem coarse_shifted_square_log_bound (N : ℕ)
    (hp : 1 ≤ coarseExponent (inputSmallLog N)) :
    ((coarseExponent (inputSmallLog N) : ℝ) + 1) ^ 2 /
        Real.log (inputSmallLog N : ℝ) ≤
      4 / (Real.log 2 * (coarseExponent (inputSmallLog N) : ℝ) ^ 2) := by
  rw [inputSmallLog_real_log]
  apply shifted_square_log_bound
  · exact_mod_cast hp
  · have hnat := coarseExponent_fourth_power (inputSmallLog N)
    rw [inputSmallLog_log_two] at hnat
    exact_mod_cast hnat

/-- The central earlier-index dependency exponent in Section 10 is sublinear. -/
theorem coarse_shifted_square_div_log_tendsto :
    Tendsto (fun N => ((coarseExponent (inputSmallLog N) : ℝ) + 1) ^ 2 /
      Real.log (inputSmallLog N : ℝ)) atTop (𝓝 0) := by
  have hupper : Tendsto (fun N =>
      4 / (Real.log 2 * (coarseExponent (inputSmallLog N) : ℝ) ^ 2)) atTop (𝓝 0) := by
    have h := (coarseExponent_real_tendsto.inv_tendsto_atTop.pow 2).const_mul (4 / Real.log 2)
    convert h using 1
    · ext N
      simp only [Pi.inv_apply, div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring
    · simp
  apply squeeze_zero' _ _ hupper
  · filter_upwards [smallLogExponent_tendsto.eventually (eventually_ge_atTop 1)] with N hN
    apply div_nonneg (sq_nonneg _)
    rw [inputSmallLog_real_log]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  · filter_upwards [coarseExponent_tendsto.eventually (eventually_ge_atTop 1)] with N hN
    exact coarse_shifted_square_log_bound N hN

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterLocalAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar bounds for the local enumeration exponent. -/

namespace EditApproximation

open Filter
open scoped Topology

/-- Every fixed polynomial in the computed small logarithm is negligible
relative to the computed height. -/
theorem smallLog_polynomial_div_height_tendsto (k : ℕ) :
    Tendsto (fun N => (inputSmallLog N : ℝ) ^ k / inputHeight N) atTop (𝓝 0) := by
  have hupper : Tendsto (fun N => (2 : ℝ) ^ k *
      ((heightExponent N : ℝ) ^ k / (2 : ℝ) ^ heightExponent N)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)).comp
        heightExponent_tendsto).const_mul ((2 : ℝ) ^ k)
  apply squeeze_zero' (Eventually.of_forall fun N =>
    div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)) _ hupper
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hbound : (inputSmallLog N : ℝ) ≤ 2 * (heightExponent N : ℝ) := by
    exact_mod_cast (inputSmallLog_bounds N hN).2.le
  have hpower := pow_le_pow_left₀ (Nat.cast_nonneg (inputSmallLog N)) hbound k
  simpa only [inputHeight, Nat.cast_pow, Nat.cast_ofNat, mul_pow, mul_div_assoc] using
    div_le_div_of_nonneg_right hpower (by positivity : (0 : ℝ) ≤ 2 ^ heightExponent N)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SeedFactorSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The literal dyadic factor schedule stops at A<=F. Each active pass
replaces A by 4A/F and uses the integer factor a=A/F. -/

namespace EditApproximation




theorem dyadicSeedPassCount_le (f initial : ℕ) (hf : 3 ≤ f) :
    dyadicSeedPassCount f initial ≤ initial / (f - 2) + 1 := by
  have hd : 0 < f - 2 := by omega
  apply (ceilDiv_le_iff_le_mul hd).2
  have hfloor := Nat.lt_mul_div_succ initial hd
  nlinarith only [hfloor, show initial - f ≤ initial from Nat.sub_le _ _]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedStageTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact divisibility and power bounds for the computed time counts. -/

namespace EditApproximation

theorem computed_refinement_count_exact (N : ℕ) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) :
    (integerParameters N).S * inputSmallLog N ^ 2 = inputHeight N := by
  have hellone : (1 : ℝ) ≤ inputSmallLog N := by exact_mod_cast (Nat.one_le_two_pow (n := smallLogExponent N))
  have hpowR := (pow_le_pow_right₀ hellone (by decide : 2 ≤ 20000)).trans
    (inputHeight_polynomial_slack N hN hell)
  have hpow : inputSmallLog N ^ 2 ≤ inputHeight N := by exact_mod_cast hpowR
  have hexponent : smallLogExponent N * 2 ≤ heightExponent N := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1
    simpa only [inputSmallLog, inputHeight, ← pow_mul] using hpow
  have hdiv : inputSmallLog N ^ 2 ∣ inputHeight N := by
    simpa only [inputSmallLog, inputHeight, ← pow_mul] using Nat.pow_dvd_pow 2 hexponent
  exact Nat.div_mul_cancel hdiv

theorem computed_warmup_count_power (N : ℕ) :
    inputHeight N ^ 3 ≤ (integerParameters N).T ^ 4 ∧
      (integerParameters N).T ^ 4 ≤ 16 * inputHeight N ^ 3 := by
  let k := heightExponent N
  have hlow : 3 * k ≤ ((3 * k + 3) / 4) * 4 := by omega
  have hhigh : ((3 * k + 3) / 4) * 4 ≤ 3 * k + 4 := by omega
  constructor
  · simpa only [integerParameters, inputHeight, ← pow_mul, k, mul_comm] using
      pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hlow
  · have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hhigh
    simpa only [integerParameters, inputHeight, ← pow_mul, pow_add, k,
      show (2 : ℕ) ^ 4 = 16 by norm_num, mul_comm] using h

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterDependencyAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual pass/index count and the exponents in the dependency-path
bound. These statements concern computed numbers, independently of the
proof that an evaluator satisfies the dependency budgets. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem le_fourth_root_of_fourth_power_le {x y : ℝ} (h : x ^ 4 ≤ y) :
    x ≤ Real.sqrt (Real.sqrt y) := by
  apply Real.le_sqrt_of_sq_le
  apply Real.le_sqrt_of_sq_le
  simpa only [← pow_mul] using h

theorem warmup_smallLog_square_div_height_tendsto :
    Tendsto (fun N => ((integerParameters N).T : ℝ) * (inputSmallLog N : ℝ) ^ 2 /
      inputHeight N) atTop (𝓝 0) := by
  have hupper : Tendsto (fun N => Real.sqrt (Real.sqrt
      (16 * ((inputSmallLog N : ℝ) ^ 8 / inputHeight N)))) atTop (𝓝 0) := by
    simpa only [mul_zero, Real.sqrt_zero] using
      ((smallLog_polynomial_div_height_tendsto 8).const_mul 16).sqrt.sqrt
  apply squeeze_zero' (Eventually.of_forall fun N => by positivity) _ hupper
  apply Eventually.of_forall
  intro N
  apply le_fourth_root_of_fourth_power_le
  have hH : (0 : ℝ) < inputHeight N := by exact_mod_cast Nat.two_pow_pos (heightExponent N)
  have hT : ((integerParameters N).T : ℝ) ^ 4 ≤ 16 * (inputHeight N : ℝ) ^ 3 := by
    exact_mod_cast (computed_warmup_count_power N).2
  have hmul := mul_le_mul_of_nonneg_right hT
    (pow_nonneg (Nat.cast_nonneg (inputSmallLog N)) 8)
  rw [div_pow, mul_pow, ← pow_mul]
  apply (div_le_iff₀ (pow_pos hH 4)).2
  calc
    ((integerParameters N).T : ℝ) ^ 4 * (inputSmallLog N : ℝ) ^ 8 ≤
        16 * (inputHeight N : ℝ) ^ 3 * (inputSmallLog N : ℝ) ^ 8 := hmul
    _ = (16 * ((inputSmallLog N : ℝ) ^ 8 / inputHeight N)) *
        (inputHeight N : ℝ) ^ 4 := by field_simp [hH.ne']

theorem computed_warmup_le_refinement_eventually :
    ∀ᶠ N in atTop, (integerParameters N).T ≤ (integerParameters N).S ∧
      1 ≤ (integerParameters N).S := by
  have hratio := warmup_smallLog_square_div_height_tendsto.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hratio, eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop (2 ^ 1000))] with N hratio hN hell
  have hcount := computed_refinement_count_exact N hN hell
  have hH : (0 : ℝ) < inputHeight N := by exact_mod_cast Nat.two_pow_pos (heightExponent N)
  have hproduct : ((integerParameters N).T : ℝ) * (inputSmallLog N : ℝ) ^ 2 < inputHeight N :=
    (div_lt_one hH).1 hratio
  have hT : (integerParameters N).T < (integerParameters N).S := by
    have hproductN : (integerParameters N).T * inputSmallLog N ^ 2 < inputHeight N := by
      exact_mod_cast hproduct
    rw [← hcount] at hproductN
    exact Nat.lt_of_mul_lt_mul_right hproductN
  exact ⟨hT.le, by omega⟩

theorem scalar_pass_count_bound (p e ell f K : ℝ)
    (hp : 0 ≤ p) (hf : 4 ≤ f) (helf : f ≤ ell) (heel : e ≤ ell)
    (hK : K ≤ (p + 4) * e / (f - 2) + 2) :
    K ≤ 10 * (p + 1) * ell / f := by
  have hfpos : 0 < f := by linarith
  have hden : 0 < f - 2 := by linarith
  have hqell : 0 ≤ (p + 1) * ell := mul_nonneg (by linarith) (by linarith)
  have hnum : (p + 4) * e ≤ 4 * (p + 1) * ell := by
    have h := mul_le_mul_of_nonneg_left heel (by linarith : 0 ≤ p + 4)
    nlinarith [mul_nonneg hp (show 0 ≤ ell by linarith)]
  have hmain : (p + 4) * e / (f - 2) ≤ 8 * (p + 1) * ell / f := by
    apply (div_le_div_iff₀ hden hfpos).2
    have hnumf := mul_le_mul_of_nonneg_right hnum hfpos.le
    have hslack := mul_nonneg hqell (show 0 ≤ f - 4 by linarith)
    nlinarith
  have hconst : 2 ≤ 2 * (p + 1) * ell / f := by
    apply (le_div_iff₀ hfpos).2
    nlinarith [mul_nonneg hp (show 0 ≤ ell by linarith)]
  calc
    K ≤ (p + 4) * e / (f - 2) + 2 := hK
    _ ≤ 8 * (p + 1) * ell / f + 2 * (p + 1) * ell / f := add_le_add hmain hconst
    _ = 10 * (p + 1) * ell / f := by ring

theorem computed_pass_count_bound (N : ℕ) (hN : 0 < N) (hf : 4 ≤ smallLogExponent N) :
    (computedSeedPassCount N + 1 : ℝ) ≤
      10 * ((coarseExponent (inputSmallLog N) : ℝ) + 1) * inputSmallLog N / smallLogExponent N := by
  apply scalar_pass_count_bound (e := (heightExponent N : ℝ))
  · exact Nat.cast_nonneg _
  · exact_mod_cast hf
  · have h := (Nat.lt_pow_self (by decide : 1 < (2 : ℕ)) (n := smallLogExponent N)).le
    exact_mod_cast h
  · exact_mod_cast (inputSmallLog_bounds N hN).1
  · have hraw := dyadicSeedPassCount_le (smallLogExponent N) (computedSeedInitialExponent N) (by omega)
    have hcast : (computedSeedPassCount N : ℝ) ≤
        ((computedSeedInitialExponent N / (smallLogExponent N - 2) : ℕ) : ℝ) + 1 := by
      exact_mod_cast hraw
    have hdiv : ((computedSeedInitialExponent N / (smallLogExponent N - 2) : ℕ) : ℝ) ≤
        (computedSeedInitialExponent N : ℝ) / (smallLogExponent N - 2 : ℕ) := Nat.cast_div_le
    have hden : ((smallLogExponent N - 2 : ℕ) : ℝ) = (smallLogExponent N : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ smallLogExponent N)]
      norm_num
    rw [hden] at hdiv
    have hexp : (computedSeedInitialExponent N : ℝ) =
        ((coarseExponent (inputSmallLog N) : ℝ) + 4) * heightExponent N := by
      simp only [computedSeedInitialExponent, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    rw [hexp] at hdiv
    linarith

theorem scalar_dependency_index_bound (p ell f H S T K : ℝ)
    (hell : 0 < ell) (hf : 0 < f) (hS : 1 ≤ S) (hT : T ≤ S)
    (hK : 0 ≤ K) (hcount : S * ell ^ 2 = H)
    (hpass : K ≤ 10 * (p + 1) * ell / f) :
    K * (T + S + 1) ≤ 30 * H * (p + 1) / (ell * f) := by
  calc
    K * (T + S + 1) ≤ K * (3 * S) := mul_le_mul_of_nonneg_left (by linarith) hK
    _ ≤ (10 * (p + 1) * ell / f) * (3 * S) :=
      mul_le_mul_of_nonneg_right hpass (by linarith)
    _ = 30 * H * (p + 1) / (ell * f) := by
      rw [← hcount]
      field_simp [hell.ne', hf.ne']
      ring

theorem computed_dependency_index_bound_eventually :
    ∀ᶠ N in atTop, (computedDependencyIndexCount N : ℝ) ≤
      30 * (inputHeight N : ℝ) * ((coarseExponent (inputSmallLog N) : ℝ) + 1) /
        ((inputSmallLog N : ℝ) * smallLogExponent N) := by
  filter_upwards [computed_warmup_le_refinement_eventually, eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop (2 ^ 1000)),
    smallLogExponent_tendsto.eventually (eventually_ge_atTop 4)] with N htime hN hell hf
  have h := scalar_dependency_index_bound
    (coarseExponent (inputSmallLog N)) (inputSmallLog N) (smallLogExponent N)
    (inputHeight N) ((integerParameters N).S) ((integerParameters N).T)
    (computedSeedPassCount N + 1)
    (by exact_mod_cast Nat.two_pow_pos (smallLogExponent N))
    (by exact_mod_cast (show 0 < smallLogExponent N by omega))
    (by exact_mod_cast htime.2) (by exact_mod_cast htime.1) (by positivity)
    (by exact_mod_cast computed_refinement_count_exact N hN hell)
    (computed_pass_count_bound N hN hf)
  simpa only [computedDependencyIndexCount, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using h

theorem coarse_shifted_square_div_smallExponent_tendsto :
    Tendsto (fun N => ((coarseExponent (inputSmallLog N) : ℝ) + 1) ^ 2 /
      smallLogExponent N) atTop (𝓝 0) := by
  have h := coarse_shifted_square_div_log_tendsto.const_mul (Real.log 2)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [smallLogExponent_tendsto.eventually (eventually_ge_atTop 1)] with N hf
  rw [inputSmallLog_real_log]
  have hfn : (smallLogExponent N : ℝ) ≠ 0 := by exact_mod_cast (show smallLogExponent N ≠ 0 by omega)
  have hc : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  field_simp [hfn, hc]

theorem scalar_weighted_dependency_bound (q k e ell f H c : ℝ)
    (hq : 0 ≤ q) (hk : 0 ≤ k) (heel : e ≤ ell)
    (hell : 0 < ell) (hf : 0 < f) (hH : 0 < H) (hc : 0 ≤ c)
    (hbound : k ≤ 30 * H * q / (ell * f)) :
    q * k * (e * c) / H ≤ 30 * c * q ^ 2 / f := by
  have hproduct : k * (ell * f) ≤ 30 * H * q :=
    (le_div_iff₀ (mul_pos hell hf)).1 hbound
  apply (div_le_div_iff₀ hH hf).2
  calc
    q * k * (e * c) * f = k * (e * f) * (q * c) := by ring
    _ ≤ k * (ell * f) * (q * c) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hq hc)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right heel hf.le) hk
    _ ≤ (30 * H * q) * (q * c) := mul_le_mul_of_nonneg_right hproduct (mul_nonneg hq hc)
    _ = 30 * c * q ^ 2 * H := by ring

/-- The exponent of the earlier-index branching factor is `o(H)`. -/
theorem weighted_dependency_div_height_tendsto_oai :
    Tendsto (fun N => ((coarseExponent (inputSmallLog N) : ℝ) + 1) *
      computedDependencyIndexCount N * Real.log (inputHeight N : ℝ) / inputHeight N)
      atTop (𝓝 0) := by
  have hupper := coarse_shifted_square_div_smallExponent_tendsto.const_mul (30 * Real.log 2)
  simp only [mul_zero] at hupper
  apply squeeze_zero' (Eventually.of_forall fun N => by
    apply div_nonneg
    · apply mul_nonneg (by positivity)
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_two_pow (n := heightExponent N)
    · exact Nat.cast_nonneg _) _ hupper
  filter_upwards [computed_dependency_index_bound_eventually, eventually_ge_atTop 1,
    smallLogExponent_tendsto.eventually (eventually_ge_atTop 1)] with N hbound hN hf
  have hlog : Real.log (inputHeight N : ℝ) = (heightExponent N : ℝ) * Real.log 2 := by
    simp only [inputHeight, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  rw [hlog]
  simpa only [mul_div_assoc] using scalar_weighted_dependency_bound
    ((coarseExponent (inputSmallLog N) : ℝ) + 1) (computedDependencyIndexCount N)
    (heightExponent N) (inputSmallLog N) (smallLogExponent N) (inputHeight N) (Real.log 2)
    (by positivity) (Nat.cast_nonneg _)
    (by exact_mod_cast (inputSmallLog_bounds N hN).1)
    (by exact_mod_cast Nat.two_pow_pos (smallLogExponent N))
    (by exact_mod_cast (show 0 < smallLogExponent N by omega))
    (by exact_mod_cast Nat.two_pow_pos (heightExponent N))
    (Real.log_nonneg (by norm_num)) hbound

end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.weighted_dependency_div_height_tendsto_oai := @OAI.EditApproximation.weighted_dependency_div_height_tendsto_oai
