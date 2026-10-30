-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.eventually_residual_inverse_target
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:37:17.700241+00:00
-- url     : https://prove2.me/submissions/312af428-5b8b-4910-8ccf-0b2c35762bc9

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S003
import Definitions.Def_OAIQ081S006

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpExponentArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Growing-parameter exponent arithmetic

All factors in this module are actual real powers. The bounds expose the
growing parameters; they assert no program-running-time fact.
-/

namespace SubexponentialSAT.SubexpExponentArithmetic

noncomputable section
open Filter
open scoped Topology

theorem logb_lt_natLog2_add_one (n : ℕ) :
    Real.logb 2 (n : ℝ) < (Nat.log2 n : ℝ) + 1 := by
  have hf : ⌊Real.logb 2 (n : ℝ)⌋₊ = Nat.log2 n := by
    rw [Nat.log2_eq_log_two]
    exact Real.natFloor_logb_natCast 2 n
  simpa only [hf] using
    (Nat.lt_floor_add_one (Real.logb 2 (n : ℝ)))

end
end SubexponentialSAT.SubexpExponentArithmetic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRuntime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Uniform runtime assembly with growing layout parameters

Unlike the older fixed-width-exponent accounting, all layout parameters are
input-dependent here. `GrowingParameters.entries` exposes every argument of
the polynomial costs in Proposition 4.2 and the layout construction. The
analytic lemmas also pay for the variable-degree sunflower search.

Only the purely numerical work/trace infrastructure from `RuntimeAssembly`
is reused; none of its fixed-prime or exponent-0.9 estimates is used.
-/

namespace SubexponentialSAT.SubexpRuntime

open Filter
open scoped Topology

noncomputable section

/-- Any fixed power of log is eventually dominated by the input size, with
an arbitrary fixed positive coefficient and the source's shift by sixteen. -/
theorem eventually_logb_power_le (q : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℝ in atTop, C * (Real.logb 2 (n + 16)) ^ q ≤ n := by
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hp : 0 < (Real.log (2 : ℝ)) ^ q := pow_pos hl q
  have ht : Tendsto (fun n : ℝ => n + 16) atTop atTop :=
    tendsto_id.atTop_add tendsto_const_nhds
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := q)).bound
    (show 0 < (Real.log (2 : ℝ)) ^ q / (2 * C) by positivity)
  filter_upwards [ht.eventually hsmall, eventually_ge_atTop (16 : ℝ)] with n hb hn
  have hn0 : 0 ≤ n + 16 := by linarith
  have hlog0 : 0 ≤ Real.log (n + 16) := Real.log_nonneg (by linarith)
  have hb' : (Real.log (n + 16)) ^ q ≤
      (Real.log (2 : ℝ)) ^ q / (2 * C) * (n + 16) := by
    simpa only [Function.id_def, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hlog0 q), abs_of_nonneg hn0] using hb
  have hmul : C * (Real.log (n + 16)) ^ q ≤
      (Real.log (2 : ℝ)) ^ q * ((n + 16) / 2) := by
    calc
      C * (Real.log (n + 16)) ^ q ≤
          C * ((Real.log (2 : ℝ)) ^ q / (2 * C) * (n + 16)) :=
        mul_le_mul_of_nonneg_left hb' hC.le
      _ = (Real.log (2 : ℝ)) ^ q * ((n + 16) / 2) := by
        field_simp
  calc
    C * (Real.logb 2 (n + 16)) ^ q =
        (C * (Real.log (n + 16)) ^ q) / (Real.log (2 : ℝ)) ^ q := by
      unfold Real.logb
      rw [div_pow]
      ring
    _ ≤ (n + 16) / 2 := (div_le_iff₀ hp).mpr (by nlinarith [hmul])
    _ ≤ n := by linarith

end
end SubexponentialSAT.SubexpRuntime

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact, computable square-root-log scheduling. No algorithmic assertion is
hidden in these numerical lemmas. Small inputs may have schedule zero. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem w_pos (n : ℕ) : 0 < w n := by unfold w; omega

theorem le_s_iff (n a : ℕ) : a ≤ s n ↔ a ^ 2 * w n ^ 4 ≤ L n := by
  rw [s, Nat.le_div_iff_mul_le (pow_pos (w_pos n) 2), Nat.le_sqrt']
  ring_nf

theorem schedule_maximal (n : ℕ) : L n < (s n + 1) ^ 2 * w n ^ 4 := by
  have h := (le_s_iff n (s n + 1)).not
  exact Nat.lt_of_not_ge (h.mp (by omega))

theorem four_le_logSize (n : ℕ) : 4 ≤ logSize n := by
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : 0 < (n : ℝ) + 16)).mpr
  norm_num

theorem two_le_logLogSize (n : ℕ) : 2 ≤ logLogSize n := by
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
    (by have := four_le_logSize n; linarith : 0 < logSize n)).mpr
  norm_num
  exact four_le_logSize n

theorem logSize_lt_L (n : ℕ) : logSize n < (L n : ℝ) := by
  simpa [logSize, L, Nat.cast_add, Nat.cast_ofNat] using
    SubexpExponentArithmetic.logb_lt_natLog2_add_one (n + 16)

theorem L_le_logSize_add_one (n : ℕ) : (L n : ℝ) ≤ logSize n + 1 := by
  have h := Real.natLog_le_logb (n + 16) 2
  simpa [L, logSize, Nat.log2_eq_log_two, Nat.cast_add] using add_le_add_right h 1

theorem L_le_twice_logSize (n : ℕ) : (L n : ℝ) ≤ 2 * logSize n := by
  have := L_le_logSize_add_one n
  have := four_le_logSize n
  linarith

theorem w_le_twice_logLogSize (n : ℕ) : (w n : ℝ) ≤ 2 * logLogSize n := by
  have hp : (0 : ℝ) < logSize n := by have := four_le_logSize n; linarith
  have hL : (0 : ℝ) < L n := by exact_mod_cast L_pos n
  have hn := Real.natLog_le_logb (L n) 2
  have hlog : Real.logb 2 (L n : ℝ) ≤ 1 + logLogSize n := by
    calc
      Real.logb 2 (L n : ℝ) ≤ Real.logb 2 (2 * logSize n) :=
        Real.logb_le_logb_of_le (by norm_num) hL (L_le_twice_logSize n)
      _ = 1 + logLogSize n := by
        rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) hp.ne']
        norm_num [logLogSize]
  have hw : (w n : ℝ) ≤ Real.logb 2 (L n : ℝ) + 1 := by
    simpa [w, Nat.log2_eq_log_two] using add_le_add_right hn 1
  have := two_le_logLogSize n
  linarith

theorem logSize_tendsto : Tendsto logSize atTop atTop := by
  exact (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)

theorem eventually_le_s (a : ℕ) : ∀ᶠ n : ℕ in atTop, a ≤ s n := by
  have hb := logSize_tendsto.eventually
    (SubexpRuntime.eventually_logb_power_le 4
      (show (0 : ℝ) < ((a : ℝ) + 1) ^ 2 * 16 by positivity))
  filter_upwards [hb] with n hn
  have hw : (w n : ℝ) ≤ 2 * Real.logb 2 (logSize n + 16) := by
    have hm : logLogSize n ≤ Real.logb 2 (logSize n + 16) :=
      Real.logb_le_logb_of_le (by norm_num)
        (by have := four_le_logSize n; linarith) (by linarith)
    exact (w_le_twice_logLogSize n).trans (by linarith)
  have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ w n by positivity) hw 4
  have ha : (a : ℝ) ^ 2 * (w n : ℝ) ^ 4 ≤ (L n : ℝ) := by
    calc
      (a : ℝ) ^ 2 * (w n : ℝ) ^ 4 ≤
          ((a : ℝ) + 1) ^ 2 * (2 * Real.logb 2 (logSize n + 16)) ^ 4 := by
        apply mul_le_mul
        · nlinarith [Nat.cast_nonneg (α := ℝ) a]
        · exact hp
        · positivity
        · positivity
      _ = (((a : ℝ) + 1) ^ 2 * 16) * Real.logb 2 (logSize n + 16) ^ 4 := by ring_nf
      _ ≤ logSize n := hn
      _ ≤ (L n : ℝ) := (logSize_lt_L n).le
  exact (le_s_iff n a).mpr (by exact_mod_cast ha)

/-- An explicit lower-bound comparison, with the only small-input condition
being positivity of the actual integer schedule. -/
theorem sqrt_logSize_le (n : ℕ) (hs : 1 ≤ s n) :
    Real.sqrt (logSize n) ≤ 8 * (s n : ℝ) * logLogSize n ^ 2 := by
  have ht := four_le_logSize n
  have hW := two_le_logLogSize n
  have hs' : (1 : ℝ) ≤ s n := by exact_mod_cast hs
  have hm : (L n : ℝ) < ((s n : ℝ) + 1) ^ 2 * (w n : ℝ) ^ 4 := by
    exact_mod_cast schedule_maximal n
  have hroot := Real.sq_sqrt (show 0 ≤ logSize n by linarith)
  have hr0 := Real.sqrt_nonneg (logSize n)
  have hw0 : (0 : ℝ) ≤ w n := by positivity
  have hw := w_le_twice_logLogSize n
  have hw2 : (w n : ℝ) ^ 2 ≤ 4 * logLogSize n ^ 2 := by nlinarith
  have hfirst : Real.sqrt (logSize n) ≤ ((s n : ℝ) + 1) * (w n : ℝ) ^ 2 := by
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, ?_⟩
    calc
      logSize n ≤ (L n : ℝ) := (logSize_lt_L n).le
      _ ≤ ((s n : ℝ) + 1) ^ 2 * (w n : ℝ) ^ 4 := hm.le
      _ = (((s n : ℝ) + 1) * (w n : ℝ) ^ 2) ^ 2 := by ring_nf
  have hmul := mul_le_mul_of_nonneg_left hw2 (show 0 ≤ (s n : ℝ) + 1 by positivity)
  nlinarith [sq_nonneg (logLogSize n)]

theorem inverse_schedule_le (n : ℕ) (hs : 1 ≤ s n) :
    (n : ℝ) / s n ≤ 8 * binaryScale n := by
  have hs' : (0 : ℝ) < s n := by exact_mod_cast (by omega : 0 < s n)
  have ht : 0 < Real.sqrt (logSize n) :=
    Real.sqrt_pos.2 (by have := four_le_logSize n; linarith)
  have h := mul_le_mul_of_nonneg_left (sqrt_logSize_le n hs) (Nat.cast_nonneg n)
  unfold binaryScale
  rw [show 8 * ((n : ℝ) * logLogSize n ^ 2 / Real.sqrt (logSize n)) =
    (8 * (n : ℝ) * logLogSize n ^ 2) / Real.sqrt (logSize n) by ring_nf]
  apply (div_le_div_iff₀ hs' ht).2
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring_nf

theorem eventually_inverse_schedule_le :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / s n ≤ 8 * binaryScale n := by
  filter_upwards [eventually_le_s 1] with n hn
  exact inverse_schedule_le n hn

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_StatementScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The exact square-root-logarithm runtime scale

These are numerical definitions and elementary lemmas only.  In particular,
this module supplies no SAT algorithm and makes no computational existence claim.
The logarithms in the target are natural logarithms, including at small inputs.
-/

namespace SubexponentialSAT.SqrtLog.Statement

noncomputable section

theorem two_le_log_shift (n : ℕ) : 2 ≤ Real.log ((n : ℝ) + 16) := by
  have htwo : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hpow := Real.log_pow (2 : ℝ) 4
  norm_num at hpow
  have hmon : Real.log 16 ≤ Real.log ((n : ℝ) + 16) :=
    Real.log_le_log (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  linarith

theorem log_shift_pos (n : ℕ) : 0 < Real.log ((n : ℝ) + 16) := by
  have := two_le_log_shift n
  linarith

theorem log_log_shift_pos (n : ℕ) : 0 < Real.log (Real.log ((n : ℝ) + 16)) :=
  Real.log_pos (lt_of_lt_of_le (by norm_num) (two_le_log_shift n))

theorem sqrt_log_shift_pos (n : ℕ) : 0 < Real.sqrt (Real.log ((n : ℝ) + 16)) :=
  Real.sqrt_pos.2 (log_shift_pos n)

end

end SubexponentialSAT.SqrtLog.Statement

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Conversion to the exact natural-logarithm target and absorption of
fixed polylogarithmic construction, search, and arithmetic overheads. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem log_two_bounds : (1 : ℝ) / 2 ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  · have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h

theorem logSize_natural_bounds (n : ℕ) :
    Real.log ((n : ℝ) + 16) ≤ logSize n ∧
      logSize n ≤ 2 * Real.log ((n : ℝ) + 16) := by
  have hpos := Statement.log_shift_pos n
  have hb := log_two_bounds
  have htwo : 0 < Real.log (2 : ℝ) := by linarith
  unfold logSize Real.logb
  constructor
  · apply (le_div_iff₀ htwo).2
    nlinarith
  · apply (div_le_iff₀ htwo).2
    nlinarith

theorem logLogSize_le_natural (n : ℕ) :
    logLogSize n ≤ 4 * Real.log (Real.log ((n : ℝ) + 16)) := by
  have ha := Statement.two_le_log_shift n
  have hap := Statement.log_shift_pos n
  have hb := log_two_bounds
  have htwo : 0 < Real.log (2 : ℝ) := by linarith
  have hlog : Real.log 2 ≤ Real.log (Real.log ((n : ℝ) + 16)) :=
    Real.log_le_log (by norm_num) ha
  have ht : 0 < logSize n := by have := four_le_logSize n; linarith
  have htlog : Real.log (logSize n) ≤
      Real.log 2 + Real.log (Real.log ((n : ℝ) + 16)) := by
    calc
      Real.log (logSize n) ≤ Real.log (2 * Real.log ((n : ℝ) + 16)) :=
        Real.log_le_log ht (logSize_natural_bounds n).2
      _ = _ := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hap.ne'
  unfold logLogSize Real.logb
  apply (div_le_iff₀ htwo).2
  nlinarith

theorem binaryScale_le_target (n : ℕ) :
    binaryScale n ≤ 16 * Statement.runtimeScale n := by
  have hW := logLogSize_le_natural n
  have hW0 : 0 ≤ logLogSize n := by have := two_le_logLogSize n; linarith
  have hroot := Real.sqrt_le_sqrt (logSize_natural_bounds n).1
  have ha := Statement.sqrt_log_shift_pos n
  have hb : 0 < Real.sqrt (logSize n) := by linarith
  have hsq : logLogSize n ^ 2 ≤
      16 * Real.log (Real.log ((n : ℝ) + 16)) ^ 2 := by nlinarith
  unfold binaryScale Statement.runtimeScale
  calc
    (n : ℝ) * logLogSize n ^ 2 / Real.sqrt (logSize n) ≤
        (n : ℝ) * (16 * Real.log (Real.log ((n : ℝ) + 16)) ^ 2) /
          Real.sqrt (Real.log ((n : ℝ) + 16)) := by gcongr
    _ = _ := by ring

theorem eventually_inverse_schedule_target :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / s n ≤ 128 * Statement.runtimeScale n := by
  filter_upwards [eventually_inverse_schedule_le] with n hn
  have h := binaryScale_le_target n
  linarith

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticLayoutCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem eventually_layout_inverse_target :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / layoutR n ≤ 128 * Statement.runtimeScale n := by
  filter_upwards [eventually_inverse_schedule_target, eventually_le_s 1] with n hn hs
  have hs' : (0 : ℝ) < s n := by exact_mod_cast (by omega : 0 < s n)
  have hr : (s n : ℝ) ≤ layoutR n := by exact_mod_cast le_max_right 2 (s n)
  exact (div_le_div_of_nonneg_left (Nat.cast_nonneg n) hs' hr).trans hn

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticMonotone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact monotonicity of the stated runtime scale, including unused ambient
variables. These lemmas concern numbers, not a change in the input encoding. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

theorem mul_log_shift_le {a b : ℕ} (hab : a ≤ b) :
    (a : ℝ) * Real.log ((b : ℝ) + 16) ≤
      (b : ℝ) * Real.log ((a : ℝ) + 16) := by
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have ha : 0 < (a : ℝ) + 16 := by positivity
  have hb : 0 < (b : ℝ) + 16 := by positivity
  have hd : 0 ≤ Real.log ((b : ℝ) + 16) - Real.log ((a : ℝ) + 16) := by
    have h := Real.log_le_log ha (show (a : ℝ) + 16 ≤ (b : ℝ) + 16 by linarith)
    linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at h
  have hm : (Real.log ((b : ℝ) + 16) - Real.log ((a : ℝ) + 16) + 1) *
      ((a : ℝ) + 16) ≤ (b : ℝ) + 16 :=
    (le_div_iff₀ ha).mp (by linarith)
  have hla := Statement.two_le_log_shift a
  have hprod := mul_nonneg (sub_nonneg.mpr hab')
    (show 0 ≤ Real.log ((a : ℝ) + 16) - 1 by linarith)
  nlinarith

theorem div_sqrt_log_shift_mono {a b : ℕ} (hab : a ≤ b) :
    (a : ℝ) / Real.sqrt (Real.log ((a : ℝ) + 16)) ≤
      (b : ℝ) / Real.sqrt (Real.log ((b : ℝ) + 16)) := by
  have ha := Statement.sqrt_log_shift_pos a
  have hb := Statement.sqrt_log_shift_pos b
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hlog := mul_log_shift_le hab
  have ham := Real.sq_sqrt (Statement.log_shift_pos a).le
  have hbm := Real.sq_sqrt (Statement.log_shift_pos b).le
  have hsq : ((a : ℝ) * Real.sqrt (Real.log ((b : ℝ) + 16))) ^ 2 ≤
      ((b : ℝ) * Real.sqrt (Real.log ((a : ℝ) + 16))) ^ 2 := by
    rw [mul_pow, mul_pow, ham, hbm]
    have hm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg a)
    have hn := mul_nonneg (show (0 : ℝ) ≤ b - a by linarith)
      (mul_nonneg (Nat.cast_nonneg b) (Statement.log_shift_pos a).le)
    nlinarith
  apply (div_le_div_iff₀ ha hb).2
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq

theorem runtimeScale_mono : Monotone Statement.runtimeScale := by
  intro a b hab
  have hbase := div_sqrt_log_shift_mono hab
  have hinner : Real.log ((a : ℝ) + 16) ≤ Real.log ((b : ℝ) + 16) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.add_le_add_right hab 16
  have houter := Real.log_le_log (Statement.log_shift_pos a) hinner
  have hpow := pow_le_pow_left₀ (Statement.log_log_shift_pos a).le houter 2
  have hm := mul_le_mul hbase hpow (sq_nonneg _)
    (div_nonneg (Nat.cast_nonneg b) (Statement.sqrt_log_shift_pos b).le)
  simpa only [Statement.runtimeScale, div_mul_eq_mul_div] using hm

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform transport from the original dimension to a residual dimension
between one half and all of it. No lower bound on arbitrary residuals is
assumed: callers must supply the displayed half-dimension condition. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

/-- Eventual assertions are uniform over every residual dimension in the
half interval; in particular the residual may depend on a branch. -/
theorem eventually_uniform_half {P : ℕ → Prop} (hP : ∀ᶠ m in atTop, P m) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, n ≤ 2 * m → P m := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hP
  filter_upwards [eventually_ge_atTop (2 * N)] with n hn m hnm
  exact hN m (by omega)

theorem eventually_residual_inverse_target_oai :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, m ≤ n → n ≤ 2 * m →
      (n : ℝ) / layoutR m ≤ 256 * Statement.runtimeScale n := by
  filter_upwards [eventually_uniform_half eventually_layout_inverse_target] with n hn m hmn hnm
  have hlocal := hn m hnm
  have hnm' : (n : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hnm
  have hh := div_le_div_of_nonneg_right hnm' (show (0 : ℝ) ≤ layoutR m by positivity)
  have ht := runtimeScale_mono hmn
  calc
    _ ≤ 2 * ((m : ℝ) / layoutR m) := by simpa [mul_div_assoc] using hh
    _ ≤ 2 * (128 * Statement.runtimeScale m) := by gcongr
    _ ≤ 256 * Statement.runtimeScale n := by nlinarith

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.eventually_residual_inverse_target_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.eventually_residual_inverse_target_oai
