-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.eventually_uniform_label_log
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:38:18.556746+00:00
-- url     : https://prove2.me/submissions/140c8a8e-1846-4936-8bbe-2944674c5c95

import Mathlib
import Definitions.Def_OAIQ081S003

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

theorem s_le_L (n : ℕ) : s n ≤ L n :=
  (Nat.div_le_self _ _).trans (Nat.sqrt_le_self _)

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

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticOverhead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Absorption of all fixed polylogarithmic exponents. The quantifiers keep
the power and multiplicative constant independent of the input size. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem eventually_w_power_le_L (q : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, C * (w n : ℝ) ^ q ≤ L n := by
  have hb := logSize_tendsto.eventually
    (SubexpRuntime.eventually_logb_power_le q
      (show 0 < C * (2 : ℝ) ^ q by positivity))
  filter_upwards [hb] with n hn
  have hm : logLogSize n ≤ Real.logb 2 (logSize n + 16) :=
    Real.logb_le_logb_of_le (by norm_num)
      (by have := four_le_logSize n; linarith) (by linarith)
  have hw : (w n : ℝ) ≤ 2 * Real.logb 2 (logSize n + 16) :=
    (w_le_twice_logLogSize n).trans (by linarith)
  calc
    C * (w n : ℝ) ^ q ≤ C * (2 * Real.logb 2 (logSize n + 16)) ^ q :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hw q) hC.le
    _ = (C * (2 : ℝ) ^ q) * Real.logb 2 (logSize n + 16) ^ q := by
      rw [mul_pow]; ring
    _ ≤ logSize n := hn
    _ ≤ L n := (logSize_lt_L n).le

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

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticLayoutParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Integer layout parameters agreed with the layout and spectral components.
The occurrence bound `b` is an explicit argument. Positivity assumptions are
kept on theorems rather than built into an opaque choice. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem layoutDen_pos (n : ℕ) : 0 < layoutDen n := by
  unfold layoutDen
  positivity

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticLayoutBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem layoutR_le_L (n : ℕ) : layoutR n ≤ L n := by
  have h : (4 : ℝ) < L n := (four_le_logSize n).trans_lt (logSize_lt_L n)
  have hnat : 4 < L n := by exact_mod_cast h
  exact max_le (by omega) (s_le_L n)

theorem layoutDen_le (n : ℕ) : layoutDen n ≤ 64 * w n := by
  have h := Nat.log_mono_right (b := 2) (layoutR_le_L n)
  simpa only [layoutDen, w, Nat.log2_eq_log_two] using Nat.mul_le_mul_left 64
    (Nat.add_le_add_right h 1)

theorem layoutEnergy_le (n b q : ℕ) (hb : b ≤ L n ^ q) :
    layoutEnergy n b ≤ (q + 10) * w n := by
  have hL : L n ≤ 2 ^ w n := (Nat.lt_log2_self (n := L n)).le
  have hr := layoutR_le_L n
  have hz : 64 * b * layoutR n * L n ^ 2 ≤ 2 ^ (6 + w n * (q + 3)) := by
    calc
      64 * b * layoutR n * L n ^ 2 ≤ 64 * (L n ^ q) * L n * L n ^ 2 := by gcongr
      _ = 64 * L n ^ (q + 3) := by ring
      _ ≤ 64 * (2 ^ w n) ^ (q + 3) := by gcongr
      _ = 2 ^ (6 + w n * (q + 3)) := by rw [← pow_mul]; norm_num [pow_add]
  have hlog := Nat.log_mono_right (b := 2) hz
  rw [Nat.log_pow (by norm_num : 1 < (2 : ℕ))] at hlog
  have hw := w_pos n
  unfold layoutEnergy
  rw [Nat.log2_eq_log_two]
  nlinarith

theorem eventually_layoutQ_ge (a : ℕ) : ∀ᶠ n : ℕ in atTop, a ≤ layoutQ n := by
  have hh := eventually_w_power_le_L 1 (show (0 : ℝ) < 64 * ((a : ℝ) + 1) by positivity)
  filter_upwards [hh] with n hn
  simp only [pow_one] at hn
  have hh' : 64 * (a + 1) * w n ≤ L n := by exact_mod_cast hn
  have hd := layoutDen_le n
  apply (Nat.le_div_iff_mul_le (layoutDen_pos n)).2
  nlinarith

theorem eventually_layoutQ_energy_ratio (b : ℕ → ℕ) (q A : ℕ)
    (hb : ∀ᶠ n : ℕ in atTop, b n ≤ L n ^ q) :
    ∀ᶠ n : ℕ in atTop, A * layoutEnergy n (b n) ≤ layoutQ n := by
  have hh := eventually_w_power_le_L 2
    (show (0 : ℝ) < 64 * ((A : ℝ) + 1) * ((q : ℝ) + 10) by positivity)
  filter_upwards [hb, hh] with n hn hpow
  have hp : 64 * (A + 1) * (q + 10) * w n ^ 2 ≤ L n := by exact_mod_cast hpow
  have he := layoutEnergy_le n (b n) q hn
  have hd := layoutDen_le n
  apply (Nat.le_div_iff_mul_le (layoutDen_pos n)).2
  calc
    A * layoutEnergy n (b n) * layoutDen n ≤ A * ((q + 10) * w n) * (64 * w n) := by gcongr
    _ ≤ 64 * (A + 1) * (q + 10) * w n ^ 2 := by nlinarith
    _ ≤ L n := hp

theorem layout_fits_of_ratio (n b : ℕ)
    (hQ : 64 ≤ layoutQ n) (he : 32768 * layoutEnergy n b ≤ layoutQ n) :
    4 * layoutCutoff n b ≤ layoutQ n := by
  have hs := Nat.sqrt_le' (128 * layoutQ n * layoutEnergy n b)
  unfold layoutCutoff
  nlinarith

theorem eventually_layout_fits (b : ℕ → ℕ) (q : ℕ)
    (hb : ∀ᶠ n : ℕ in atTop, b n ≤ L n ^ q) :
    ∀ᶠ n : ℕ in atTop, 4 * layoutCutoff n (b n) ≤ layoutQ n := by
  filter_upwards [eventually_layoutQ_ge 64,
    eventually_layoutQ_energy_ratio b q 32768 hb] with n hn he
  exact layout_fits_of_ratio n (b n) hn he

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticLayoutRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem eventually_L_ge (a : ℕ) : ∀ᶠ n : ℕ in atTop, a ≤ L n := by
  filter_upwards [eventually_le_s a] with n hn
  exact hn.trans (s_le_L n)

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticLayoutLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

private theorem label_log_bound (N B Q : ℝ) (R : ℕ)
    (hN : 1 ≤ N) (hB : 1 ≤ B) (hQ : 1 ≤ Q) :
    Real.log (4 * N * B * (8 * Q) ^ (2 * R) + 1) ≤
      7 + Real.log N + Real.log B + (2 * R : ℕ) * (7 + Real.log Q) := by
  have hN0 : 0 < N := by linarith
  have hB0 : 0 < B := by linarith
  have hQ0 : 0 < Q := by linarith
  have hp : 1 ≤ (8 * Q) ^ (2 * R) := one_le_pow₀ (by linarith)
  have hz : 1 ≤ 4 * N * B * (8 * Q) ^ (2 * R) := by
    have hNB := one_le_mul_of_one_le_of_one_le hN hB
    have hNBp := one_le_mul_of_one_le_of_one_le hNB hp
    nlinarith
  have hlog8 : Real.log 8 ≤ 7 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
    linarith
  calc
    Real.log (4 * N * B * (8 * Q) ^ (2 * R) + 1) ≤
        Real.log (8 * N * B * (8 * Q) ^ (2 * R)) :=
      Real.log_le_log (by positivity) (by nlinarith)
    _ = Real.log 8 + Real.log N + Real.log B +
        (2 * R : ℕ) * (Real.log 8 + Real.log Q) := by
      simp [Real.log_mul, Real.log_pow, hN0.ne', hB0.ne', hQ0.ne']
    _ ≤ 7 + Real.log N + Real.log B + (2 * R : ℕ) * (7 + Real.log Q) := by gcongr

theorem eventually_layout_label_log (b : ℕ → ℕ) (q : ℕ)
    (hb : ∀ᶠ n : ℕ in atTop, 1 ≤ b n ∧ b n ≤ L n ^ q) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (4 * (n : ℝ) * b n * (8 * (layoutQ n : ℝ)) ^
        (2 * layoutCutoff n (b n)) + 1) ≤ 4 * (L n : ℝ) ^ 2 := by
  have hbp : ∀ᶠ n : ℕ in atTop, b n ≤ L n ^ q := hb.mono fun _ h => h.2
  filter_upwards [hb, eventually_layout_fits b q hbp, eventually_layoutQ_ge 1,
    eventually_L_ge (max 16 q), eventually_ge_atTop (1 : ℕ)] with n hbn hfit hQ hL hn
  have hL16 : (16 : ℝ) ≤ L n := by exact_mod_cast (le_max_left 16 q).trans hL
  have hqL : (q : ℝ) ≤ L n := by exact_mod_cast (le_max_right 16 q).trans hL
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hB : (1 : ℝ) ≤ b n := by exact_mod_cast hbn.1
  have hQ' : (1 : ℝ) ≤ layoutQ n := by exact_mod_cast hQ
  have hR : (layoutCutoff n (b n) : ℝ) ≤ L n := by
    have hQle : layoutQ n ≤ L n := Nat.div_le_self _ _
    exact_mod_cast (show layoutCutoff n (b n) ≤ L n by omega)
  have hLn : Real.log (n : ℝ) ≤ L n := by
    calc
      Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 16) := Real.log_le_log (by linarith) (by linarith)
      _ ≤ logSize n := (logSize_natural_bounds n).1
      _ ≤ L n := (logSize_lt_L n).le
  have hLL : Real.log (L n : ℝ) ≤ L n := by
    have h := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < L n)
    linarith
  have hLB : Real.log (b n : ℝ) ≤ (q : ℝ) * (L n : ℝ) := by
    calc
      Real.log (b n : ℝ) ≤ Real.log ((L n : ℝ) ^ q) :=
        Real.log_le_log (by linarith) (by exact_mod_cast hbn.2)
      _ = (q : ℝ) * Real.log (L n : ℝ) := Real.log_pow _ _
      _ ≤ (q : ℝ) * (L n : ℝ) := mul_le_mul_of_nonneg_left hLL (Nat.cast_nonneg q)
  have hLQ : Real.log (layoutQ n : ℝ) ≤ L n := by
    calc
      Real.log (layoutQ n : ℝ) ≤ Real.log (L n : ℝ) :=
        Real.log_le_log (by linarith) (by exact_mod_cast Nat.div_le_self (L n) (layoutDen n))
      _ ≤ L n := hLL
  have hmain := label_log_bound (n : ℝ) (b n : ℝ) (layoutQ n : ℝ)
    (layoutCutoff n (b n)) hN hB hQ'
  have hprod : (2 * layoutCutoff n (b n) : ℕ) * (7 + Real.log (layoutQ n : ℝ)) ≤
      2 * (L n : ℝ) * (7 + (L n : ℝ)) := by
    push_cast
    gcongr
  have hqb := mul_le_mul_of_nonneg_right hqL (show (0 : ℝ) ≤ L n by positivity)
  nlinarith

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

theorem layoutCutoff_mono (n : ℕ) : Monotone (layoutCutoff n) := by
  intro a b hab
  have he : layoutEnergy n a ≤ layoutEnergy n b := by
    unfold layoutEnergy
    simp only [Nat.log2_eq_log_two]
    apply Nat.add_le_add_right
    apply Nat.log_mono_right
    gcongr
  unfold layoutCutoff
  apply Nat.add_le_add_right
  apply Nat.sqrt_le_sqrt
  exact Nat.mul_le_mul_left _ he

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticResidualLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The layout guards hold uniformly for all half-size residuals and all
polynomially bounded branch-dependent occurrence/arity parameters. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem eventually_uniform_label_log_oai (q : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ b : ℕ, 1 ≤ b → b ≤ L m ^ q →
      Real.log (4 * (m : ℝ) * b * (8 * (layoutQ m : ℝ)) ^
        (2 * layoutCutoff m b) + 1) ≤ 4 * (L m : ℝ) ^ 2 := by
  have hmax : ∀ᶠ m : ℕ in atTop, 1 ≤ L m ^ q ∧ L m ^ q ≤ L m ^ q :=
    Eventually.of_forall (fun m => ⟨Nat.succ_le_of_lt (pow_pos (L_pos m) q), le_rfl⟩)
  filter_upwards [eventually_layout_label_log (fun m => L m ^ q) q hmax,
    eventually_layoutQ_ge 1] with m hm hQ b hb0 hb
  have hR := layoutCutoff_mono m hb
  have hQ' : (1 : ℝ) ≤ layoutQ m := by exact_mod_cast hQ
  have harg : 4 * (m : ℝ) * b * (8 * (layoutQ m : ℝ)) ^
        (2 * layoutCutoff m b) + 1 ≤
      4 * (m : ℝ) * (L m ^ q : ℕ) * (8 * (layoutQ m : ℝ)) ^
        (2 * layoutCutoff m (L m ^ q)) + 1 := by
    gcongr
    linarith
  exact (Real.log_le_log (by positivity) harg).trans hm

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.eventually_uniform_label_log_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.eventually_uniform_label_log_oai
