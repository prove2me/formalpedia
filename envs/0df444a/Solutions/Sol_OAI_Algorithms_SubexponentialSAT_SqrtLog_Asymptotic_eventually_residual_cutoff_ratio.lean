-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.eventually_residual_cutoff_ratio
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:37:16.647268+00:00
-- url     : https://prove2.me/submissions/f4076a9b-746c-4ff1-b76d-bc51a63f28c1

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

theorem schedule_maximal (n : ℕ) : L n < (s n + 1) ^ 2 * w n ^ 4 := by
  have h := (le_s_iff n (s n + 1)).not
  exact Nat.lt_of_not_ge (h.mp (by omega))

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

theorem eventually_w_sq_le_s : ∀ᶠ n : ℕ in atTop, w n ^ 2 ≤ s n := by
  filter_upwards [eventually_w_power_le_L 8 (show (0 : ℝ) < 1 by norm_num)] with n hn
  apply (le_s_iff n (w n ^ 2)).2
  simp only [one_mul] at hn
  have hnat : w n ^ 8 ≤ L n := by exact_mod_cast hn
  convert hnat using 1 <;> first | rfl | ring

theorem eventually_w_le_log_r :
    ∀ᶠ n : ℕ in atTop, w n ≤ 7 * (Nat.log2 (layoutR n) + 1) := by
  filter_upwards [eventually_w_sq_le_s] with n hn
  have hr : s n ≤ layoutR n := le_max_right _ _
  have hr2 := layoutR_ge_two n
  have hw : w n ^ 2 ≤ layoutR n := hn.trans hr
  have hw4 : w n ^ 4 ≤ layoutR n ^ 2 := by
    have h := Nat.pow_le_pow_left hw 2
    convert h using 1 <;> first | rfl | ring
  have hsp : s n + 1 ≤ 2 * layoutR n := by omega
  have hL : L n ≤ 4 * layoutR n ^ 4 := by
    calc
      L n ≤ (s n + 1) ^ 2 * w n ^ 4 := (schedule_maximal n).le
      _ ≤ (2 * layoutR n) ^ 2 * layoutR n ^ 2 := by gcongr
      _ = _ := by ring
  have hpow : L n ≤ 2 ^ (2 + 4 * (Nat.log2 (layoutR n) + 1)) := by
    calc
      L n ≤ 4 * layoutR n ^ 4 := hL
      _ ≤ 4 * (2 ^ (Nat.log2 (layoutR n) + 1)) ^ 4 := by
        exact Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left Nat.lt_log2_self.le 4)
      _ = _ := by rw [← pow_mul]; norm_num [pow_add, Nat.mul_comm]
  have hlog := Nat.log_mono_right (b := 2) hpow
  rw [Nat.log_pow (by norm_num : 1 < (2 : ℕ))] at hlog
  unfold w
  rw [Nat.log2_eq_log_two]
  nlinarith

theorem eventually_layoutCutoff_sq_le (b : ℕ → ℕ) (q : ℕ)
    (hb : ∀ᶠ n : ℕ in atTop, b n ≤ L n ^ q) :
    ∀ᶠ n : ℕ in atTop, layoutCutoff n (b n) ^ 2 ≤ (28 * q + 312) * L n := by
  filter_upwards [hb, eventually_w_le_log_r] with n hn hw
  have he := layoutEnergy_le n (b n) q hn
  have hbudget : 64 * (Nat.log2 (layoutR n) + 1) * layoutQ n ≤ L n :=
    Nat.mul_div_le (L n) (layoutDen n)
  have hQE : 64 * layoutQ n * layoutEnergy n (b n) ≤ 7 * (q + 10) * L n := by
    calc
      64 * layoutQ n * layoutEnergy n (b n) ≤ 64 * layoutQ n * ((q + 10) * w n) := by gcongr
      _ ≤ 64 * layoutQ n * ((q + 10) * (7 * (Nat.log2 (layoutR n) + 1))) := by gcongr
      _ = 7 * (q + 10) * (64 * (Nat.log2 (layoutR n) + 1) * layoutQ n) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hbudget
  have hroot := Nat.sqrt_le' (128 * layoutQ n * layoutEnergy n (b n))
  have hL := L_pos n
  have hsmall (x : ℕ) : (x + 4) ^ 2 ≤ 2 * x ^ 2 + 32 := by
    have hi : ((x : ℤ) + 4) ^ 2 ≤ 2 * (x : ℤ) ^ 2 + 32 := by
      nlinarith [sq_nonneg ((x : ℤ) - 4)]
    exact_mod_cast hi
  unfold layoutCutoff
  calc
    _ ≤ 2 * Nat.sqrt (128 * layoutQ n * layoutEnergy n (b n)) ^ 2 + 32 := hsmall _
    _ ≤ 256 * layoutQ n * layoutEnergy n (b n) + 32 := by nlinarith
    _ ≤ (28 * q + 312) * L n := by nlinarith

theorem eventually_layoutQ_comparison :
    ∀ᶠ n : ℕ in atTop,
      L n ≤ 128 * layoutQ n * w n ∧ 64 * layoutQ n * w n ≤ 7 * L n := by
  filter_upwards [eventually_layoutQ_ge 1, eventually_w_le_log_r] with n hQ hw
  have hb : 64 * (Nat.log2 (layoutR n) + 1) * layoutQ n ≤ L n :=
    Nat.mul_div_le (L n) (layoutDen n)
  have hd := layoutDen_le n
  have hdiv := Nat.div_add_mod (L n) (layoutDen n)
  have hmod := Nat.mod_lt (L n) (layoutDen_pos n)
  change layoutDen n * layoutQ n + L n % layoutDen n = L n at hdiv
  constructor
  · have hm := Nat.mul_le_mul_left (layoutQ n + 1) hd
    nlinarith
  · have hm := Nat.mul_le_mul_left (64 * layoutQ n) hw
    nlinarith

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

theorem eventually_cutoff_ratio (b : ℕ → ℕ) (q : ℕ)
    (hb : ∀ᶠ n : ℕ in atTop, b n ≤ L n ^ q) :
    ∀ᶠ n : ℕ in atTop,
      (layoutCutoff n (b n) : ℝ) / layoutQ n ≤
        (128 * (28 * q + 312) : ℕ) * (w n : ℝ) / Real.sqrt (L n : ℝ) := by
  filter_upwards [eventually_layoutCutoff_sq_le b q hb,
    eventually_layoutQ_comparison, eventually_layoutQ_ge 1] with n hsq hcomp hQ
  have hQ' : (0 : ℝ) < layoutQ n := by exact_mod_cast (by omega : 0 < layoutQ n)
  have hL : (0 : ℝ) < L n := by exact_mod_cast L_pos n
  have hroot0 : 0 < Real.sqrt (L n : ℝ) := Real.sqrt_pos.2 hL
  have hroot := Real.sq_sqrt hL.le
  have hsq' : (layoutCutoff n (b n) : ℝ) ^ 2 ≤ (28 * q + 312 : ℕ) * (L n : ℝ) := by
    exact_mod_cast hsq
  have hK : (1 : ℝ) ≤ (28 * q + 312 : ℕ) := by norm_cast; omega
  have hR : (layoutCutoff n (b n) : ℝ) ≤
      (28 * q + 312 : ℕ) * Real.sqrt (L n : ℝ) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    calc
      (layoutCutoff n (b n) : ℝ) ^ 2 ≤ (28 * q + 312 : ℕ) * (L n : ℝ) := hsq'
      _ ≤ ((28 * q + 312 : ℕ) : ℝ) ^ 2 * (L n : ℝ) :=
        mul_le_mul_of_nonneg_right (by nlinarith) hL.le
      _ = ((28 * q + 312 : ℕ) * Real.sqrt (L n : ℝ)) ^ 2 := by rw [mul_pow, hroot]
  have hprod := mul_le_mul_of_nonneg_right hR hroot0.le
  have hprod' : (layoutCutoff n (b n) : ℝ) * Real.sqrt (L n : ℝ) ≤
      (28 * q + 312 : ℕ) * (L n : ℝ) := by
    calc
      _ ≤ (28 * q + 312 : ℕ) * Real.sqrt (L n : ℝ) * Real.sqrt (L n : ℝ) := hprod
      _ = _ := by rw [mul_assoc, ← pow_two, hroot]
  have hcomp' : (L n : ℝ) ≤ 128 * (layoutQ n : ℝ) * w n := by exact_mod_cast hcomp.1
  have hm := mul_le_mul_of_nonneg_left hcomp' (show (0 : ℝ) ≤ (28 * q + 312 : ℕ) by positivity)
  apply (div_le_div_iff₀ hQ' hroot0).2
  convert hprod'.trans hm using 1 ; push_cast ; ring

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

theorem L_mono : Monotone L := by
  intro a b hab
  unfold L
  simp only [Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_mono_right (Nat.add_le_add_right hab 16)) 1

theorem w_mono : Monotone w := by
  intro a b hab
  unfold w
  simp only [Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_mono_right (L_mono hab)) 1

theorem L_le_succ_of_half {n m : ℕ} (hnm : n ≤ 2 * m) : L n ≤ L m + 1 := by
  have harg : n + 16 ≤ (m + 16) * 2 := by omega
  have h := Nat.log_mono_right (b := 2) harg
  rw [Nat.log_mul_base (by norm_num : 1 < (2 : ℕ)) (by omega : m + 16 ≠ 0)] at h
  simpa [L, Nat.log2_eq_log_two, Nat.add_assoc] using Nat.add_le_add_right h 1

theorem L_le_twice_of_half {n m : ℕ} (hnm : n ≤ 2 * m) : L n ≤ 2 * L m := by
  have := L_le_succ_of_half hnm
  have := L_pos m
  omega

theorem sqrt_L_le_twice_of_half {n m : ℕ} (hnm : n ≤ 2 * m) :
    Real.sqrt (L n : ℝ) ≤ 2 * Real.sqrt (L m : ℝ) := by
  have h : (L n : ℝ) ≤ 2 * (L m : ℝ) := by exact_mod_cast L_le_twice_of_half hnm
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ L m by positivity)
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · nlinarith

theorem residual_log_ratio_le {n m : ℕ} (hmn : m ≤ n) (hnm : n ≤ 2 * m) :
    (w m : ℝ) / Real.sqrt (L m : ℝ) ≤
      2 * (w n : ℝ) / Real.sqrt (L n : ℝ) := by
  have hm : 0 < Real.sqrt (L m : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast L_pos m)
  have hn : 0 < Real.sqrt (L n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast L_pos n)
  have hw : (w m : ℝ) ≤ w n := by exact_mod_cast w_mono hmn
  have hs := sqrt_L_le_twice_of_half hnm
  apply (div_le_div_iff₀ hm hn).2
  calc
    (w m : ℝ) * Real.sqrt (L n : ℝ) ≤ (w n : ℝ) * (2 * Real.sqrt (L m : ℝ)) := by gcongr
    _ = _ := by ring

/-- Eventual assertions are uniform over every residual dimension in the
half interval; in particular the residual may depend on a branch. -/
theorem eventually_uniform_half {P : ℕ → Prop} (hP : ∀ᶠ m in atTop, P m) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, n ≤ 2 * m → P m := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hP
  filter_upwards [eventually_ge_atTop (2 * N)] with n hn m hnm
  exact hN m (by omega)

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

theorem eventually_uniform_cutoff_ratio (q : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ b : ℕ, b ≤ L m ^ q →
      (layoutCutoff m b : ℝ) / layoutQ m ≤
        (128 * (28 * q + 312) : ℕ) * (w m : ℝ) / Real.sqrt (L m : ℝ) := by
  have hh := eventually_cutoff_ratio (fun m => L m ^ q) q (Eventually.of_forall (fun _ => le_rfl))
  filter_upwards [hh] with m hm b hb
  exact (div_le_div_of_nonneg_right (by exact_mod_cast layoutCutoff_mono m hb) (by positivity)).trans hm

theorem eventually_residual_cutoff_ratio_oai (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m b : ℕ, m ≤ n → n ≤ 2 * m → b ≤ L m ^ q →
      (layoutCutoff m b : ℝ) / layoutQ m ≤
        (256 * (28 * q + 312) : ℕ) * (w n : ℝ) / Real.sqrt (L n : ℝ) := by
  filter_upwards [eventually_uniform_half (eventually_uniform_cutoff_ratio q)] with n hn m b hmn hnm hb
  have hlocal := hn m hnm b hb
  have hratio := residual_log_ratio_le hmn hnm
  calc
    _ ≤ (128 * (28 * q + 312) : ℕ) * ((w m : ℝ) / Real.sqrt (L m : ℝ)) := by simpa [mul_div_assoc] using hlocal
    _ ≤ (128 * (28 * q + 312) : ℕ) * (2 * (w n : ℝ) / Real.sqrt (L n : ℝ)) := by gcongr
    _ = _ := by push_cast; ring

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.eventually_residual_cutoff_ratio_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.eventually_residual_cutoff_ratio_oai
