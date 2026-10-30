-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.eventually_residual_layout_guards
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:38:17.476057+00:00
-- url     : https://prove2.me/submissions/8d40efd2-6566-4630-ab7b-4d8615628c49

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

theorem eventually_L_power_le_n (q : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, C * (L n : ℝ) ^ q ≤ n := by
  have hb := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (SubexpRuntime.eventually_logb_power_le q
      (show 0 < C * (2 : ℝ) ^ q by positivity))
  filter_upwards [hb] with n hn
  calc
    C * (L n : ℝ) ^ q ≤ C * (2 * logSize n) ^ q :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (L_le_twice_logSize n) q) hC.le
    _ = (C * (2 : ℝ) ^ q) * logSize n ^ q := by rw [mul_pow]; ring
    _ ≤ n := hn

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

theorem layout_grid_square (n : ℕ) :
    (layoutR n ^ (4 * layoutQ n)) ^ 2 ≤ n + 16 := by
  have hbudget : 64 * (Nat.log2 (layoutR n) + 1) * layoutQ n ≤ L n := by
    exact Nat.mul_div_le (L n) (layoutDen n)
  have hlog : 1 ≤ Nat.log2 (n + 16) :=
    (Nat.le_log2 (by omega)).2 (by norm_num)
  have hexp : (Nat.log2 (layoutR n) + 1) * (4 * layoutQ n * 2) ≤ Nat.log2 (n + 16) := by
    unfold L at hbudget
    nlinarith
  calc
    (layoutR n ^ (4 * layoutQ n)) ^ 2 = layoutR n ^ (4 * layoutQ n * 2) :=
      (pow_mul _ _ _).symm
    _ ≤ (2 ^ (Nat.log2 (layoutR n) + 1)) ^ (4 * layoutQ n * 2) :=
      Nat.pow_le_pow_left (Nat.lt_log2_self.le) _
    _ = 2 ^ ((Nat.log2 (layoutR n) + 1) * (4 * layoutQ n * 2)) :=
      (pow_mul _ _ _).symm
    _ ≤ 2 ^ Nat.log2 (n + 16) := Nat.pow_le_pow_right (by omega) hexp
    _ ≤ n + 16 := Nat.log2_self_le (by omega)

/-- The exponentially many grid cells still leave room for every fixed
polylogarithmic factor. The exponent 4Q is the actual squared grid factor. -/
theorem eventually_polylog_grid_le_n (f : ℕ → ℝ) (q : ℕ) {C : ℝ} (hC : 0 < C)
    (hf0 : ∀ n, 0 ≤ f n)
    (hf : ∀ᶠ n : ℕ in atTop, f n ≤ C * (L n : ℝ) ^ q) :
    ∀ᶠ n : ℕ in atTop, f n * (layoutR n : ℝ) ^ (4 * layoutQ n) ≤ n := by
  have hh := eventually_L_power_le_n (2 * q) (show 0 < 2 * C ^ 2 by positivity)
  filter_upwards [hf, hh, eventually_ge_atTop (16 : ℕ)] with n hn hp hn16
  have hgrid : ((layoutR n : ℝ) ^ (4 * layoutQ n)) ^ 2 ≤ (n : ℝ) + 16 := by
    exact_mod_cast layout_grid_square n
  have hsq : 2 * (f n) ^ 2 ≤ n := by
    have hpow := pow_le_pow_left₀ (hf0 n) hn 2
    have heq : (C * (L n : ℝ) ^ q) ^ 2 = C ^ 2 * (L n : ℝ) ^ (2 * q) := by
      rw [mul_pow, ← pow_mul]
      congr 2
      omega
    rw [heq] at hpow
    nlinarith
  have hn16' : (16 : ℝ) ≤ n := by exact_mod_cast hn16
  have hmul := mul_le_mul hsq hgrid (sq_nonneg _) (by positivity : (0 : ℝ) ≤ n)
  have hfpos := hf0 n
  have hgpos : 0 ≤ (layoutR n : ℝ) ^ (4 * layoutQ n) := by positivity
  nlinarith [sq_nonneg ((n : ℝ) - f n * (layoutR n : ℝ) ^ (4 * layoutQ n))]

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticLayoutFeasibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem eventually_layout_small_grid :
    ∀ᶠ n : ℕ in atTop, 16 * layoutQ n * layoutR n ^ 2 ≤ n := by
  filter_upwards [eventually_L_power_le_n 3 (show (0 : ℝ) < 16 by norm_num)] with n hn
  have hnat : 16 * L n ^ 3 ≤ n := by exact_mod_cast hn
  have hQ : layoutQ n ≤ L n := Nat.div_le_self _ _
  have hr := layoutR_le_L n
  calc
    16 * layoutQ n * layoutR n ^ 2 ≤ 16 * L n * L n ^ 2 := by gcongr
    _ = 16 * L n ^ 3 := by ring
    _ ≤ n := hnat

theorem eventually_layout_large_grid (a b : ℕ → ℕ) (q : ℕ)
    (ha : ∀ᶠ n : ℕ in atTop, a n ≤ L n ^ q)
    (hb : ∀ᶠ n : ℕ in atTop, b n ≤ L n ^ q) :
    ∀ᶠ n : ℕ in atTop,
      4096 * (b n + a n) * b n ^ 2 * layoutR n ^ 2 * L n ^ 4 *
        (layoutR n ^ (2 * layoutQ n)) ^ 2 ≤ n := by
  let f (n : ℕ) : ℝ := 4096 * ((b n : ℝ) + a n) * (b n : ℝ) ^ 2 *
    (layoutR n : ℝ) ^ 2 * (L n : ℝ) ^ 4
  have hf : ∀ᶠ n : ℕ in atTop, f n ≤ 8192 * (L n : ℝ) ^ (3 * q + 6) := by
    filter_upwards [ha, hb] with n han hbn
    have ha' : (a n : ℝ) ≤ (L n : ℝ) ^ q := by exact_mod_cast han
    have hb' : (b n : ℝ) ≤ (L n : ℝ) ^ q := by exact_mod_cast hbn
    have hr : (layoutR n : ℝ) ≤ L n := by exact_mod_cast layoutR_le_L n
    calc
      f n ≤ 4096 * ((L n : ℝ) ^ q + (L n : ℝ) ^ q) * ((L n : ℝ) ^ q) ^ 2 *
          (L n : ℝ) ^ 2 * (L n : ℝ) ^ 4 := by dsimp [f]; gcongr
      _ = 8192 * (L n : ℝ) ^ (3 * q + 6) := by
        simp only [pow_add, pow_mul]
        ring
  have h := eventually_polylog_grid_le_n f (3 * q + 6)
    (show (0 : ℝ) < 8192 by norm_num) (by intro n; dsimp [f]; positivity) hf
  filter_upwards [h] with n hn
  have heq : (layoutR n ^ (2 * layoutQ n)) ^ 2 = layoutR n ^ (4 * layoutQ n) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [heq]
  dsimp [f] at hn
  exact_mod_cast hn

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

theorem eventually_uniform_layout_guards (q : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ a b : ℕ, a ≤ L m ^ q → b ≤ L m ^ q →
      2 ≤ layoutQ m ∧
      4 * layoutCutoff m b ≤ layoutQ m ∧
      16 * layoutQ m * layoutR m ^ 2 ≤ m ∧
      4096 * (b + a) * b ^ 2 * layoutR m ^ 2 * L m ^ 4 *
        (layoutR m ^ (2 * layoutQ m)) ^ 2 ≤ m := by
  have hmax : ∀ᶠ m : ℕ in atTop, L m ^ q ≤ L m ^ q := Eventually.of_forall (fun _ => le_rfl)
  filter_upwards [eventually_layoutQ_ge 2,
    eventually_layout_fits (fun m => L m ^ q) q hmax,
    eventually_layout_small_grid,
    eventually_layout_large_grid (fun m => L m ^ q) (fun m => L m ^ q) q hmax hmax]
    with m hQ hfit hsmall hlarge a b ha hb
  refine ⟨hQ, ?_, hsmall, ?_⟩
  · exact (Nat.mul_le_mul_left 4 (layoutCutoff_mono m hb)).trans hfit
  · exact (by gcongr :
      4096 * (b + a) * b ^ 2 * layoutR m ^ 2 * L m ^ 4 *
          (layoutR m ^ (2 * layoutQ m)) ^ 2 ≤
        4096 * (L m ^ q + L m ^ q) * (L m ^ q) ^ 2 * layoutR m ^ 2 * L m ^ 4 *
          (layoutR m ^ (2 * layoutQ m)) ^ 2).trans hlarge

theorem eventually_residual_layout_guards_oai (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m a b : ℕ, n ≤ 2 * m → a ≤ L m ^ q → b ≤ L m ^ q →
      2 ≤ layoutQ m ∧
      4 * layoutCutoff m b ≤ layoutQ m ∧
      16 * layoutQ m * layoutR m ^ 2 ≤ m ∧
      4096 * (b + a) * b ^ 2 * layoutR m ^ 2 * L m ^ 4 *
        (layoutR m ^ (2 * layoutQ m)) ^ 2 ≤ m := by
  filter_upwards [eventually_uniform_half (eventually_uniform_layout_guards q)] with n hn m a b hnm ha hb
  exact hn m hnm a b ha hb

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.eventually_residual_layout_guards_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.eventually_residual_layout_guards_oai
