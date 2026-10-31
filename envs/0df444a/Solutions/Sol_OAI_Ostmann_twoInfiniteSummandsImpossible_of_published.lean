-- Prove2me | solution 1 for OAI.Ostmann.twoInfiniteSummandsImpossible_of_published
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:36:53.792186+00:00
-- url     : https://prove2.me/submissions/d6ab7ca7-cb43-4291-b1e9-e652dc3135cf

import Mathlib
import Definitions.Def_OstmannComplete
import Definitions.Def_OAIQ095D008
import Theorems.Thm_OAI_Ostmann_EventuallyPrimeSumset_constructed_initial_amplitude
import Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_selected_scheduled_diagonal
import Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_selected_scheduled_final_contradiction
import Theorems.Thm_OAI_Ostmann_frozen_initial_small_amplitude
import Theorems.Thm_OAI_Ostmann_selected_scheduled_iteration

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticErrorRates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing the fixed-depth arithmetic comparison costs

The polynomial and spectator costs in Section 8 are dominated by the
double-exponential savings. The strict numerical gaps in the manuscript
therefore survive the finite history and equality-pattern sums.
-/

namespace Ostmann

open Filter Asymptotics

theorem arithmetic_exponent_absorption (a b d C c : ℝ) (n : ℕ)
    (hb : 0 < b) (hab : a < b) (hdb : d < b) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      C * L ^ n + C * L * Real.exp (a * L) - c * Real.exp (b * L) ≤
        -Real.exp (d * L) := by
  have hp := (isLittleO_pow_exp_pos_mul_atTop n hb).const_mul_left C
  have hm : (fun L : ℝ => C * (Real.exp (a * L) * L)) =o[atTop]
      (fun L => Real.exp (b * L)) := by
    simpa only [Real.rpow_one] using (isLittleO_exp_mul_rpow_of_lt 1 hab).const_mul_left C
  have he : (fun L : ℝ => Real.exp (d * L)) =o[atTop] (fun L => Real.exp (b * L)) := by
    simpa only [Real.rpow_zero, mul_one] using isLittleO_exp_mul_rpow_of_lt 0 hdb
  have h := ((hp.add hm).add he).bound hc
  filter_upwards [h] with L hL
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hL
  have hle := (le_abs_self _).trans hL
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SquarePullback
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The factor two in square pullbacks

The finite-fiber bound and Cauchy--Schwarz estimate used in the manuscript's
equation `tree-square-pullback`. Multiplicative characters are extended by zero
at zero, as in the manuscript. Evaluations in these lemmas are at units.
-/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.instDecidableEqMulCharZModComplex_solutions
/-- A multiplicative character has modulus one at each unit. -/
theorem norm_mulChar_unit {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (u : (ZMod p)ˣ) : ‖χ u‖ = 1 := by
  exact Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OneSidedDecayBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The separated long/short scales absorb the one-sided losses -/

namespace Ostmann

open Filter

theorem eventual_polynomial_log_budget (C z α ε : ℝ) (d : ℕ)
    (hC : 0 ≤ C) (hz : 0 ≤ z) (hα : 0 < α) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 0 ≤ m → m ≤ z * L →
      C * (1 + m) ^ d ≤ ε * Real.exp (α * L) := by
  have hb := ((isLittleO_pow_exp_pos_mul_atTop d hα).const_mul_left
    (C * (z + 1) ^ d)).bound hε
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with L hlarge hL m hm hmL
  have hx : 1 + m ≤ (z + 1) * L := by nlinarith
  have hp : (1 + m) ^ d ≤ ((z + 1) * L) ^ d := pow_le_pow_left₀ (by linarith) hx d
  have hlarge' : C * (z + 1) ^ d * L ^ d ≤ ε * Real.exp (α * L) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ C * (z + 1) ^ d * L ^ d),
      abs_of_pos (Real.exp_pos _)] using hlarge
  calc
    _ ≤ C * (((z + 1) * L) ^ d) := mul_le_mul_of_nonneg_left hp hC
    _ = C * (z + 1) ^ d * L ^ d := by rw [mul_pow]; ring
    _ ≤ _ := hlarge'

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_WeightedPrimeIntervals
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Freezing a smooth cutoff on an actual prime log cell -/

namespace Ostmann

open scoped BigOperators
open MeasureTheory

theorem log_mem_of_mem_exp_interval {p : ℕ} {s t : ℝ}
    (hp : p ∈ Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊) :
    Real.log (p : ℝ) ∈ Set.Ioc s t := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hp
  have hexp : Real.exp s < p := Nat.lt_of_floor_lt hlo
  have hp0 : (0 : ℝ) < p := (Real.exp_pos s).trans hexp
  exact ⟨(Real.lt_log_iff_exp_lt hp0).mpr hexp,
    (Real.log_le_iff_le_exp hp0).mpr ((Nat.le_floor_iff (Real.exp_pos t).le).mp hhi)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeLogGrid
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete equal-mesh log cells and unit residues -/

namespace Ostmann

open scoped Classical

theorem mem_primeLogCellSet_iff {q a p : ℕ} {s t : ℝ} :
    p ∈ primeLogCellSet q a s t ↔
      p.Prime ∧ Nat.ModEq q p a ∧ Real.log (p : ℝ) ∈ Set.Ioc s t := by
  constructor
  · intro hp
    obtain ⟨hI, hprime, hres⟩ := Finset.mem_filter.mp hp
    exact ⟨hprime, hres, log_mem_of_mem_exp_interval hI⟩
  · rintro ⟨hprime, hres, hlo, hhi⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hprime, hres⟩
    · exact (Nat.floor_lt (Real.exp_pos s).le).mpr ((Real.lt_log_iff_exp_lt hp0).mp hlo)
    · exact (Nat.le_floor_iff (Real.exp_pos t).le).mpr ((Real.log_le_iff_le_exp hp0).mp hhi)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_PrimeJacobiCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prime-level Jacobi character is primitive -/

namespace Ostmann

theorem jacobiCharacterInt_prime (p : ℕ) [Fact p.Prime] :
    jacobiCharacterInt p = quadraticChar (ZMod p) := by
  apply MulChar.ext
  intro a
  have hcast : ((((a : ZMod p).val : ℤ) : ZMod p)) = (a : ZMod p) := by
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  calc
    jacobiCharacterInt p a = jacobiCharacterInt p ((((a : ZMod p).val : ℤ) : ZMod p)) :=
      congrArg (jacobiCharacterInt p) hcast.symm
    _ = jacobiSym ((a : ZMod p).val : ℤ) p := jacobiCharacterInt_intCast p _
    _ = legendreSym p ((a : ZMod p).val : ℤ) := (jacobiSym.legendreSym.to_jacobiSym p _).symm
    _ = quadraticChar (ZMod p) a := by rw [legendreSym, hcast]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RoundedEnergyCutoffs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical cutoffs for the actual square-root-reserve schedule -/

namespace Ostmann
open Filter

/-- The signed root-frequency set includes zero and both endpoints. -/
theorem card_transferFrequencyRange (V : ℕ) : (transferFrequencyRange V).card = 2 * V + 1 := by
  simp only [transferFrequencyRange, Int.card_Icc]
  omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFrequencyBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual accumulated gaps and rounded frequency cutoffs of Section 7 -/

namespace Ostmann
open scoped BigOperators

theorem movingCutoffExponent_zero (Bs BD Bz z m : ℝ) :
    movingCutoffExponent Bs BD Bz z m 0 = spectatorBaseGap Bs z m + Real.sqrt (4 * m) := by
  simp [movingCutoffExponent]

theorem movingCutoffExponent_succ (Bs BD Bz z m : ℝ) (n : ℕ) :
    movingCutoffExponent Bs BD Bz z m (n + 1) =
      movingCutoffExponent Bs BD Bz z m n +
      spectatorStepGap BD Bz z ((2 : ℝ) ^ n) m + (2 : ℝ) ^ n * Real.sqrt (4 * m) := by
  simp only [movingCutoffExponent, Finset.sum_range_succ, pow_succ]
  ring

private theorem moving_sum_two_pow (n : ℕ) :
    (∑ j ∈ Finset.range n, (2 : ℝ) ^ j) + 1 = (2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith

theorem movingCutoffExponent_bound (Bs BD Bz z m : ℝ) (n : ℕ)
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) (hz : 1 ≤ z) (hm : 4 ≤ m) :
    movingCutoffExponent Bs BD Bz z m n ≤
      (movingFrequencyRate Bs BD Bz z n - (2 : ℝ) ^ n) * m := by
  let Q := BD + Bz * Real.log z + (2 / 5 : ℝ) * Real.log ((2 : ℝ) ^ n)
  have hr : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hlogz : 0 ≤ Real.log z := Real.log_nonneg hz
  have hlogr : 0 ≤ Real.log ((2 : ℝ) ^ n) := Real.log_nonneg hr
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hm0 : 0 ≤ m := by linarith
  have hsum : (∑ j ∈ Finset.range n, spectatorStepGap BD Bz z ((2 : ℝ) ^ j) m) ≤
      (2 : ℝ) ^ n * Q * m := by
    calc
      _ ≤ ∑ j ∈ Finset.range n, (2 : ℝ) ^ j * Q * m := by
        apply Finset.sum_le_sum
        intro j hj
        have hjn : j ≤ n := (Finset.mem_range.mp hj).le
        have hp : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hjn
        have hl := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ j) hp
        have hc : BD + Bz * Real.log z + (2 / 5 : ℝ) * Real.log ((2 : ℝ) ^ j) ≤ Q := by
          dsimp only [Q]
          linarith
        unfold spectatorStepGap
        nlinarith only [mul_le_mul_of_nonneg_left hc (mul_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ j) hm0)]
      _ = (∑ j ∈ Finset.range n, (2 : ℝ) ^ j) * Q * m := by
        rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ (2 : ℝ) ^ n * Q * m := by
        have hh := moving_sum_two_pow n
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith : (∑ j ∈ Finset.range n, (2 : ℝ) ^ j) ≤ (2 : ℝ) ^ n) hQ) hm0
  have hsqrt : Real.sqrt (4 * m) ≤ m := by
    have hs := Real.sq_sqrt (show 0 ≤ 4 * m by positivity)
    have hp : 0 ≤ m * (m - 4) := mul_nonneg hm0 (by linarith)
    nlinarith [Real.sqrt_nonneg (4 * m)]
  have hbase : Bs + 8 * Real.log z ≤ (2 : ℝ) ^ n * (Bs + 8 * Real.log z) := by
    exact le_mul_of_one_le_left (by positivity) hr
  have hr0 : 0 ≤ (2 : ℝ) ^ n := by positivity
  have hb := mul_le_mul_of_nonneg_right hbase hm0
  have hs := mul_le_mul_of_nonneg_left hsqrt hr0
  unfold movingCutoffExponent spectatorBaseGap movingFrequencyRate
  dsimp only [Q] at hsum
  nlinarith only [hsum, hb, hs]

theorem movingNaturalCutoff_frequency_bound (Bs BD Bz z m : ℝ) (n : ℕ)
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) (hz : 1 ≤ z) (hm : 4 ≤ m) :
    (movingNaturalCutoff Bs BD Bz z m n : ℝ) ≤ Real.exp (movingFrequencyRate Bs BD Bz z n * m) ∧
    ((transferFrequencyRange (movingNaturalCutoff Bs BD Bz z m n)).card : ℝ) ≤
      Real.exp (movingFrequencyRate Bs BD Bz z n * m) := by
  let E := movingCutoffExponent Bs BD Bz z m n
  let A := movingFrequencyRate Bs BD Bz z n
  have hE := movingCutoffExponent_bound Bs BD Bz z m n hBs hBD hBz hz hm
  have hfloor : (movingNaturalCutoff Bs BD Bz z m n : ℝ) ≤ Real.exp E :=
    Nat.floor_le (Real.exp_pos _).le
  have hE0 : 0 ≤ E := by
    dsimp only [E, movingCutoffExponent, spectatorBaseGap]
    have hlogz := Real.log_nonneg hz
    apply add_nonneg
    · apply add_nonneg (mul_nonneg (by positivity) (by linarith))
      apply Finset.sum_nonneg
      intro j _
      have hl := Real.log_nonneg (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : 1 ≤ (2 : ℝ) ^ j)
      unfold spectatorStepGap
      positivity
    · positivity
  have hmargin : Real.log 3 ≤ (2 : ℝ) ^ n * m := by
    have hr : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    nlinarith
  have hcard : ((transferFrequencyRange (movingNaturalCutoff Bs BD Bz z m n)).card : ℝ) ≤
      3 * Real.exp E := by
    rw [card_transferFrequencyRange]
    push_cast
    have he1 := Real.one_le_exp hE0
    linarith
  have hfinal : 3 * Real.exp E ≤ Real.exp (A * m) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp only [A, E]
    nlinarith only [hE, hmargin]
  exact ⟨hfloor.trans ((by nlinarith [Real.exp_pos E] : Real.exp E ≤ 3 * Real.exp E).trans hfinal),
    hcard.trans hfinal⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SpectatorBulkScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The even bulk size and the accumulated giant loss in Section 9 -/

namespace Ostmann
open Filter
open scoped BigOperators

theorem spectatorBulkCount_even (k : ℕ) (L : ℝ) : Even (spectatorBulkCount k L) := by
  exact ⟨⌊(k : ℝ) ^ 4 * L / 2⌋₊, by unfold spectatorBulkCount; omega⟩

theorem spectatorBulkCount_lower (k : ℕ) (L : ℝ) :
    (k : ℝ) ^ 4 * L - 2 < (spectatorBulkCount k L : ℝ) := by
  have h := Nat.sub_one_lt_floor ((k : ℝ) ^ 4 * L / 2)
  unfold spectatorBulkCount
  push_cast
  linarith

theorem spectatorBulkCount_upper (k : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    (spectatorBulkCount k L : ℝ) ≤ (k : ℝ) ^ 4 * L := by
  have h := Nat.floor_le (show 0 ≤ (k : ℝ) ^ 4 * L / 2 by positivity)
  unfold spectatorBulkCount
  push_cast
  linarith

theorem spectatorBulkCount_half (k : ℕ) (L : ℝ)
    (hL : 4 ≤ (k : ℝ) ^ 4 * L) :
    (k : ℝ) ^ 4 * L / 2 ≤ (spectatorBulkCount k L : ℝ) := by
  linarith [spectatorBulkCount_lower k L]

theorem spectatorBulkCount_tendsto (k : ℕ) (hk : 0 < k) :
    Tendsto (fun L : ℝ => (spectatorBulkCount k L : ℝ)) atTop atTop := by
  have hk0 : 0 < (k : ℝ) ^ 4 := by positivity
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop ((b + 2) / (k : ℝ) ^ 4)] with L hL
  have h := (div_le_iff₀ hk0).mp hL
  linarith [spectatorBulkCount_lower k L]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCellGap
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From the prescribed cell sums to the diagonal's scalar gap -/

namespace Ostmann
open Filter

theorem spectatorStepGap_sub_one (BD Bz z r m : ℝ) :
    spectatorStepGap (BD - 1) Bz z r m = spectatorStepGap BD Bz z r m - r * m := by
  unfold spectatorStepGap
  ring

/-- `J + tail` is the protected and surviving compensation target in (7.4).
The two cell errors are paid by one unit of the coefficient of the step gap. -/
theorem moving_cell_diagonal_gap (BD Bz z r m J tail w b cb small cg ec es : ℝ)
    (hr : 0 ≤ r)
    (hbalance : r * w = r * (J + tail) - spectatorStepGap BD Bz z r m)
    (hupper : 4 * b ≤ w + ec)
    (hlower : r * (J + tail) - es * r ≤ small + r * (cb - 1))
    (hcost : 2 * cg + 1 + (ec + es) * r ≤ r * m) :
    2 * cg + 1 + (r * 4) * b - (small + r * (cb - 1)) ≤
      -spectatorStepGap (BD - 1) Bz z r m := by
  rw [spectatorStepGap_sub_one]
  have hu := mul_le_mul_of_nonneg_left hupper hr
  nlinarith only [hu, hlower, hbalance, hcost]

/-- The centers may each have an error proportional to `L`.  Since the bulk
size is `k^4 L + O(1)`, the same one-unit gap reserve pays these errors. -/
theorem moving_linear_cell_error_budget (k n : ℕ) (C L cg ec es : ℝ)
    (hC : 0 ≤ C) (hk : 4 * C + 16 ≤ (k : ℝ) ^ 4) (hL : 1 ≤ L)
    (hcg : cg ≤ (91 / 100 : ℝ) * L) (he : ec + es ≤ C * L) :
    2 * cg + 1 + (ec + es) * (2 ^ n : ℕ) ≤
      (2 ^ n : ℕ) * (spectatorBulkCount k L : ℝ) := by
  have hr : (1 : ℝ) ≤ (2 ^ n : ℕ) := by exact_mod_cast Nat.one_le_two_pow
  have hL0 : 0 ≤ L := by linarith
  have hm := spectatorBulkCount_lower k L
  have hkL := mul_le_mul_of_nonneg_right hk hL0
  have hCL := mul_nonneg hC hL0
  have hml : (C + 4) * L ≤ (spectatorBulkCount k L : ℝ) := by
    nlinarith only [hm, hkL, hCL, hL]
  have hem := mul_le_mul_of_nonneg_right he (by linarith : (0 : ℝ) ≤ (2 ^ n : ℕ))
  have hrL : L ≤ (2 ^ n : ℕ) * L := le_mul_of_one_le_left hL0 hr
  have htotal := mul_le_mul_of_nonneg_left hml
    (by linarith : (0 : ℝ) ≤ (2 ^ n : ℕ))
  nlinarith only [hcg, hL, hem, hrL, htotal]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCompensationTargets
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The backwards compensation-center construction of equation (7.4) -/

namespace Ostmann

theorem movingCompensationTargets_sum (J : ℝ) (ds : List ℝ) :
    J + (movingCompensationTargets J ds).sum =
      (2 : ℝ) ^ ds.length * J - movingCompensationTargetError ds := by
  induction ds with
  | nil => simp only [movingCompensationTargets, List.sum_nil, List.length_nil,
      pow_zero, one_mul, movingCompensationTargetError, sub_zero, add_zero]
  | cons d ds ih =>
    simp only [movingCompensationTargets, List.sum_cons, List.length_cons,
      movingCompensationTargetError, pow_succ]
    linarith

theorem movingCompensationTargetError_bounds (B : ℝ) (ds : List ℝ)
    (h : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ B) :
    0 ≤ movingCompensationTargetError ds ∧
      movingCompensationTargetError ds ≤ ((2 : ℝ) ^ ds.length - 1) * B := by
  induction ds with
  | nil => simp only [movingCompensationTargetError, List.length_nil, pow_zero,
      sub_self, zero_mul, le_refl, and_self]
  | cons d ds ih =>
    have hd := h d (by simp)
    have ht := ih (fun x hx => h x (by simp only [List.mem_cons]; exact Or.inr hx))
    simp only [movingCompensationTargetError, List.length_cons, pow_succ]
    constructor <;> linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCompensationGeometry
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every prescribed compensation target lies in the small-prime range -/

namespace Ostmann
open Filter

theorem movingCompensationTargets_mem_bounds (J B : ℝ) (ds : List ℝ)
    (hJ : 0 ≤ J) (hB : 0 ≤ B) (hd : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ B) :
    ∀ w ∈ movingCompensationTargets J ds,
      J - 2 ^ ds.length * B ≤ w ∧ w ≤ 2 ^ ds.length * J := by
  induction ds with
  | nil => simp [movingCompensationTargets]
  | cons d ds ih =>
    have hd0 := hd d (by simp)
    have hds : ∀ e ∈ ds, 0 ≤ e ∧ e ≤ B := fun e he => hd e (by simp [he])
    have herror := movingCompensationTargetError_bounds B ds hds
    have hsum := movingCompensationTargets_sum J ds
    have hp : (1 : ℝ) ≤ 2 ^ ds.length := one_le_pow₀ (by norm_num)
    have hpJ := mul_le_mul_of_nonneg_right hp hJ
    have hpB : 0 ≤ (2 : ℝ) ^ ds.length * B := by positivity
    have hpJ0 : 0 ≤ (2 : ℝ) ^ ds.length * J := by positivity
    intro w hw
    simp only [movingCompensationTargets, List.mem_cons] at hw
    simp only [List.length_cons, pow_succ]
    rcases hw with rfl | hw
    · constructor <;> nlinarith only [hsum, herror.1, herror.2, hd0.1, hd0.2, hpJ, hpB, hpJ0]
    · obtain ⟨hl, hu⟩ := ih hds w hw
      constructor <;> nlinarith only [hl, hu, hpB, hpJ0]

theorem eventual_moving_compensation_range (k : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ L : ℝ in atTop, ∀ (J : ℝ) (ds : List ℝ), ds.length ≤ k →
      16 * Real.exp ((1 / 100 : ℝ) * L) ≤ J →
      J ≤ 32 * Real.exp ((1 / 100 : ℝ) * L) →
      (∀ d ∈ ds, 0 ≤ d ∧ d ≤ B * L) →
      ∀ w ∈ movingCompensationTargets J ds,
        Real.exp ((1 / 100 : ℝ) * L) ≤ w / 4 ∧
        w / 4 ≤ Real.exp ((105 / 10000 : ℝ) * L) := by
  let C := (2 : ℝ) ^ k * B
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ht : Tendsto (fun L : ℝ => Real.exp ((5 / 10000 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [arithmetic_exponent_absorption 0 (1 / 100) 0 C 8 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ht.eventually (eventually_ge_atTop (8 * (2 : ℝ) ^ k)),
    eventually_ge_atTop (0 : ℝ)] with L hgap hratio hL
  intro J ds hlen hJlo hJhi hd w hw
  have hJ : 0 ≤ J := (by positivity : 0 ≤ 16 * Real.exp ((1 / 100 : ℝ) * L)).trans hJlo
  have hpow : (2 : ℝ) ^ ds.length ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hlen
  have hpowB := mul_le_mul_of_nonneg_right hpow (mul_nonneg hB hL)
  have hpowJ := mul_le_mul_of_nonneg_right hpow hJ
  obtain ⟨hl, hu⟩ := movingCompensationTargets_mem_bounds J (B * L) ds hJ (mul_nonneg hB hL) hd w hw
  simp only [pow_one, zero_mul, Real.exp_zero, mul_one] at hgap
  have hCL : 0 ≤ C * L := mul_nonneg hC hL
  have hcost : (2 : ℝ) ^ k * (B * L) ≤ 8 * Real.exp ((1 / 100 : ℝ) * L) := by
    dsimp only [C] at hgap hCL
    nlinarith only [hgap, hCL]
  constructor
  · nlinarith only [hl, hpowB, hcost, hJlo, Real.exp_nonneg ((1 / 100 : ℝ) * L)]
  · have hscale := mul_le_mul_of_nonneg_right hratio
      (Real.exp_nonneg ((1 / 100 : ℝ) * L))
    have heq : Real.exp ((5 / 10000 : ℝ) * L) * Real.exp ((1 / 100 : ℝ) * L) =
        Real.exp ((105 / 10000 : ℝ) * L) := by rw [← Real.exp_add]; congr 1; ring
    rw [heq] at hscale
    have hJbound := mul_le_mul_of_nonneg_left hJhi (by positivity : 0 ≤ (2 : ℝ) ^ k)
    nlinarith only [hu, hpowJ, hscale, hJbound]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCompensationGapList
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prescribed normalized gaps in the backwards target recursion -/

namespace Ostmann
open Filter

theorem movingCompensationGapRate_nonneg (k : ℕ) (hk : 0 < k)
    (BD Bz : ℝ) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) :
    0 ≤ movingCompensationGapRate k BD Bz := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hz : 1 ≤ (k : ℝ) ^ 4 := one_le_pow₀ hk1
  have hzlog := Real.log_nonneg hz
  have h2log : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold movingCompensationGapRate
  positivity

theorem movingCompensationGaps_bounds (k : ℕ) (hk : 0 < k)
    (BD Bz L : ℝ) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) (hL : 0 ≤ L) :
    ∀ d ∈ movingCompensationGaps k BD Bz L,
      0 ≤ d ∧ d ≤ movingCompensationGapRate k BD Bz * L := by
  intro d hd
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
  have hr : (0 : ℝ) < 2 ^ (i : ℕ) := by positivity
  have heq : spectatorStepGap BD Bz ((k : ℝ) ^ 4) ((2 : ℝ) ^ (i : ℕ))
      (spectatorBulkCount k L) / (2 : ℝ) ^ (i : ℕ) =
      (BD + Bz * Real.log ((k : ℝ) ^ 4) +
        (2 / 5 : ℝ) * (i : ℕ) * Real.log 2) * (spectatorBulkCount k L : ℝ) := by
    unfold spectatorStepGap
    simp only [Real.log_pow]
    field_simp [hr.ne']
  rw [heq]
  have hz : 1 ≤ (k : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast hk)
  have hzlog := Real.log_nonneg hz
  have h2log : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hi : ((i : ℕ) : ℝ) ≤ k := by exact_mod_cast i.isLt.le
  have hc : 0 ≤ BD + Bz * Real.log ((k : ℝ) ^ 4) + (2 / 5 : ℝ) * (i : ℕ) * Real.log 2 := by positivity
  have hc' : BD + Bz * Real.log ((k : ℝ) ^ 4) + (2 / 5 : ℝ) * (i : ℕ) * Real.log 2 ≤
      BD + Bz * Real.log ((k : ℝ) ^ 4) + (2 / 5 : ℝ) * k * Real.log 2 := by
    nlinarith only [hi, h2log]
  refine ⟨mul_nonneg hc (Nat.cast_nonneg _), ?_⟩
  have h1 := mul_le_mul_of_nonneg_right hc' (Nat.cast_nonneg (spectatorBulkCount k L) (α := ℝ))
  have h2 := mul_le_mul_of_nonneg_left (spectatorBulkCount_upper k L hL)
    (hc.trans hc')
  dsimp [movingCompensationGapRate]
  nlinarith only [h1, h2]

theorem eventual_prescribed_compensation_range (k : ℕ) (hk : 0 < k)
    (BD Bz : ℝ) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) :
    ∀ᶠ L : ℝ in atTop, ∀ J : ℝ,
      16 * Real.exp ((1 / 100 : ℝ) * L) ≤ J →
      J ≤ 32 * Real.exp ((1 / 100 : ℝ) * L) →
      ∀ w ∈ movingCompensationTargets J (movingCompensationGaps k BD Bz L),
        Real.exp ((1 / 100 : ℝ) * L) ≤ w / 4 ∧
        w / 4 ≤ Real.exp ((105 / 10000 : ℝ) * L) := by
  filter_upwards [eventual_moving_compensation_range k (movingCompensationGapRate k BD Bz)
      (movingCompensationGapRate_nonneg k hk BD Bz hBD hBz),
    eventually_ge_atTop (0 : ℝ)] with L htarget hL
  intro J hJlo hJhi
  exact htarget J (movingCompensationGaps k BD Bz L)
    (by simp) hJlo hJhi (movingCompensationGaps_bounds k hk BD Bz L hBD hBz hL)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFrequencyRateMonotone
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One frequency budget covers every depth of the finite schedule -/
namespace Ostmann

theorem movingFrequencyRate_monotone (Bs BD Bz z : ℝ)
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) (hz : 1 ≤ z) :
    Monotone (movingFrequencyRate Bs BD Bz z) := by
  intro n k hnk
  have hp : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hnk
  have hl := Real.log_nonneg hz
  have hr := Real.log_nonneg (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := n))
  have hlr := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ n) hp
  unfold movingFrequencyRate
  apply mul_le_mul hp
    (show Bs + 8 * Real.log z + BD + Bz * Real.log z + 2 / 5 * Real.log ((2 : ℝ) ^ n) + 2 ≤
      Bs + 8 * Real.log z + BD + Bz * Real.log z + 2 / 5 * Real.log ((2 : ℝ) ^ k) + 2 by linarith)
    (by positivity) (by positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Residues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complementary residue supports

The elementary reduction in §2 of the manuscript. Only the exclusion of
composite sums is used to separate the tail supports at a prime.
-/

namespace Ostmann

/-- The residue-support reduction requires only unboundedness of a summand. -/
theorem tailResidues_nonempty {A : Set ℕ} (hA : A.Infinite) (N p : ℕ) :
    (tailResidues A N p).Nonempty := by
  have hnot : ¬ BddAbove A := fun h => hA (Set.finite_iff_bddAbove.mpr h)
  obtain ⟨a, ha, hlarge⟩ := (not_bddAbove_iff.mp hnot) (N + p)
  exact ⟨(a : ZMod p), a, ⟨ha, hlarge⟩, rfl⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_TailStability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Collision stability on the two summand tails

This specializes the finite collision bound to the complementary supports
forced by an eventual prime decomposition. Prime-sum estimates remain
explicit hypotheses; no statement about the existence of a decomposition
is assumed as an analytic input.
-/

namespace Ostmann

open scoped BigOperators

theorem tailSupport_subset (A : Set ℕ) (N p : ℕ) :
    tailSupport A N p ⊆ Finset.range p := by
  classical
  exact Finset.filter_subset _ _

theorem mod_mem_tailSupport {A : Set ℕ} {N p a : ℕ} (hp : 0 < p)
    (ha : a ∈ A) (hlarge : N + p < a) : a % p ∈ tailSupport A N p := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (Nat.mod_lt a hp), ?_⟩
  have heq : ((a % p : ℕ) : ZMod p) = (a : ZMod p) := by simp
  rw [heq]
  exact ⟨a, ⟨ha, hlarge⟩, rfl⟩

theorem tailSupport_nonempty {A : Set ℕ} (hA : A.Infinite) (N p : ℕ)
    (hp : 0 < p) : (tailSupport A N p).Nonempty := by
  obtain ⟨_, a, ⟨ha, hlarge⟩, rfl⟩ := tailResidues_nonempty hA N p
  exact ⟨a % p, mod_mem_tailSupport hp ha hlarge⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_SignedQuadraticFrequency
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The signed Fourier series and its positive-frequency half -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap FourierTransform
open MeasureTheory

/-- Reality of the original physical cutoff supplies Hermitian symmetry of
its Fourier transform without any additional analytic input. -/
theorem fourier_real_conj (f : ℝ → ℂ) (hf : ∀ x, conj (f x) = f x) (ξ : ℝ) :
    𝓕 f (-ξ) = conj (𝓕 f ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul, map_mul, ← Complex.exp_conj, Complex.conj_ofReal,
    Complex.conj_I, hf]
  congr 2
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PositiveFourierCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A positive band-limited Schwartz cutoff

A narrow real even smooth bump has a real Fourier transform bounded away from
zero on the unit interval. Squaring this transform gives the required cutoff;
its Fourier support is controlled by the convolution of the original bumps.
-/

namespace Ostmann

open MeasureTheory
open scoped SchwartzMap FourierTransform ComplexConjugate Convolution

private theorem narrowSchwartz_apply (x : ℝ) : narrowSchwartz x = (narrowBump x : ℂ) := rfl

private theorem narrowSchwartz_even (x : ℝ) : narrowSchwartz (-x) = narrowSchwartz x := by
  simp only [narrowSchwartz_apply, narrowBump.neg]

private theorem narrow_fourier_real (x : ℝ) :
    conj (𝓕 narrowSchwartz x) = 𝓕 narrowSchwartz x := by
  have hr := fourier_real_conj narrowSchwartz (by intro y; simp [narrowSchwartz_apply]) x
  change conj (𝓕 (narrowSchwartz : ℝ → ℂ) x) = 𝓕 (narrowSchwartz : ℝ → ℂ) x
  rw [← hr]
  have he := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := ℝ))
    (narrowSchwartz : ℝ → ℂ) x
  have hh : (narrowSchwartz : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ = narrowSchwartz := by
    funext y
    exact narrowSchwartz_even y
  rw [hh] at he
  exact he.symm

private theorem narrow_fourier_lower (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ y : ℝ, narrowBump y) / 2 ≤ (𝓕 narrowSchwartz x).re := by
  let phase : ℝ → ℂ := fun y => Complex.exp ((-2 * Real.pi * y * x : ℝ) * Complex.I)
  have hc : HasCompactSupport (fun y : ℝ => narrowSchwartz y) := by
    change HasCompactSupport (Complex.ofReal ∘ (narrowBump : ℝ → ℝ))
    exact narrowBump.hasCompactSupport.comp_left (show Complex.ofReal 0 = 0 by simp)
  have hi : Integrable (fun y : ℝ => phase y * narrowSchwartz y) :=
    (by fun_prop : Continuous (fun y : ℝ => phase y * narrowSchwartz y)).integrable_of_hasCompactSupport hc.mul_left
  have hu : Integrable (narrowBump : ℝ → ℝ) :=
    narrowBump.continuous.integrable_of_hasCompactSupport narrowBump.hasCompactSupport
  have hphase (y : ℝ) : (phase y * narrowSchwartz y).re =
      Real.cos (-2 * Real.pi * y * x) * narrowBump y := by
    simp only [phase, narrowSchwartz_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.exp_ofReal_mul_I_re]
  have hire := hi.re
  change Integrable (fun y => (phase y * narrowSchwartz y).re) at hire
  have hint : Integrable (fun y => Real.cos (-2 * Real.pi * y * x) * narrowBump y) := by
    simpa only [hphase] using hire
  have he : (𝓕 narrowSchwartz x).re = ∫ y : ℝ, Real.cos (-2 * Real.pi * y * x) * narrowBump y := by
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
    change (∫ y : ℝ, phase y * narrowSchwartz y).re = _
    have hh := integral_re hi
    change (∫ y : ℝ, (phase y * narrowSchwartz y).re) = (∫ y : ℝ, phase y * narrowSchwartz y).re at hh
    rw [← hh]
    simp only [hphase]
  rw [he, div_eq_mul_inv, ← integral_mul_const]
  apply integral_mono (hu.mul_const _) hint
  · intro y
    by_cases hy : narrowBump y = 0
    · simp [hy]
    have hylt : |y| < 1 / 100 := by
      have hm : y ∈ Function.support narrowBump := hy
      rw [narrowBump.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hm
      exact hm
    have hxabs : |x| ≤ 1 := by rw [abs_of_nonneg hx.1]; exact hx.2
    have hang : |(-2 * Real.pi * y * x)| ≤ 1 := by
      rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (show (0 : ℝ) < 2 by norm_num), abs_of_pos Real.pi_pos]
      have hh := mul_le_mul (le_of_lt hylt) hxabs (abs_nonneg x) (by norm_num : (0 : ℝ) ≤ 1 / 100)
      nlinarith [Real.pi_lt_four, Real.pi_pos]
    have hcos : (1 / 2 : ℝ) ≤ Real.cos (-2 * Real.pi * y * x) := by
      have hs := (abs_le.mp hang)
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := -2 * Real.pi * y * x)]
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using mul_le_mul_of_nonneg_right hcos (narrowBump.nonneg' y)

private theorem narrow_integral_pos : 0 < ∫ y : ℝ, narrowBump y := by
  apply integral_pos_of_integrable_nonneg_nonzero narrowBump.continuous
    (narrowBump.continuous.integrable_of_hasCompactSupport narrowBump.hasCompactSupport)
    narrowBump.nonneg'
  have hh : narrowBump (0 : ℝ) = 1 := narrowBump.one_of_mem_closedBall (by
    simp only [Metric.mem_closedBall, dist_self]; exact narrowBump.rIn_pos.le)
  rw [hh]
  norm_num

private theorem schwartz_fourier_twice (f : 𝓢(ℝ, ℂ)) (x : ℝ) : 𝓕 (𝓕 f) x = f (-x) := by
  have hh := congrArg (fun g : 𝓢(ℝ, ℂ) => g (-x)) (show (𝓕⁻ (𝓕 f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) = f from FourierTransform.fourierInv_fourier_eq f)
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_neg] at hh
  exact hh

private theorem narrow_convolution_zero (x : ℝ) (hx : 1 ≤ |x|) :
    SchwartzMap.convolution (.mul ℂ ℂ) narrowSchwartz narrowSchwartz x = 0 := by
  rw [SchwartzMap.convolution_apply, convolution_def]
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  by_cases hy : 1 / 100 ≤ |y|
  · have hz : narrowBump y = 0 := narrowBump.zero_of_le_dist (by simpa [Real.dist_eq, narrowBump] using hy)
    simp [narrowSchwartz_apply, hz]
  · have hxy : 1 / 100 ≤ |x - y| := by
      have hh := abs_add_le (x - y) y
      rw [sub_add_cancel] at hh
      linarith
    have hz : narrowBump (x - y) = 0 := narrowBump.zero_of_le_dist (by simpa [Real.dist_eq, narrowBump] using hxy)
    simp [narrowSchwartz_apply, hz]

/-- The cutoff needed by the original amplified moment argument exists. -/
theorem exists_positive_even_fourier_cutoff :
    ∃ (c : ℝ) (ψ : 𝓢(ℝ, ℂ)), 0 < c ∧
      (∀ x, conj (ψ x) = ψ x) ∧ (∀ x, 0 ≤ (ψ x).re) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, c ≤ (ψ x).re) ∧
      (∀ x : ℝ, (3 : ℝ) ^ 2 < |x| → 𝓕 ψ x = 0) ∧
      (∀ x : ℝ, 𝓕 ψ (-x) = 𝓕 ψ x) := by
  let f := 𝓕 narrowSchwartz
  let ψ := SchwartzMap.pairing (.mul ℂ ℂ) f f
  let c := ((∫ y : ℝ, narrowBump y) / 2) ^ 2
  have hfreal (x : ℝ) : (f x).im = 0 := by
    have hh := congrArg Complex.im (narrow_fourier_real x)
    simp only [Complex.conj_im] at hh
    change -(f x).im = (f x).im at hh
    linarith
  have hψ (x : ℝ) : ψ x = f x * f x := rfl
  have hcpos := narrow_integral_pos
  refine ⟨c, ψ, by dsimp [c]; positivity, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simpa only [hψ, map_mul] using congrArg (fun z : ℂ => z * z) (narrow_fourier_real x)
  · intro x
    rw [hψ, Complex.mul_re, hfreal]
    nlinarith
  · intro x hx
    rw [hψ, Complex.mul_re, hfreal]
    have hl := narrow_fourier_lower x hx
    change (∫ y : ℝ, narrowBump y) / 2 ≤ (f x).re at hl
    dsimp [c]
    nlinarith [narrow_integral_pos]
  · intro x hx
    have he : ψ = 𝓕 (SchwartzMap.convolution (.mul ℂ ℂ) narrowSchwartz narrowSchwartz) :=
      (SchwartzMap.fourier_convolution _ _ _).symm
    rw [he, schwartz_fourier_twice]
    exact narrow_convolution_zero (-x) (by rw [abs_neg]; linarith)

  · intro x
    have hfEven (y : ℝ) : f (-y) = f y := by
      have he := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := ℝ))
        (narrowSchwartz : ℝ → ℂ) y
      have hh : (narrowSchwartz : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ = narrowSchwartz := by
        funext z
        exact narrowSchwartz_even z
      rw [hh] at he
      exact he.symm
    have hψEven : (ψ : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ = ψ := by
      funext y
      change f (-y) * f (-y) = f y * f y
      rw [hfEven]
    have he := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := ℝ))
      (ψ : ℝ → ℂ) x
    rw [hψEven] at he
    exact he.symm

/-- A positive Fourier cutoff with bounded derivatives and compact Fourier support. -/
theorem exists_positive_fourier_cutoff :
    ∃ (c : ℝ) (ψ : 𝓢(ℝ, ℂ)), 0 < c ∧
      (∀ x, conj (ψ x) = ψ x) ∧ (∀ x, 0 ≤ (ψ x).re) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, c ≤ (ψ x).re) ∧
      (∀ x : ℝ, (3 : ℝ) ^ 2 < |x| → 𝓕 ψ x = 0) := by
  obtain ⟨c, ψ, hc, hr, hp, hl, hs, _⟩ := exists_positive_even_fourier_cutoff
  exact ⟨c, ψ, hc, hr, hp, hl, hs⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingInitialCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal level-zero coefficient and its original cutoff -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingFrequencyCoefficient_levelZero (σ : Type) [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (s : ℤ) (small bulk : List σ) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G 0 s
      small bulk XL XR =
    movingGuardedLeaf value outside F ⟨0, .leaf s (small ++ bulk), XL, XR⟩ s := by
  unfold movingFrequencyCoefficient
  change (∑ t : Unit, _) = _
  rw [Finset.univ_unique, Finset.sum_singleton]
  unfold movingSupportedSampledWeight movingSampledWeight
  rw [← (movingSampleZeroEquiv σ).sum_comp]
  rw [Finset.univ_unique, Finset.sum_singleton]
  simp [movingSampleZeroEquiv, movingSamplesPrior, recursiveTransferWeight,
    buildMovingSlotData, frequencyRoot, flattenMovingSlots, movingRootedFrequencyTree]

theorem movingFrequencyCoefficient_levelZero_support (σ : Type) [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (s : ℤ) (small bulk : List σ) (XL XR : ℕ)
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G 0 s
      small bulk XL XR ≠ 0) :
    F ⟨0, .leaf s (small ++ bulk), XL, XR⟩ s ≠ 0 := by
  rw [movingFrequencyCoefficient_levelZero] at h
  unfold movingGuardedLeaf at h
  split_ifs at h
  · exact h
  · exact (h rfl).elim

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingProtectedTarget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The protected target from the actual initial window -/

namespace Ostmann
open Filter

theorem eventual_protected_target_error (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ totalGap td : ℝ,
      0 ≤ totalGap → totalGap ≤ C * L →
      0 ≤ td → td ≤ C * L * Real.exp ((1 / 1000 : ℝ) * L) →
      |totalGap - 2 * td| ≤ Real.exp ((1 / 100 : ℝ) * L) := by
  filter_upwards [arithmetic_exponent_absorption (1 / 1000) (1 / 100) 0 (2 * C) 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)] with L hrate
  intro totalGap td hgap0 hgap htd0 htd
  simp only [pow_one, one_mul, zero_mul, Real.exp_zero] at hrate
  rw [abs_le]
  constructor <;> nlinarith only [hgap0, hgap, htd0, htd, hrate]

theorem eventual_protected_cell_target_range :
    ∀ᶠ L : ℝ in atTop, ∀ J cb : ℝ,
      16 * Real.exp ((1 / 100 : ℝ) * L) ≤ J →
      J ≤ 32 * Real.exp ((1 / 100 : ℝ) * L) →
      0 ≤ cb → cb ≤ J / 4 →
      Real.exp ((1 / 100 : ℝ) * L) ≤ (J - cb) / 6 ∧
      (J - cb) / 6 ≤ Real.exp ((105 / 10000 : ℝ) * L) := by
  have ht : Tendsto (fun L : ℝ => Real.exp ((5 / 10000 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [ht.eventually (eventually_ge_atTop (8 : ℝ))] with L hratio
  intro J cb hJlo hJhi hcb0 hcb
  have hs := mul_le_mul_of_nonneg_right hratio (Real.exp_nonneg ((1 / 100 : ℝ) * L))
  have heq : Real.exp ((5 / 10000 : ℝ) * L) * Real.exp ((1 / 100 : ℝ) * L) =
      Real.exp ((105 / 10000 : ℝ) * L) := by rw [← Real.exp_add]; congr 1; ring
  rw [heq] at hs
  constructor <;> nlinarith only [hJlo, hJhi, hcb0, hcb, hs,
    Real.exp_nonneg ((1 / 100 : ℝ) * L)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticResidueTests
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual quadratic tests on complementary residue supports -/

namespace Ostmann

open scoped BigOperators Classical

theorem quadraticResidueTest_eq_character (p : ℕ) [NeZero p] (t : ℤ) (r : ℕ) :
    quadraticResidueTest p t r = jacobiCharacter p ((r : ZMod p) - (t : ZMod p)) := by
  rw [quadraticResidueTest, ← jacobiCharacter_intCast]
  simp only [Int.cast_sub, Int.cast_natCast]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_TailCollisionCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The square-root prime cutoff and its logarithmic collision budget -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem tailCollisionCutoff_bounds (L : ℝ) (hL : 1 ≤ L)
    (hr : 2 ≤ Real.exp (L / 2) / L ^ 5) :
    1 ≤ tailCollisionCutoff L ∧
    (tailCollisionCutoff L : ℝ) ≤ Real.exp (L / 2) / L ^ 5 ∧
    L / 2 - 5 * Real.log L - Real.log 2 ≤ Real.log (tailCollisionCutoff L : ℝ) := by
  have hLp : 0 < L := by linarith
  have hrp : 0 < Real.exp (L / 2) / L ^ 5 := by positivity
  have hQ : 1 ≤ tailCollisionCutoff L := (Nat.one_le_floor_iff _).mpr (show (1 : ℝ) ≤ _ by linarith)
  have hhalf : (Real.exp (L / 2) / L ^ 5) / 2 ≤ (tailCollisionCutoff L : ℝ) := by
    have hh := Nat.sub_one_lt_floor (Real.exp (L / 2) / L ^ 5)
    change Real.exp (L / 2) / L ^ 5 - 1 < (tailCollisionCutoff L : ℝ) at hh
    linarith
  refine ⟨hQ, Nat.floor_le hrp.le, ?_⟩
  have hh := Real.log_le_log (show 0 < (Real.exp (L / 2) / L ^ 5) / 2 by positivity) hhalf
  rw [Real.log_div (ne_of_gt hrp) (by norm_num),
    Real.log_div (Real.exp_ne_zero _) (pow_ne_zero 5 hLp.ne'),
    Real.log_exp, Real.log_pow] at hh
  exact hh

theorem eventual_tailCollisionCutoff (N : ℕ) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ 2 ≤ Real.exp (L / 2) / L ^ 5 ∧
      N + tailCollisionCutoff L ≤ summandTailCutoff L := by
  have hb := ((isLittleO_pow_exp_pos_mul_atTop 5 (show (0 : ℝ) < 1 / 2 by norm_num)).const_mul_left 2).bound
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hb, eventually_ge_atTop (3 * ((N : ℝ) + 3))] with L hb hL
  have hL1 : 1 ≤ L := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hLp : 0 < L := by linarith
  have hpoly : 2 * L ^ 5 ≤ Real.exp (L / 2) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) * L ^ 5),
      abs_of_pos (Real.exp_pos _), one_mul, one_div_mul_eq_div] using hb
  have hr : 2 ≤ Real.exp (L / 2) / L ^ 5 := (le_div_iff₀ (pow_pos hLp 5)).mpr hpoly
  have hQ := (tailCollisionCutoff_bounds L hL1 hr).2.1
  have hQ' : (tailCollisionCutoff L : ℝ) ≤ Real.exp (L / 2) := hQ.trans
    (div_le_self (Real.exp_nonneg _) (one_le_pow₀ hL1))
  have he : (1 : ℝ) ≤ Real.exp (L / 2) := Real.one_le_exp (by positivity)
  have hN : (N : ℝ) + 3 ≤ Real.exp (2 * L / 5) := by
    have := Real.add_one_le_exp (2 * L / 5)
    linarith
  have hmul := mul_le_mul_of_nonneg_left hN (Real.exp_nonneg (L / 2))
  have hexp : Real.exp (L / 2) * Real.exp (2 * L / 5) = Real.exp (9 * L / 10) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp] at hmul
  have hN0 : 0 ≤ (N : ℝ) + 2 := by positivity
  have hprod := mul_nonneg (sub_nonneg.mpr he) hN0
  have hfloor := Nat.sub_one_lt_floor (Real.exp (9 * L / 10))
  change Real.exp (9 * L / 10) - 1 < (summandTailCutoff L : ℝ) at hfloor
  have hfinal : (N : ℝ) + tailCollisionCutoff L ≤ (summandTailCutoff L : ℝ) := by
    nlinarith only [hmul, hprod, hfloor, hQ']
  exact ⟨hL1, hr, by exact_mod_cast hfinal⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_TailDensityMask
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual residue masks for the positive endpoint tail -/

namespace Ostmann

open scoped Classical

theorem tailDensityMask_card (A : Set ℕ) (N p : ℕ) :
    (tailDensityMask A N p).card = (tailSupport A N p).card := by
  apply Finset.card_image_of_injOn
  intro r hr s hs he
  have hrp := Finset.mem_range.mp (tailSupport_subset A N p hr)
  have hsp := Finset.mem_range.mp (tailSupport_subset A N p hs)
  have hmod := (ZMod.natCast_eq_natCast_iff' r s p).mp he
  simpa only [Nat.mod_eq_of_lt hrp, Nat.mod_eq_of_lt hsp] using hmod

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailCellWindow
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected small cells lie below the actual collision cutoff -/

namespace Ostmann
open Filter

theorem eventual_tail_cell_window (a C H : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ X target : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ X → X ≤ Real.exp L →
      Real.exp ((1 / 100 : ℝ) * L) ≤ target →
      target ≤ Real.exp ((11 / 1000 : ℝ) * L) →
      H ≤ target ∧
      target + 64 * tailDefectBudget a C X + 2 ≤ Real.log (tailCollisionCutoff X : ℝ) ∧
      target + 64 * tailDefectBudget a C X + 1 ≤ Real.exp (L / 2) := by
  let D := 256 * C + 256 * Real.log 2 + 128 * Real.log 4 / a + Real.log 2 + 2
  let K := 1290 + |D|
  have hK : 1 ≤ K := by dsimp [K]; linarith [abs_nonneg D]
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (eventual_tailCollisionCutoff 0)
  have ht (b : ℝ) (hb : 0 < b) : Tendsto (fun L : ℝ => Real.exp (b * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hb)
  filter_upwards [arithmetic_exponent_absorption (11 / 1000) (4 / 100) 0 K (1 / 2) 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    arithmetic_exponent_absorption (11 / 1000) (1 / 2) 0 K 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    (ht (4 / 100) (by norm_num)).eventually (eventually_ge_atTop X₀),
    (ht (1 / 100) (by norm_num)).eventually (eventually_ge_atTop H),
    eventually_ge_atTop (1 : ℝ)] with L hgap hlarge hX0 hH hL
  intro X target hXlo hXhi htlo hthi
  have hcut := hX₀ X (hX0.trans hXlo)
  have hlogX : Real.log X ≤ L := by
    have h := Real.log_le_log (by linarith [hcut.1] : 0 < X) hXhi
    rwa [Real.log_exp] at h
  have htail := (tailCollisionCutoff_bounds X hcut.1 hcut.2.1).2.2
  have hlinear : 1285 * L + D ≤ K * L := by
    have hD := le_abs_self D
    have hDL := mul_le_mul_of_nonneg_left hL (abs_nonneg D)
    dsimp [K]
    nlinarith only [hD, hDL, hL]
  have hprod : Real.exp ((11 / 1000 : ℝ) * L) ≤
      K * L * Real.exp ((11 / 1000 : ℝ) * L) := by
    have hKL : 1 ≤ K * L := hL.trans (le_mul_of_one_le_left (by linarith) hK)
    exact le_mul_of_one_le_left (Real.exp_nonneg _) hKL
  have hbound : target + 64 * tailDefectBudget a C X + 2 +
      5 * Real.log X + Real.log 2 ≤ K * L + K * L * Real.exp ((11 / 1000 : ℝ) * L) := by
    calc
      _ = target + 1285 * Real.log X + D := by dsimp [tailDefectBudget, D]; ring
      _ ≤ Real.exp ((11 / 1000 : ℝ) * L) + 1285 * L + D := by linarith
      _ ≤ _ := by linarith only [hlinear, hprod]
  simp only [pow_one, zero_mul, Real.exp_zero] at hgap hlarge
  refine ⟨hH.trans htlo, ?_, ?_⟩
  · nlinarith only [hbound, hgap, htail, hXlo]
  · have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg hcut.1
    have hexp : Real.exp ((1 / 2 : ℝ) * L) = Real.exp (L / 2) := by congr 1; ring
    rw [hexp] at hlarge
    nlinarith only [hbound, hlarge, hlog2, hlogX0]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailSieveMasks
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two complementary residue masks used by the integer-tail sieve -/
namespace Ostmann
open scoped Classical

theorem tailDensityMask_nonempty {A : Set ℕ} (hA : A.Infinite) (N p : ℕ) (hp : 0 < p) :
    (tailDensityMask A N p).Nonempty :=
  (tailSupport_nonempty hA N p hp).image _

theorem tailDensityMask_eq_tailResidues (A : Set ℕ) (N p : ℕ) [NeZero p] (_hp : 0 < p) :
    (tailDensityMask A N p : Set (ZMod p)) = tailResidues A N p := by
  ext x
  constructor
  · intro hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hr).2
  · intro hx
    apply Finset.mem_image.mpr
    exact ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt x), by simpa⟩,
      ZMod.natCast_zmod_val x⟩

theorem tailDensityMask_complement_nonempty {A B : Set ℕ} (hB : B.Infinite)
    (N p : ℕ) [NeZero p] (hp : 0 < p)
    (hdis : Disjoint (tailResidues A N p) (negTailResidues B N p)) :
    (Finset.univ \ tailDensityMask A N p).Nonempty := by
  obtain ⟨x, hx, hlarge⟩ := hB.exists_gt (N + p)
  refine ⟨-(x : ZMod p), Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  intro hm
  have hh : -(x : ZMod p) ∈ tailResidues A N p :=
    (tailDensityMask_eq_tailResidues A N p hp) ▸ hm
  exact Set.disjoint_left.mp hdis hh ⟨x, ⟨hx, hlarge⟩, rfl⟩

theorem tailDensityMask_card_lt {A B : Set ℕ} (hB : B.Infinite)
    (N p : ℕ) [NeZero p] (hp : 0 < p)
    (hdis : Disjoint (tailResidues A N p) (negTailResidues B N p)) :
    (tailDensityMask A N p).card < p := by
  have ht := Finset.card_pos.mpr (tailDensityMask_complement_nonempty hB N p hp hdis)
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, ZMod.card] at ht
  omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingProductFrequency
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer frequency cutoffs that retain the actual product-window center -/
namespace Ostmann

theorem movingProductExponent_monotone (T : ℕ → ℝ) (W : ℝ)
    (hgap : ∀ n, 2 * T n ≤ movingProductExponent T W n) :
    Monotone (movingProductExponent T W) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [movingProductExponent]
  linarith [hgap n]

theorem movingProductNaturalCutoff_monotone (T : ℕ → ℝ) (W Y m : ℝ)
    (hgap : ∀ n, 2 * T n ≤ movingProductExponent T W n) :
    Monotone (movingProductNaturalCutoff T W Y m) := by
  intro i j hij
  apply Nat.floor_mono
  apply Real.exp_le_exp.mpr
  have hE := movingProductExponent_monotone T W hgap hij
  have hpow : (2 : ℝ) ^ i ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hij
  have hs := mul_le_mul_of_nonneg_right hpow (Real.sqrt_nonneg (4 * m))
  dsimp only [movingProductFrequencyExponent]
  linarith

theorem movingProductFrequency_reserve (T : ℕ → ℝ) (W Y m : ℝ) (n : ℕ) :
    movingProductFrequencyExponent T W Y m (n + 1) -
      (movingProductFrequencyExponent T W Y m n + movingProductExponent T W n - 2 * T n) =
      (2 : ℝ) ^ n * Real.sqrt (4 * m) := by
  simp only [movingProductFrequencyExponent, movingProductExponent, pow_succ]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingProductInitialCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Centered initial windows and the original energy cutoff -/
namespace Ostmann
open Filter

/-- The initial cutoff depends on the quotient of the two product scales. -/
theorem movingProductNaturalCutoff_zero_translate (T : ℕ → ℝ) (W Y m D : ℝ) :
    movingProductNaturalCutoff T (W - D) (Y - D) m 0 =
      movingProductNaturalCutoff T W Y m 0 := by
  unfold movingProductNaturalCutoff movingProductFrequencyExponent
  simp only [movingProductExponent]
  congr 2
  ring

/-- Using one quarter of the bulk mass in the frequency reserve leaves room
for the fixed width of the actual initial product window. The diagonal energy
estimate retains its original `sqrt (4m)` cutoff. -/
theorem movingProductNaturalCutoff_zero_window (T : ℕ → ℝ)
    (W Y Δ m H : ℝ) (hW : W - Y ≤ Δ + H)
    (hwidth : H ≤ Real.sqrt m) :
    (movingProductNaturalCutoff T W Y (m / 4) 0 : ℝ) ≤
      Real.exp (Δ + Real.sqrt (4 * m)) := by
  have hs : Real.sqrt (4 * m) = 2 * Real.sqrt m := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hq : 4 * (m / 4) = m := by ring
  have he : movingProductFrequencyExponent T W Y (m / 4) 0 ≤
      Δ + Real.sqrt (4 * m) := by
    simp only [movingProductFrequencyExponent, movingProductExponent, pow_zero, one_mul, hq]
    rw [hs]
    linarith
  exact (Nat.floor_le (Real.exp_pos _).le).trans (Real.exp_le_exp.mpr he)

theorem eventually_initial_product_reserve (H : ℝ) :
    ∀ᶠ m : ℝ in atTop, 64 ≤ m / 4 ∧ H ≤ Real.sqrt m := by
  filter_upwards [eventually_ge_atTop (256 : ℝ),
    Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop H)] with m hm hH
  exact ⟨by linarith, hH⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTargetTotal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The backwards target construction preserves the original total log size -/

namespace Ostmann
open scoped BigOperators

theorem movingCompensationTargetError_ofFn (k : ℕ) (d : Fin k → ℝ) :
    movingCompensationTargetError (List.ofFn d) = ∑ i : Fin k, (2 : ℝ) ^ (i : ℕ) * d i := by
  induction k with
  | zero => simp [movingCompensationTargetError]
  | succ k ih =>
    rw [List.ofFn_succ, movingCompensationTargetError, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ]
    calc
      _ = d 0 + ∑ i : Fin k, 2 * (2 ^ (i : ℕ) * d i.succ) := by
        rw [← Finset.mul_sum]
        ring
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring

theorem movingCompensationTargetError_gaps (k : ℕ) (BD Bz L : ℝ) :
    movingCompensationTargetError (movingCompensationGaps k BD Bz L) =
      ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4) ((2 : ℝ) ^ (i : ℕ))
        (spectatorBulkCount k L) := by
  unfold movingCompensationGaps
  rw [movingCompensationTargetError_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  have hr : (2 : ℝ) ^ (i : ℕ) ≠ 0 := by positivity
  field_simp

theorem moving_protected_and_compensation_total (k : ℕ) (BD Bz L logX G td Δ₀ : ℝ) :
    let gaps := movingCompensationGaps k BD Bz L
    let J := movingProtectedTarget k logX G td
      (Δ₀ + ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4)
        ((2 : ℝ) ^ (i : ℕ)) (spectatorBulkCount k L))
    2 * G + 2 * td + J + (movingCompensationTargets J gaps).sum = logX + Δ₀ := by
  intro gaps J
  have hs := movingCompensationTargets_sum J gaps
  have hlen : gaps.length = k := movingCompensationGaps_length k BD Bz L
  rw [hlen, movingCompensationTargetError_gaps] at hs
  have hJ : (2 : ℝ) ^ k * J = logX - 2 * G - 2 * td +
      (Δ₀ + ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4)
        ((2 : ℝ) ^ (i : ℕ)) (spectatorBulkCount k L)) := by
    dsimp [J, movingProtectedTarget]
    field_simp
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterHigherBias
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform translated higher-order character bias of the actual residue supports -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem translatedResidueCharacterMean_norm_le_one (A : Set ℕ) (N p : ℕ)
    (χ : DirichletCharacter ℂ p) (t : ZMod p) :
    ‖translatedResidueCharacterMean A N p χ t‖ ≤ 1 := by
  unfold translatedResidueCharacterMean
  rw [norm_div, Complex.norm_natCast]
  have hs : ‖∑ r ∈ tailSupport A N p, χ ((r : ZMod p) - t)‖ ≤ (tailSupport A N p).card := by
    calc
      _ ≤ ∑ r ∈ tailSupport A N p, ‖χ ((r : ZMod p) - t)‖ := norm_sum_le _ _
      _ ≤ ∑ _r ∈ tailSupport A N p, (1 : ℝ) := Finset.sum_le_sum (fun _ _ => χ.norm_le_one _)
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hs (Nat.cast_nonneg _)).trans (div_self_le_one _)

theorem higherCharacterBias_nonneg (A : Set ℕ) (N p : ℕ) : 0 ≤ higherCharacterBias A N p := by
  apply le_csSup _ (Set.mem_insert 0 _)
  refine ⟨1, ?_⟩
  rintro r (rfl | ⟨χ, _, t, rfl⟩)
  · norm_num
  · exact translatedResidueCharacterMean_norm_le_one A N p χ t

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_NormalizedResidueFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single family of normalized transforms for varying sampled primes -/

namespace Ostmann
open scoped Classical BigOperators

theorem normalizedResidueFamily_eq (sets : ∀ q : ℕ, Finset (ZMod q))
    (q : ℕ) [NeZero q] :
    normalizedResidueFamily sets q = normalizedResidueTransform (sets q) := by
  simp only [normalizedResidueFamily, dite_eq_right (NeZero.ne q)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_MaximalQuadraticBias
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Maximizing translating residues and the little-o conclusion -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

theorem quadraticResidueTest_translate_congr (p : ℕ) [NeZero p] (t u : ℤ)
    (htu : (t : ZMod p) = (u : ZMod p)) :
    quadraticResidueTest p t = quadraticResidueTest p u := by
  funext r
  rw [quadraticResidueTest_eq_character, quadraticResidueTest_eq_character, htu]

theorem translated_quadratic_bias_le_maximal (S : Finset ℕ) (p : ℕ) [NeZero p] (t : ℤ) :
    |residueTestMean S (quadraticResidueTest p t)| ≤ maximalQuadraticBias S p := by
  have hm := (Classical.choose_spec (Finset.exists_max_image (Finset.range (p + 1))
    (fun t : ℕ => |residueTestMean S (quadraticResidueTest p t)|)
    (Finset.nonempty_range_iff.mpr (by omega)))).2
  have he : (t : ZMod p) = (((t : ZMod p).val : ℕ) : ℤ) := by simp
  rw [quadraticResidueTest_translate_congr p t _ he]
  exact hm _ (Finset.mem_range.mpr (by have := ZMod.val_lt (t : ZMod p); omega))

theorem maximalQuadraticBias_nonneg (S : Finset ℕ) (p : ℕ) : 0 ≤ maximalQuadraticBias S p :=
  abs_nonneg _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PrimeQuadraticUniqueness
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The only nonprincipal quadratic character at a prime -/
namespace Ostmann

theorem prime_character_eq_of_square_eq_one {p : ℕ} [Fact p.Prime]
    (χ ψ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (hχ2 : χ ^ 2 = 1) (hψ2 : ψ ^ 2 = 1) : χ = ψ := by
  obtain ⟨g, hg⟩ := exists_zpow_surjective (ZMod p)ˣ
  have hext (φ θ : DirichletCharacter ℂ p) (heq : φ g = θ g) : φ = θ := by
    apply MulChar.equivToUnitHom.injective
    apply MonoidHom.ext
    intro u
    obtain ⟨z, rfl⟩ := hg u
    change φ.toUnitHom (g ^ z) = θ.toUnitHom (g ^ z)
    rw [map_zpow, map_zpow]
    congr 1
    exact Units.ext heq
  have hneg (φ : DirichletCharacter ℂ p) (hφ : φ ≠ 1) (hφ2 : φ ^ 2 = 1) : φ g = -1 := by
    have hs : φ g ^ 2 = 1 := by
      have hh := congrArg (fun θ : DirichletCharacter ℂ p => θ g) hφ2
      simpa only [MulChar.pow_apply_coe, MulChar.one_apply g.isUnit] using hh
    rcases sq_eq_one_iff.mp hs with hh | hh
    · exact (hφ (hext φ 1 (by simpa only [MulChar.one_apply g.isUnit] using hh))).elim
    · exact hh
  exact hext χ ψ ((hneg χ hχ hχ2).trans (hneg ψ hψ hψ2).symm)

theorem complexJacobiCharacter_square {p : ℕ} [Fact p.Prime] :
    complexJacobiCharacter p ^ 2 = 1 := by
  apply MulChar.IsQuadratic.sq_eq_one
  change ((jacobiCharacterInt p).ringHomComp (Int.castRingHom ℂ)).IsQuadratic
  rw [jacobiCharacterInt_prime]
  exact (quadraticChar_isQuadratic (ZMod p)).comp _

theorem complexJacobiCharacter_ne_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    complexJacobiCharacter p ≠ 1 := by
  have hc : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp2
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hc
  intro he
  have hev := congrArg (fun χ : DirichletCharacter ℂ p => χ a) he
  have hneg : complexJacobiCharacter p a = -1 := by
    simp only [complexJacobiCharacter, MulChar.ringHomComp_apply, jacobiCharacterInt_prime]
    rw [ha]
    norm_num
  rw [hneg, MulChar.one_apply a.isUnit] at hev
  norm_num at hev

theorem prime_quadratic_character_unique {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (hχ2 : χ ^ 2 = 1) :
    χ = complexJacobiCharacter p :=
  prime_character_eq_of_square_eq_one χ _ hχ (complexJacobiCharacter_ne_one hp2)
    hχ2 complexJacobiCharacter_square

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TailCharacterBias
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both character orders control the actual tail transform -/
namespace Ostmann
open scoped Classical BigOperators

theorem translated_complexJacobi_mean (A : Set ℕ) (N p : ℕ) [NeZero p] (t : ZMod p) :
    translatedResidueCharacterMean A N p (complexJacobiCharacter p) t =
      (residueTestMean (tailSupport A N p) (quadraticResidueTest p (t.val : ℤ)) : ℂ) := by
  have ht : ((t.val : ℤ) : ZMod p) = t := by simp
  have he (r : ℕ) : complexJacobiCharacter p ((r : ZMod p) - t) =
      (quadraticResidueTest p (t.val : ℤ) r : ℂ) := by
    rw [quadraticResidueTest_eq_character, ht]
    simp only [complexJacobiCharacter, jacobiCharacter, MulChar.ringHomComp_apply]
    norm_cast
  simp only [translatedResidueCharacterMean, he, residueTestMean,
    Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast]

theorem translatedResidueCharacterMean_norm_le_higher (A : Set ℕ) (N p : ℕ)
    (χ : DirichletCharacter ℂ p) (hχ : χ ^ 2 ≠ 1) (t : ZMod p) :
    ‖translatedResidueCharacterMean A N p χ t‖ ≤ higherCharacterBias A N p := by
  unfold higherCharacterBias
  refine le_csSup ?_ (Or.inr ⟨χ, hχ, t, rfl⟩)
  refine ⟨1, ?_⟩
  rintro r (rfl | ⟨ψ, _, u, rfl⟩)
  · norm_num
  · exact translatedResidueCharacterMean_norm_le_one A N p ψ u

theorem translated_tail_character_mean_bound (A : Set ℕ) (N p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (t : ZMod p) :
    ‖translatedResidueCharacterMean A N p χ t‖ ≤
      maximalQuadraticBias (tailSupport A N p) p + higherCharacterBias A N p := by
  by_cases hχ2 : χ ^ 2 = 1
  · rw [prime_quadratic_character_unique hp2 χ hχ hχ2, translated_complexJacobi_mean,
      Complex.norm_real, Real.norm_eq_abs]
    exact (translated_quadratic_bias_le_maximal (tailSupport A N p) p (t.val : ℤ)).trans
      (le_add_of_nonneg_right (higherCharacterBias_nonneg A N p))
  · exact (translatedResidueCharacterMean_norm_le_higher A N p χ hχ2 t).trans
      (le_add_of_nonneg_left (maximalQuadraticBias_nonneg (tailSupport A N p) p))

theorem tailDensityMask_character_mean (A : Set ℕ) (N p : ℕ)
    (χ : DirichletCharacter ℂ p) (t : ZMod p) :
    ((tailDensityMask A N p).card : ℂ)⁻¹ *
      (∑ x ∈ tailDensityMask A N p, χ (x - t)) = translatedResidueCharacterMean A N p χ t := by
  rw [tailDensityMask_card]
  have hi : Set.InjOn (fun r : ℕ => (r : ZMod p)) (tailSupport A N p) := by
    intro r hr s hs he
    have hrp := Finset.mem_range.mp (tailSupport_subset A N p hr)
    have hsp := Finset.mem_range.mp (tailSupport_subset A N p hs)
    have hm := (ZMod.natCast_eq_natCast_iff' r s p).mp he
    simpa only [Nat.mod_eq_of_lt hrp, Nat.mod_eq_of_lt hsp] using hm
  rw [tailDensityMask, Finset.sum_image hi]
  exact (div_eq_inv_mul _ _).symm

theorem tailDensityMask_reverse_character_mean_bound (A : Set ℕ) (N p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (a : ZMod p) :
    ‖((tailDensityMask A N p).card : ℂ)⁻¹ *
      (∑ x ∈ tailDensityMask A N p, χ⁻¹ (-a - x))‖ ≤
      maximalQuadraticBias (tailSupport A N p) p + higherCharacterBias A N p := by
  have he (x : ZMod p) : χ⁻¹ (-a - x) = χ⁻¹ (-1) * χ⁻¹ (x - (-a)) := by
    rw [← map_mul]
    congr 1
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, ← mul_assoc, mul_comm _ (χ⁻¹ (-1)), mul_assoc,
    tailDensityMask_character_mean, norm_mul]
  have hunit : ‖χ⁻¹ (-1 : ZMod p)‖ = 1 := by
    exact norm_mulChar_unit χ⁻¹ (-1 : (ZMod p)ˣ)
  rw [hunit, one_mul]
  exact translated_tail_character_mean_bound A N p hp2 χ⁻¹ (inv_ne_one.mpr hχ) (-a)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RoundedProtectedTarget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The protected target at the rounded integral endpoint -/
namespace Ostmann

theorem movingProtectedTarget_rounded_bounds (k : ℕ) (hk : 2 ≤ k)
    (h lo G Y td totalGap : ℝ) (hh : 1 ≤ h)
    (hYlo : 2 * lo + 2 ^ (k + 1) * (12 * h) ≤ Y)
    (hYhi : Y ≤ 2 * lo + 2 ^ (k + 1) * (12 * h) + 1)
    (hGlo : lo - 2 ≤ G) (hGhi : G ≤ lo - 2 + 12 * h)
    (herror : |totalGap - 2 * td| ≤ h) :
    16 * h ≤ movingProtectedTarget k Y G td totalGap ∧
      movingProtectedTarget k Y G td totalGap ≤ 32 * h := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have hp4 : (4 : ℝ) ≤ 2 ^ k := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
    norm_num at hh
    exact hh
  have hph := mul_le_mul_of_nonneg_right hp4 (show 0 ≤ h by linarith)
  obtain ⟨herrlo, herrhi⟩ := abs_le.mp herror
  unfold movingProtectedTarget
  rw [le_div_iff₀ hp, div_le_iff₀ hp]
  rw [pow_succ] at hYlo hYhi
  constructor <;> nlinarith only [hYlo, hYhi, hGlo, hGhi, herrlo, herrhi, hph, hh]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialProtectedTarget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual two cutoff centers fit the protected target -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem movingInitialGapTotal_linear (k : ℕ) (Bs BD Bz L : ℝ) :
    movingInitialGapTotal k Bs BD Bz L =
      (spectatorBaseGap Bs ((k : ℝ) ^ 4) 1 +
        ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4) ((2 : ℝ) ^ (i : ℕ)) 1) *
          spectatorBulkCount k L := by
  simp only [movingInitialGapTotal, spectatorBaseGap, spectatorStepGap, mul_one,
    add_mul, Finset.sum_mul]

theorem initial_log_center_bounds (m : ℕ) (T : ℝ) (c : ℤ)
    (hc : c ∈ Finset.Icc (0 : ℤ) ⌈(m / 2 : ℕ) * Real.exp T⌉₊) :
    0 ≤ (c : ℝ) ∧ (c : ℝ) ≤ (m : ℝ) * Real.exp T + 1 := by
  have hc0 : 0 ≤ (c : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hc).1
  have hcu : (c : ℝ) ≤ (⌈(m / 2 : ℕ) * Real.exp T⌉₊ : ℕ) := by
    exact_mod_cast (Finset.mem_Icc.mp hc).2
  have hn : ((m / 2 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.div_le_self m 2
  have he := Nat.ceil_lt_add_one (show 0 ≤ ((m / 2 : ℕ) : ℝ) * Real.exp T by positivity)
  exact ⟨hc0, hcu.trans (he.le.trans (by gcongr))⟩

theorem eventual_initial_protected_target (k : ℕ) (hk : 2 ≤ k)
    (Bs BD Bz : ℝ) (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) :
    ∀ᶠ L : ℝ in atTop, ∀ cb cd : ℤ,
      cb ∈ Finset.Icc (0 : ℤ)
        ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 1000 : ℝ) * L)⌉₊ →
      cd ∈ Finset.Icc (0 : ℤ)
        ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 10000 : ℝ) * L)⌉₊ →
      ∀ lo G Y : ℝ,
      2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) ≤ Y →
      Y ≤ 2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) + 1 →
      lo - 2 ≤ G → G ≤ lo - 2 + 12 * Real.exp ((1 / 100 : ℝ) * L) →
      let J := movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L)
      16 * Real.exp ((1 / 100 : ℝ) * L) ≤ J ∧
      J ≤ 32 * Real.exp ((1 / 100 : ℝ) * L) ∧
      0 ≤ 2 * (cb : ℝ) ∧ 2 * (cb : ℝ) ≤ J / 4 := by
  let z : ℝ := (k : ℝ) ^ 4
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hz1 : 1 ≤ z := one_le_pow₀ (by exact_mod_cast (show 1 ≤ k by omega))
  have hlogz : 0 ≤ Real.log z := Real.log_nonneg hz1
  let R := spectatorBaseGap Bs z 1 +
    ∑ i : Fin k, spectatorStepGap BD Bz z ((2 : ℝ) ^ (i : ℕ)) 1
  have hR : 0 ≤ R := by
    dsimp only [R, spectatorBaseGap]
    apply add_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro i _
    have hl : 0 ≤ Real.log ((2 : ℝ) ^ (i : ℕ)) :=
      Real.log_nonneg (one_le_pow₀ (by norm_num))
    dsimp only [spectatorStepGap]
    positivity
  let C := max (R * z) (z + 1)
  have hC : 0 ≤ C := (by linarith only [hz] : 0 ≤ z + 1).trans (le_max_right _ _)
  filter_upwards [eventual_protected_target_error C,
    arithmetic_exponent_absorption (6 / 1000) (1 / 100) 0 (z + 1) 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L herror hsmall hL
  intro cb cd hcb hcd lo G Y hYlo hYhi hGlo hGhi J
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hm : (spectatorBulkCount k L : ℝ) ≤ z * L := spectatorBulkCount_upper k L hL0
  obtain ⟨hcb0, hcbU⟩ := initial_log_center_bounds _ _ cb hcb
  obtain ⟨hcd0, hcdU⟩ := initial_log_center_bounds _ _ cd hcd
  have he : Real.exp ((6 / 10000 : ℝ) * L) ≤ Real.exp ((1 / 1000 : ℝ) * L) :=
    Real.exp_le_exp.mpr (by linarith only [hL0])
  have hE : 1 ≤ Real.exp ((1 / 1000 : ℝ) * L) := Real.one_le_exp (by positivity)
  have hcd1 : (cd : ℝ) ≤ z * L * Real.exp ((1 / 1000 : ℝ) * L) + 1 := by
    have hh := mul_le_mul hm he (Real.exp_nonneg _) (show 0 ≤ z * L by positivity)
    linarith only [hcdU, hh]
  have hcdC : (cd : ℝ) ≤ C * L * Real.exp ((1 / 1000 : ℝ) * L) := by
    have hc := mul_le_mul_of_nonneg_right (le_max_right (R * z) (z + 1))
      (mul_nonneg hL0 (Real.exp_nonneg ((1 / 1000 : ℝ) * L)))
    have hLE : 1 ≤ L * Real.exp ((1 / 1000 : ℝ) * L) := by nlinarith only [hL, hE]
    dsimp only [C]
    nlinarith only [hcd1, hc, hLE]
  have hgap0 : 0 ≤ movingInitialGapTotal k Bs BD Bz L := by
    rw [movingInitialGapTotal_linear]
    exact mul_nonneg hR (Nat.cast_nonneg _)
  have hgapU : movingInitialGapTotal k Bs BD Bz L ≤ C * L := by
    rw [movingInitialGapTotal_linear]
    have hh := mul_le_mul_of_nonneg_right (le_max_left (R * z) (z + 1)) hL0
    have hh' := mul_le_mul_of_nonneg_left hm hR
    change R * (spectatorBulkCount k L : ℝ) ≤ C * L
    dsimp only [C]
    nlinarith only [hh, hh']
  have herr := herror _ cd hgap0 hgapU hcd0 hcdC
  obtain ⟨hJlo, hJhi⟩ := movingProtectedTarget_rounded_bounds k hk _ lo G Y cd _
    (Real.one_le_exp (by positivity)) hYlo hYhi hGlo hGhi herr
  have hcb1 : (cb : ℝ) ≤ z * L * Real.exp ((6 / 1000 : ℝ) * L) + 1 := by
    have hh := mul_le_mul_of_nonneg_right hm (Real.exp_nonneg ((6 / 1000 : ℝ) * L))
    linarith only [hcbU, hh]
  simp only [pow_one, zero_mul, Real.exp_zero, one_mul] at hsmall
  have hmul : 0 ≤ (z + 1) * L := mul_nonneg (by positivity) hL0
  have hcb2 : (cb : ℝ) ≤ Real.exp ((1 / 100 : ℝ) * L) := by
    have hh : 0 ≤ L * Real.exp ((6 / 1000 : ℝ) * L) := by positivity
    nlinarith only [hcb1, hsmall, hmul, hh]
  exact ⟨hJlo, hJhi, by linarith only [hcb0], by
    dsimp only [J]
    linarith only [hJlo, hcb2, Real.exp_nonneg ((1 / 100 : ℝ) * L)]⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedCellGap
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected actual cells discharge the diagonal's geometric gap -/

namespace Ostmann
open scoped Classical BigOperators

theorem tailCellLinearRate_nonneg (a C : ℝ) : 0 ≤ tailCellLinearRate a C := by
  unfold tailCellLinearRate
  positivity

theorem tailDefectBudget_linear (a C L X : ℝ) (hL : 1 ≤ L)
    (hX : 0 < X) (hXupper : X ≤ Real.exp L) :
    tailDefectBudget a C X ≤ tailCellLinearRate a C * L := by
  have hlog : Real.log X ≤ L := by
    have h := Real.log_le_log hX hXupper
    rwa [Real.log_exp] at h
  have hc := le_abs_self (4 * C + 4 * Real.log 2 + 2 * Real.log 4 / a)
  have hcl := mul_le_mul_of_nonneg_left hL
    (abs_nonneg (4 * C + 4 * Real.log 2 + 2 * Real.log 4 / a))
  unfold tailDefectBudget tailCellLinearRate
  nlinarith only [hlog, hc, hcl]

theorem SelectedSmallTailCell.compensation_upper
    {A B : Set ℕ} {N hi j : ℕ} {a C L X w : ℝ} {D : Finset ℕ}
    (h : SelectedSmallTailCell A B N a C L X hi D (w / 4) j) :
    4 * ((j : ℝ) + 1) ≤ w + 256 * tailDefectBudget a C X + 8 := by
  have hh := h.2.1
  linarith

theorem selected_centers_lower {A B : Set ℕ} {N hi : ℕ}
    {a C L X : ℝ} {D : Finset ℕ} {centers : List ℕ} {targets : List ℝ}
    (h : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) centers targets) :
    List.Forall₂ (fun c w => w ≤ 4 * c) (centers.map (fun (j : ℕ) => (j : ℝ))) targets := by
  induction h with
  | nil => exact .nil
  | cons h hrest ih =>
    apply List.Forall₂.cons _ ih
    have hh := h.1
    dsimp only
    linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedInitialTotal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original initial log total for the selected actual cells -/
namespace Ostmann
open scoped BigOperators

theorem selected_compensation_centers_sum_bounds
    {A B : Set ℕ} {N hi : ℕ} {a C L Y : ℝ} {D : Finset ℕ}
    {centers : List ℕ} {targets : List ℝ}
    (h : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) centers targets) :
    targets.sum ≤ 4 * (centers.map (fun j : ℕ => (j : ℝ))).sum ∧
      4 * (centers.map (fun j : ℕ => (j : ℝ))).sum ≤
        targets.sum + 4 * centers.length * (64 * tailDefectBudget a C Y + 1) := by
  induction h with
  | nil => simp
  | @cons j w js ws hj hrest ih =>
    have hlo := hj.1
    have hhi := hj.2.1
    simp only [List.sum_cons, List.map_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith only [hlo, hhi, ih.1, ih.2]

theorem selected_initial_total_error
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y G cb cd Δ₀ BD Bz : ℝ}
    {D : Finset ℕ} {centers : List ℕ} (k : ℕ)
    (htop : SelectedSmallTailCell A B N a C L Y hi D
      ((movingProtectedTarget k Y G cd
        (Δ₀ + ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4)
          ((2 : ℝ) ^ (i : ℕ)) (spectatorBulkCount k L)) - 2 * cb) / 6) top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) centers
      (movingCompensationTargets
        (movingProtectedTarget k Y G cd
          (Δ₀ + ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4)
            ((2 : ℝ) ^ (i : ℕ)) (spectatorBulkCount k L)))
        (movingCompensationGaps k BD Bz L))) :
    |2 * (G + cb + cd + 3 * top +
        2 * (centers.map (fun j : ℕ => (j : ℝ))).sum) - (Y + Δ₀)| ≤
      (6 + 4 * k) * (64 * tailDefectBudget a C Y + 1) := by
  let J := movingProtectedTarget k Y G cd
    (Δ₀ + ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4)
      ((2 : ℝ) ^ (i : ℕ)) (spectatorBulkCount k L))
  have htotal := moving_protected_and_compensation_total k BD Bz L Y G cd Δ₀
  change 2 * G + 2 * cd + J +
    (movingCompensationTargets J (movingCompensationGaps k BD Bz L)).sum = Y + Δ₀ at htotal
  have hlen : centers.length = k := by
    have hh := hcenters.length_eq
    simpa only [movingCompensationTargets_length, movingCompensationGaps_length] using hh
  have hsum := selected_compensation_centers_sum_bounds hcenters
  rw [hlen] at hsum
  have hlo := htop.1
  have hhi := htop.2.1
  change (J - 2 * cb) / 6 ≤ (top : ℝ) at hlo
  change (top : ℝ) ≤ (J - 2 * cb) / 6 + 64 * tailDefectBudget a C Y + 1 at hhi
  change (movingCompensationTargets J (movingCompensationGaps k BD Bz L)).sum ≤ _ ∧ _ at hsum
  have hnonneg : 0 ≤ 2 * (G + cb + cd + 3 * top +
      2 * (centers.map (fun j : ℕ => (j : ℝ))).sum) - (Y + Δ₀) := by
    linarith only [hlo, hsum.1, htotal]
  rw [abs_of_nonneg hnonneg]
  nlinarith only [hhi, hsum.2, htotal]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialSmallCellList
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three top labels and two labels of each compensation type -/
namespace Ostmann

theorem initialSmallCellList_length (top : ℕ) (centers : List ℕ) :
    (initialSmallCellList top centers).length = 3 + 2 * centers.length := by
  unfold initialSmallCellList
  induction centers with
  | nil => simp
  | cons j js ih => simp_all; omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialCellPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected initial small cells on a common prime space -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialRegularPrimeRange_prime (L : ℝ) (p : ℕ)
    (hp : p ∈ initialRegularPrimeRange L) : p.Prime := Nat.prime_of_mem_primesLE hp

theorem mem_initialRegularPrimeRange (L : ℝ) (p : ℕ) (hp : p.Prime)
    (hbound : (p : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) :
    p ∈ initialRegularPrimeRange L := Nat.mem_primesLE.mpr ⟨Nat.le_floor hbound, hp⟩

theorem initial_broad_cell_subset (L α β : ℝ) (hL : 0 ≤ L) (hβ : β ≤ 11 / 1000)
    (D : Finset ℕ) :
    primeLogCellSet 1 0 (Real.exp (α * L)) (Real.exp (β * L)) \ D ⊆
      initialRegularPrimeRange L := by
  intro p hp
  obtain ⟨hprime, _, _, hlog⟩ := mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp hp).1
  apply mem_initialRegularPrimeRange L p hprime
  apply ((Real.log_le_iff_le_exp (by exact_mod_cast hprime.pos)).mp hlog).trans
  exact Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hβ hL))

theorem SelectedSmallTailCell.subset_initialRegularPrimeRange
    {A B : Set ℕ} {N hi j : ℕ} {a C L Y target : ℝ} {D : Finset ℕ}
    (h : SelectedSmallTailCell A B N a C L Y hi D target j) :
    selectedTailCellPrimes A B N Y hi D j ⊆ initialRegularPrimeRange L := by
  intro p hp
  obtain ⟨_, _, hindex, _, _, _, hsupport⟩ := h
  have hs := hsupport p hp
  apply mem_initialRegularPrimeRange L p hs.1
  exact hs.2.2.1.trans (Real.exp_le_exp.mpr hindex)

theorem initialSmallCellList_property (top : ℕ) (centers : List ℕ) (P : ℕ → Prop)
    (htop : P top) (hcenters : ∀ j ∈ centers, P j) :
    ∀ j ∈ initialSmallCellList top centers, P j := by
  intro j hj
  simp only [initialSmallCellList, List.mem_append, List.mem_replicate, List.mem_flatMap] at hj
  rcases hj with ⟨_, rfl⟩ | ⟨w, hw, hjw⟩
  · exact htop
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hjw
    rcases hjw with rfl | rfl <;> exact hcenters _ hw

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialAmbientPrimeRange
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual collision cutoff contains the complete initial prime space -/
namespace Ostmann
open Filter

theorem eventual_initial_regular_prime_range :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ Y → Y ≤ Real.exp L →
      initialRegularPrimeRange L ⊆ Nat.primesLE (tailCollisionCutoff Y) := by
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (eventual_tailCollisionCutoff 0)
  have ht : Tendsto (fun L : ℝ => Real.exp ((4 / 100 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [eventual_tail_cell_window 1 0 0,
    ht.eventually (eventually_ge_atTop Y₀), eventually_ge_atTop (0 : ℝ)]
    with L hwindow hlarge hL
  intro Y hYlo hYhi p hp
  have hcut := hY₀ Y (hlarge.trans hYlo)
  have hQ := tailCollisionCutoff_bounds Y hcut.1 hcut.2.1
  have hD : 0 ≤ tailDefectBudget 1 0 Y := by
    dsimp [tailDefectBudget]
    positivity [Real.log_nonneg hcut.1, Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num),
      Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]
  have hw := (hwindow Y (Real.exp ((11 / 1000 : ℝ) * L)) hYlo hYhi
    (Real.exp_le_exp.mpr (by linarith)) le_rfl).2.1
  have hlog : Real.exp ((11 / 1000 : ℝ) * L) ≤
      Real.log (tailCollisionCutoff Y : ℝ) := by linarith
  have hQ0 : (0 : ℝ) < tailCollisionCutoff Y := by exact_mod_cast hQ.1
  have hbound : Real.exp (Real.exp ((11 / 1000 : ℝ) * L)) ≤
      (tailCollisionCutoff Y : ℝ) := by
    simpa only [Real.exp_log hQ0] using Real.exp_le_exp.mpr hlog
  obtain ⟨hpbound, hpprime⟩ := Nat.mem_primesLE.mp hp
  apply Nat.mem_primesLE.mpr
  refine ⟨?_, hpprime⟩
  exact_mod_cast (show (p : ℝ) ≤ (tailCollisionCutoff Y : ℝ) from
    (Nat.cast_le.mpr hpbound).trans ((Nat.floor_le (Real.exp_nonneg _)).trans hbound))

theorem eventual_initial_giant_prime_range (k : ℕ) (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop, ∀ lo Y G : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ Y → Y ≤ Real.exp L →
      2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) ≤ Y →
      G ≤ lo - 2 + 12 * Real.exp ((1 / 100 : ℝ) * L) →
      smoothGiantPrimeRange G ⊆ Nat.primesLE (tailCollisionCutoff Y) := by
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (eventual_tailCollisionCutoff 0)
  have ht : Tendsto (fun L : ℝ => Real.exp ((4 / 100 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [eventual_polynomial_log_budget (8 + |Real.log 2|) 1 (1 / 100) 1 1
      (by positivity) (by norm_num) (by norm_num) (by norm_num),
    ht.eventually (eventually_ge_atTop Y₀), eventually_ge_atTop (1 : ℝ)]
    with L hmargin hlarge hL
  intro lo Y G hYlo hYhi hYlower hG p hp
  have hcut := hY₀ Y (hlarge.trans hYlo)
  have hQ := tailCollisionCutoff_bounds Y hcut.1 hcut.2.1
  have hlogY : Real.log Y ≤ L := (Real.log_le_iff_le_exp (by linarith [hcut.1])).mpr hYhi
  have hm := hmargin L (by linarith) (by simp)
  simp only [pow_one, one_mul] at hm
  have hmargin' : 5 * L + Real.log 2 ≤ Real.exp ((1 / 100 : ℝ) * L) := by
    have hab := le_abs_self (Real.log 2)
    have ha0 := abs_nonneg (Real.log 2)
    nlinarith
  have hpow : (2 : ℝ) ≤ 2 ^ k := by
    calc
      2 = (2 : ℝ) ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [pow_succ] at hYlower
  have hpw := mul_le_mul_of_nonneg_right hpow
    (Real.exp_nonneg ((1 / 100 : ℝ) * L))
  have hlogcut : G + 1 ≤ Real.log (tailCollisionCutoff Y : ℝ) := by
    nlinarith only [hQ.2.2, hlogY, hmargin', hYlower, hG, hpw,
      Real.exp_nonneg ((1 / 100 : ℝ) * L)]
  have hQ0 : (0 : ℝ) < tailCollisionCutoff Y := by exact_mod_cast hQ.1
  have hceil : ⌈Real.exp (G + 1)⌉₊ ≤ tailCollisionCutoff Y := by
    apply Nat.ceil_le.mpr
    simpa only [Real.exp_log hQ0] using Real.exp_le_exp.mpr hlogcut
  have hp' := Finset.mem_filter.mp hp
  exact Nat.mem_primesLE.mpr ⟨(Finset.mem_Icc.mp hp'.1).2.trans hceil, hp'.2⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialCellRoundingBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initial cell rounding fits in the fixed gap reserve -/
namespace Ostmann

theorem initial_cell_rounding_budget (k : ℕ) (R D L : ℝ)
    (hk : 2 ≤ k) (hR : 0 ≤ R) (hL : 1 ≤ L) (hD : D ≤ R * L)
    (hlarge : 14 * (64 * R + 3) ≤ (k : ℝ) ^ 3)
    (hscale : 4 ≤ (k : ℝ) ^ 4 * L) :
    (6 + 4 * k) * (64 * D + 1) + 2 * ((3 + 2 * k : ℕ) + 3) ≤
      (spectatorBulkCount k L : ℝ) := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hL0 : 0 ≤ L := by linarith
  have hcoef : (6 + 4 * (k : ℝ)) * (64 * R + 3) ≤ (k : ℝ) ^ 4 / 2 := by
    have hh := mul_le_mul_of_nonneg_left hlarge hk0
    nlinarith only [hh, hk2, hR]
  have herr : (6 + 4 * k) * (64 * D + 1) + 2 * ((3 + 2 * k : ℕ) + 3) ≤
      (6 + 4 * (k : ℝ)) * (64 * R + 3) * L := by
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_left hD (show 0 ≤ 64 * (6 + 4 * (k : ℝ)) by positivity),
      mul_le_mul_of_nonneg_left hL (show 0 ≤ 18 + 12 * (k : ℝ) by positivity), hk0]
  apply herr.trans
  calc
    _ ≤ (k : ℝ) ^ 4 / 2 * L := mul_le_mul_of_nonneg_right hcoef hL0
    _ = (k : ℝ) ^ 4 * L / 2 := by ring
    _ ≤ _ := spectatorBulkCount_half k L hscale

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedInitialProductWindow
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact product center of the original selected mixed prior -/
namespace Ostmann
open scoped Classical BigOperators

theorem selected_initial_center_bounds
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y G cb cd Bs BD Bz : ℝ}
    {D : Finset ℕ} {centers : List ℕ} (k : ℕ)
    (htop : SelectedSmallTailCell A B N a C L Y hi D
      ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top)
    (hcenters : List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j)
      centers (movingCompensationTargets
        (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
        (movingCompensationGaps k BD Bz L))) :
    let Δ := spectatorBaseGap Bs ((k : ℝ) ^ 4) (spectatorBulkCount k L)
    Δ ≤ selectedInitialLogCenter G Y cb cd top centers ∧
      selectedInitialLogCenter G Y cb cd top centers ≤
        Δ + (6 + 4 * k) * (64 * tailDefectBudget a C Y + 1) := by
  intro Δ
  have herror := selected_initial_total_error k htop hcenters
  have hsum := selected_compensation_centers_sum_bounds hcenters
  have htotal := moving_protected_and_compensation_total k BD Bz L Y G cd Δ
  have ht := htop.1
  change (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6 ≤
    (top : ℝ) at ht
  change 2 * G + 2 * cd + movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) +
    (movingCompensationTargets (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
      (movingCompensationGaps k BD Bz L)).sum = Y + Δ at htotal
  constructor
  · dsimp only [selectedInitialLogCenter]
    linarith only [ht, hsum.1, htotal]
  · have hh := (abs_le.mp herror).2
    dsimp only [selectedInitialLogCenter]
    linarith only [hh]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedInitialWindowRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected product center fits the original one-unit gap reserve -/
namespace Ostmann

theorem selected_initial_window_rate
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y G cb cd Bs BD Bz R : ℝ}
    {D : Finset ℕ} {centers : List ℕ} (k : ℕ) (hk : 2 ≤ k)
    (hL : 1 ≤ L) (hR : 0 ≤ R) (hD : tailDefectBudget a C Y ≤ R * L)
    (hlarge : 14 * (64 * R + 3) ≤ (k : ℝ) ^ 3)
    (hscale : 4 ≤ (k : ℝ) ^ 4 * L)
    (htop : SelectedSmallTailCell A B N a C L Y hi D
      ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top)
    (hcenters : List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j)
      centers (movingCompensationTargets
        (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
        (movingCompensationGaps k BD Bz L))) (hlen : centers.length = k) :
    let m := spectatorBulkCount k L
    let Δ := selectedInitialLogCenter G Y cb cd top centers
    let W : ℝ := 2 * ((initialSmallCellList top centers).length + 3)
    (Bs - 1 + 8 * Real.log ((k : ℝ) ^ 4)) * m ≤ Δ - W ∧
      Δ + W ≤ (Bs + 1 + 8 * Real.log ((k : ℝ) ^ 4)) * m := by
  intro m Δ W
  have hbound := selected_initial_center_bounds k htop hcenters
  have hround := initial_cell_rounding_budget k R (tailDefectBudget a C Y) L
    hk hR hL hD hlarge hscale
  have hW : W = 2 * (((3 + 2 * k : ℕ) : ℝ) + 3) := by
    dsimp only [W]
    rw [initialSmallCellList_length, hlen]
  rw [← hW] at hround
  dsimp only [spectatorBaseGap] at hbound
  constructor <;> dsimp only [Δ, m] at * <;> linarith only [hbound.1, hbound.2, hround]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedInitialPrimeLower
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lower endpoints for every live prime in the original initial prior -/
namespace Ostmann
open Filter
open scoped Classical

theorem initial_selected_centers_lower
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y target H : ℝ}
    {D : Finset ℕ} {centers : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y hi D target top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) centers targets)
    (hHtop : H ≤ target) (hHcenters : ∀ w ∈ targets, H ≤ w / 4) :
    ∀ j ∈ initialSmallCellList top centers, H ≤ (j : ℝ) := by
  apply initialSmallCellList_property top centers (fun j => H ≤ (j : ℝ))
    (hHtop.trans htop.1)
  induction hcenters with
  | nil => simp
  | @cons j w js ws hj hrest ih =>
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact (hHcenters w (by simp)).trans hj.1
    · exact ih (fun v hv => hHcenters v (by simp [hv])) i hi

theorem eventual_initial_selected_centers_lower (k : ℕ) (hk : 2 ≤ k)
    (Bs BD Bz : ℝ) (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) :
    ∀ᶠ L : ℝ in atTop, ∀ {A B : Set ℕ} {N hi top : ℕ} {a C Y G lo : ℝ}
      {D : Finset ℕ} {centers : List ℕ} (cb cd : ℤ),
      cb ∈ Finset.Icc (0 : ℤ)
        ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 1000 : ℝ) * L)⌉₊ →
      cd ∈ Finset.Icc (0 : ℤ)
        ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 10000 : ℝ) * L)⌉₊ →
      2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) ≤ Y →
      Y ≤ 2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) + 1 →
      lo - 2 ≤ G → G ≤ lo - 2 + 12 * Real.exp ((1 / 100 : ℝ) * L) →
      SelectedSmallTailCell A B N a C L Y hi D
        ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top →
      List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j)
        centers (movingCompensationTargets
          (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
          (movingCompensationGaps k BD Bz L)) →
      ∀ j ∈ initialSmallCellList top centers, Real.exp ((1 / 100 : ℝ) * L) ≤ (j : ℝ) := by
  filter_upwards [eventual_initial_protected_target k hk Bs BD Bz hBs hBD hBz,
    eventual_protected_cell_target_range,
    eventual_prescribed_compensation_range k (by omega) BD Bz hBD hBz]
    with L hprotected htopRange hcompRange
  intro A B N hi top a C Y G lo D centers cb cd hcb hcd hYlo hYhi hGlo hGhi htop hcenters
  obtain ⟨hJlo, hJhi, hcb0, hcbJ⟩ := hprotected cb cd hcb hcd lo G Y hYlo hYhi hGlo hGhi
  apply initial_selected_centers_lower htop hcenters
    (htopRange _ _ hJlo hJhi hcb0 hcbJ).1
  intro w hw
  exact (hcompRange _ hJlo hJhi w hw).1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds retained by the two original half-list cutoffs -/
namespace Ostmann
open scoped Classical BigOperators

private theorem initialLogSumWeight_live {P : Type*} {n : ℕ} (value : P → ℕ)
    (c : ℝ) (x : Fin n → P) (hx : initialLogSumWeight value c x ≠ 0) :
    |(∑ i, Real.log (value (x i) : ℝ)) - c| < 1 := by
  by_contra hn
  exact hx (logCellProfile_zero_outside _ (le_of_not_gt hn))

theorem initialMovingCutoffWeight_live_sums {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P)
    (hy : initialMovingCutoffWeight value b d r cb cd sl sr y ≠ 0) :
    |(∑ i : Fin (b + b), Real.log (value (y ((), .inr i)) : ℝ)) - 2 * cb| < 2 ∧
      |(∑ i : Fin (d + d), Real.log (value (Fin.append sl sr i) : ℝ)) - 2 * cd| < 2 := by
  have hl := left_ne_zero_of_mul hy
  have hr := right_ne_zero_of_mul hy
  have hl' : initialLogSumWeight value cb (fun i : Fin b => y ((), .inr (i.castAdd b))) *
      initialLogSumWeight value cd sl ≠ 0 := by exact_mod_cast hl
  have hr' : initialLogSumWeight value cb (fun i : Fin b => y ((), .inr (Fin.natAdd b i))) *
      initialLogSumWeight value cd sr ≠ 0 := by exact_mod_cast hr
  have hbl := initialLogSumWeight_live value cb _ (left_ne_zero_of_mul hl')
  have hbr := initialLogSumWeight_live value cb _ (left_ne_zero_of_mul hr')
  have hdl := initialLogSumWeight_live value cd sl (right_ne_zero_of_mul hl')
  have hdr := initialLogSumWeight_live value cd sr (right_ne_zero_of_mul hr')
  constructor
  · rw [Fin.sum_univ_add]
    obtain ⟨hbl, hbl'⟩ := abs_lt.mp hbl
    obtain ⟨hbr, hbr'⟩ := abs_lt.mp hbr
    apply abs_lt.mpr
    constructor <;> linarith only [hbl, hbl', hbr, hbr']
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    obtain ⟨hdl, hdl'⟩ := abs_lt.mp hdl
    obtain ⟨hdr, hdr'⟩ := abs_lt.mp hdr
    apply abs_lt.mpr
    constructor <;> linarith only [hdl, hdl', hdr, hdr']

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledCellGap
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The geometric gap on the actual compensation schedule -/
namespace Ostmann
open scoped Classical BigOperators

theorem scheduledSmallCell_lower_sum (top : ℕ) (cs : List ℕ) :
    (∑ i : Fin (scheduledSmallLength cs), ((scheduledSmallCell top cs i : ℝ) - 1)) =
      6 * ((top : ℝ) - 1) + 4 * (cs.map (fun c : ℕ => (c : ℝ) - 1)).sum := by
  induction cs with
  | nil =>
    change (∑ _ : Fin 6, ((top : ℝ) - 1)) = _
    norm_num [Fin.sum_univ_succ]
    ring
  | cons c cs ih =>
    change (∑ i : Fin (4 + scheduledSmallLength cs),
      (((Fin.append (fun _ : Fin 4 => c) (scheduledSmallCell top cs) i : ℕ) : ℝ) - 1)) = _
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ih, List.map_cons, List.sum_cons]
    push_cast
    ring

theorem scheduledSmallLower_sum (top : ℕ) (cs : List ℕ) (n : ℕ) :
    (∑ i, scheduledSmallLower top cs n i) =
      (2 ^ n : ℕ) * (6 * ((top : ℝ) - 1) +
        4 * (cs.map (fun c : ℕ => (c : ℝ) - 1)).sum) := by
  simp only [scheduledSmallLower, Fintype.sum_prod_type]
  rw [scheduledSmallCell_lower_sum]
  simp only [Finset.sum_const, Finset.card_univ, card_treeLeafIndex, nsmul_eq_mul]

theorem list_sum_sub_one (cs : List ℝ) :
    (cs.map (fun c => c - 1)).sum = cs.sum - cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp only [List.map_cons, List.sum_cons, List.length_cons,
      Nat.cast_add, Nat.cast_one, ih]; ring

theorem sum_le_four_of_forall₂ {cs ts : List ℝ}
    (h : List.Forall₂ (fun c t => t ≤ 4 * c) cs ts) : ts.sum ≤ 4 * cs.sum := by
  induction h with
  | nil => simp
  | cons h hrest ih => simp only [List.sum_cons]; linarith

theorem selected_scheduled_initial_diagonal_gap
    {A B : Set ℕ} {N hi top pivot : ℕ} {a C L X J cb w cg BD Bz : ℝ}
    {D : Finset ℕ} {centers : List ℕ} {targets : List ℝ} (k n : ℕ)
    (hL : 1 ≤ L) (hX : 0 < X) (hXupper : X ≤ Real.exp L)
    (hk : 1024 * tailCellLinearRate a C + 52 ≤ (k : ℝ) ^ 4)
    (hcount : (8 + 4 * centers.length : ℕ) ≤ L)
    (hcg : cg ≤ (91 / 100 : ℝ) * L)
    (htop : SelectedSmallTailCell A B N a C L X hi D ((J - 2 * cb) / 6) top)
    (hpivot : SelectedSmallTailCell A B N a C L X hi D (w / 4) pivot)
    (hcenters : List.Forall₂
      (fun j t => SelectedSmallTailCell A B N a C L X hi D (t / 4) j) centers targets)
    (hbalance : (2 ^ n : ℕ) * w = (2 ^ n : ℕ) * (J + targets.sum) -
      spectatorStepGap BD Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ) (spectatorBulkCount k L)) :
    2 * cg + 1 + ((2 ^ n : ℕ) * 4) * ((pivot : ℝ) + 1) -
        ((∑ i, scheduledSmallLower top centers n i) + (2 ^ n : ℕ) * (2 * cb - 2)) ≤
      -spectatorStepGap (BD - 1) Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ)
        (spectatorBulkCount k L) := by
  have hr : (0 : ℝ) ≤ (2 ^ n : ℕ) := Nat.cast_nonneg _
  have ht : J ≤ 6 * (top : ℝ) + 2 * cb := by linarith [htop.1]
  have hc : targets.sum ≤ 4 * (centers.map (fun j : ℕ => (j : ℝ))).sum := by
    exact sum_le_four_of_forall₂ (selected_centers_lower hcenters)
  have hlower : (2 ^ n : ℕ) * (J + targets.sum) -
      (8 + 4 * centers.length : ℕ) * (2 ^ n : ℕ) ≤
      (∑ i, scheduledSmallLower top centers n i) + (2 ^ n : ℕ) * (2 * cb - 2) := by
    rw [scheduledSmallLower_sum]
    have hs := list_sum_sub_one (centers.map (fun j : ℕ => (j : ℝ)))
    simp only [List.map_map, Function.comp_def, List.length_map] at hs
    rw [hs]
    have htr := mul_le_mul_of_nonneg_left ht hr
    have hcr := mul_le_mul_of_nonneg_left hc hr
    push_cast at htr hcr ⊢
    nlinarith only [htr, hcr]
  have hcost : 2 * cg + 1 +
      (256 * tailDefectBudget a C X + 8 + (8 + 4 * centers.length : ℕ)) * (2 ^ n : ℕ) ≤
      (2 ^ n : ℕ) * (spectatorBulkCount k L : ℝ) := by
    apply moving_linear_cell_error_budget k n (256 * tailCellLinearRate a C + 9) L cg
      (256 * tailDefectBudget a C X + 8) (8 + 4 * centers.length : ℕ)
      (by linarith [tailCellLinearRate_nonneg a C]) (by linarith) hL hcg
    have he := tailDefectBudget_linear a C L X hL hX hXupper
    nlinarith only [he, hcount, hL]
  have he := moving_cell_diagonal_gap BD Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ)
    (spectatorBulkCount k L) J targets.sum w ((pivot : ℝ) + 1) (2 * cb - 1)
    (∑ i, scheduledSmallLower top centers n i) cg
    (256 * tailDefectBudget a C X + 8) (8 + 4 * centers.length : ℕ)
    hr hbalance (by simpa only [add_assoc] using hpivot.compensation_upper)
    (by convert hlower using 1; ring) hcost
  convert he using 1 <;> first | rfl | ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedInitialAlphabet
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every live selected regular prime belongs to the small alphabet -/
namespace Ostmann
open scoped Classical

theorem list_headD_drop_get {α : Type*} (xs : List α) (fallback : α)
    (j : ℕ) (hj : j < xs.length) :
    (xs.drop j).headD fallback = xs.get ⟨j, hj⟩ := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons c cs ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simpa only [List.drop_succ_cons, List.get_cons_succ] using ih j (by simpa using hj)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledSelectedGaps
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every actual removal has its prescribed diagonal gap -/
namespace Ostmann
open scoped Classical BigOperators

theorem movingCompensationTargets_drop_gap (J : ℝ) (ds : List ℝ) (n : ℕ)
    (hn : n < ds.length) :
    J + ((movingCompensationTargets J ds).drop (n + 1)).sum -
      ((movingCompensationTargets J ds).drop n).headD 0 = (ds.drop n).headD 0 := by
  induction ds generalizing n with
  | nil => simp at hn
  | cons d ds ih =>
    cases n with
    | zero =>
      simp only [movingCompensationTargets, List.drop_zero, List.drop_succ_cons,
        List.headD_cons]
      ring
    | succ n =>
      simpa only [movingCompensationTargets, List.drop_succ_cons] using ih n (by simpa using hn)

theorem movingCompensationGaps_at (k n : ℕ) (BD Bz L : ℝ) (hn : n < k) :
    ((movingCompensationGaps k BD Bz L).drop n).headD 0 =
      spectatorStepGap BD Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ) (spectatorBulkCount k L) /
        (2 ^ n : ℕ) := by
  rw [list_headD_drop_get _ _ _ (by simpa using hn)]
  simp only [movingCompensationGaps, List.get_ofFn, Fin.val_cast, Nat.cast_pow,
    Nat.cast_ofNat]

theorem movingCompensationTargets_drop_balance (J BD Bz L : ℝ) (k n : ℕ)
    (hn : n < k) :
    let ws := movingCompensationTargets J (movingCompensationGaps k BD Bz L)
    (2 ^ n : ℕ) * (ws.drop n).headD 0 =
      (2 ^ n : ℕ) * (J + (ws.drop (n + 1)).sum) -
        spectatorStepGap BD Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ) (spectatorBulkCount k L) := by
  intro ws
  have hh := movingCompensationTargets_drop_gap J (movingCompensationGaps k BD Bz L)
    n (by simpa using hn)
  rw [movingCompensationGaps_at k n BD Bz L hn] at hh
  have hr : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  have he := (eq_div_iff hr.ne').mp hh
  dsimp only [ws]
  nlinarith only [he]

theorem forall₂_headD_drop {R : ℕ → ℝ → Prop} {cs : List ℕ} {ws : List ℝ}
    (h : List.Forall₂ R cs ws) (n : ℕ) (hn : n < cs.length) :
    R ((cs.drop n).headD 0) ((ws.drop n).headD 0) := by
  induction h generalizing n with
  | nil => simp at hn
  | cons h hrest ih =>
    cases n with
    | zero => exact h
    | succ n => simpa only [List.drop_succ_cons] using ih n (by simpa using hn)

theorem selected_scheduled_drop_diagonal_gap
    {A B : Set ℕ} {N hi top : ℕ} {a C L X J cb cg BD Bz : ℝ}
    {D : Finset ℕ} {centers : List ℕ} (k n : ℕ) (hn : n < k)
    (hL : 1 ≤ L) (hX : 0 < X) (hXupper : X ≤ Real.exp L)
    (hk : 1024 * tailCellLinearRate a C + 52 ≤ (k : ℝ) ^ 4)
    (hcount : (8 + 4 * centers.length : ℕ) ≤ L)
    (hcg : cg ≤ (91 / 100 : ℝ) * L)
    (htop : SelectedSmallTailCell A B N a C L X hi D ((J - 2 * cb) / 6) top)
    (hcenters : List.Forall₂
      (fun j t => SelectedSmallTailCell A B N a C L X hi D (t / 4) j)
      centers (movingCompensationTargets J (movingCompensationGaps k BD Bz L))) :
    2 * cg + 1 + ((2 ^ n : ℕ) * 4) * (((centers.drop n).headD 0 : ℝ) + 1) -
        ((∑ i, scheduledSmallLower top (centers.drop (n + 1)) n i) +
          (2 ^ n : ℕ) * (2 * cb - 2)) ≤
      -spectatorStepGap (BD - 1) Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ)
        (spectatorBulkCount k L) := by
  have hlen : centers.length = k := by
    simpa only [movingCompensationTargets_length, movingCompensationGaps_length] using
      hcenters.length_eq
  have hpivot := forall₂_headD_drop hcenters n (by omega)
  have htail := List.forall₂_drop (n + 1) hcenters
  have hcount' : (8 + 4 * (centers.drop (n + 1)).length : ℕ) ≤ L := by
    apply le_trans _ hcount
    exact_mod_cast (show 8 + 4 * (centers.drop (n + 1)).length ≤ 8 + 4 * centers.length by
      simp only [List.length_drop]; omega)
  exact selected_scheduled_initial_diagonal_gap k n hL hX hXupper hk hcount' hcg htop
    hpivot htail (movingCompensationTargets_drop_balance J BD Bz L k n hn)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FrozenInitialSmallAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The constructed positive statistic on the actual regular-prime alphabet -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem restrictPrimeSamples_embedding {P Q : Finset ℕ} {d : ℕ} (hQP : Q ⊆ P)
    (s : Fin d → P) (hs : ∀ i, (s i : ℕ) ∈ Q) :
    primeAlphabetEmbedding hQP ∘ restrictPrimeSamples s hs = s := by
  funext i
  exact Subtype.ext rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialSpectatorProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed spectator product retains both original logarithmic cutoffs -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem initialMovingCutoffWeight_spectator_product {A : Type*}
    (value : A → ℕ) (hvalue : ∀ x, 0 < value x)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → A)
    (y : MovingRegularSlot 0 (r + r) (b + b) → A)
    (hy : initialMovingCutoffWeight value b d r cb cd sl sr y ≠ 0) :
    |Real.log ((∏ i, value (Fin.append sl sr i) : ℕ) : ℝ) - 2 * cd| < 2 := by
  rw [Nat.cast_prod, Real.log_prod (fun i _ => by exact_mod_cast (hvalue (Fin.append sl sr i)).ne')]
  exact (initialMovingCutoffWeight_live_sums value b d r cb cd sl sr y hy).2

theorem initialMovingOriginalLeaf_spectator_product {A I : Type*}
    (value : A → ℕ) (hvalue : ∀ x, 0 < value x)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → A) (fallback : A)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (x : MovingSlotState A) (s : ℤ)
    (hx : movingOriginalLeaf value q
      (initialMovingDataCutoff value b d r cb cd sl sr fallback) g Dq S ψ X lo hi x s ≠ 0) :
    |Real.log ((∏ i, value (Fin.append sl sr i) : ℕ) : ℝ) - 2 * cd| < 2 := by
  have hw := left_ne_zero_of_mul (left_ne_zero_of_mul hx)
  have hd : initialMovingDataCutoff value b d r cb cd sl sr fallback x.data s ≠ 0 := by
    intro hz
    apply hw
    simp only [movingWindowLeaf, movingDataLeaf, hz, ite_self]
  have hc : initialMovingCutoffWeight value b d r cb cd sl sr
      (initialRegularFromList b r fallback x.data.regularSlots) ≠ 0 := by
    intro hz
    apply hd
    simp only [initialMovingDataCutoff, hz, ite_self]
  exact initialMovingCutoffWeight_spectator_product value hvalue b d r cb cd sl sr _ hc

/-- A nonzero initial statistic certifies the fixed spectator product, with no
assumption on an individual sampled summand. -/
theorem initialTemplateAmplitude_spectator_product {A I : Type} [Fintype A]
    (value : A → ℕ) (hvalue : ∀ x, 0 < value x)
    (b d r a : ℕ) (cb cd : ℝ) (sl sr : Fin d → A) (fallback : A)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → A → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Pg : Finset ℕ) (ρ : Pg → ℝ)
    (ν : MovingRegularSlot 0 a (b + b) → A → ℝ)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (fav : ℕ → Bool)
    (h : movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
      (movingOriginalLeaf value q
        (initialMovingDataCutoff value b d r cb cd sl sr fallback) g Dq S ψ X lo hi)
      φ G 0 a (b + b) Pg ρ ν greg ggiant fav ≠ 0) :
    |Real.log ((∏ i, value (Fin.append sl sr i) : ℕ) : ℝ) - 2 * cd| < 2 := by
  obtain ⟨XL, _, hXL⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨XR, _, hXR⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hXL)
  obtain ⟨s, _, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hXR)
  obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  have hc := left_ne_zero_of_mul (right_ne_zero_of_mul hy)
  unfold movingTemplateCoefficient at hc
  have hf := movingFrequencyCoefficient_levelZero_support A value outside μ childBound
    pivotBound V _ φ G s.val _ _ XL XR hc
  exact initialMovingOriginalLeaf_spectator_product value hvalue b d r cb cd sl sr
    fallback q g Dq S ψ X lo hi _ _ hf

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedScheduledProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The recursive product budget of the actual selected cells -/
namespace Ostmann
open scoped Classical BigOperators

theorem nat_cell_drop_sum (cs : List ℕ) (n : ℕ) :
    ((cs.drop n).map (fun j : ℕ => (j : ℝ))).sum =
      ((cs.drop n).headD 0 : ℝ) + ((cs.drop (n + 1)).map (fun j : ℕ => (j : ℝ))).sum := by
  induction cs generalizing n with
  | nil => simp
  | cons c cs ih =>
    cases n with
    | zero => simp
    | succ n => simpa only [List.drop_succ_cons] using ih n

theorem selected_cell_pivot_exponent (G : ℝ) (cs : List ℕ) (n : ℕ) :
    movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n =
      G - 1 + (2 : ℝ) ^ n * 4 * ((cs.drop n).headD 0 : ℝ) := by
  simp only [movingCellPivotExponent, selectedCompensationCenter, add_sub_cancel_right,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem selectedProductExponent_eq (G Y cb cd width Dlog : ℝ) (top : ℕ) (cs : List ℕ) (n : ℕ) :
    movingProductExponent (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
      (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) n =
    2 * (G - 1) + (2 : ℝ) ^ n *
      (2 * cb + 2 * cd - Dlog + 6 * top +
        4 * ((cs.drop n).map (fun j : ℕ => (j : ℝ))).sum + width + 2) := by
  induction n with
  | zero =>
    simp only [movingProductExponent, pow_zero, one_mul, List.drop_zero,
      selectedInitialLogCenter]
    ring
  | succ n ih =>
    rw [movingProductExponent, ih, selected_cell_pivot_exponent, nat_cell_drop_sum cs n,
      pow_succ]
    ring

theorem selectedProductExponent_gap (G Y cb cd width Dlog : ℝ) (top : ℕ) (cs : List ℕ) (n : ℕ) :
    movingProductExponent (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
        (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) n -
      2 * movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n =
    (2 : ℝ) ^ n * (2 * cb + 2 * cd - Dlog + 6 * top + width + 2 +
      4 * ((cs.drop (n + 1)).map (fun j : ℕ => (j : ℝ))).sum -
      4 * ((cs.drop n).headD 0 : ℝ)) := by
  rw [selectedProductExponent_eq, selected_cell_pivot_exponent, nat_cell_drop_sum cs n]
  ring

theorem selectedProductExponent_gap_from_diagonal
    (G Y cb cd width Dlog : ℝ) (top : ℕ) (cs : List ℕ) (n : ℕ)
    (hD : Dlog ≤ 2 * cd + 2) (hwidth : 0 ≤ width)
    (hgap : 1 + ((2 ^ n : ℕ) * 4) * (((cs.drop n).headD 0 : ℝ) + 1) -
      ((∑ i, scheduledSmallLower top (cs.drop (n + 1)) n i) +
        (2 ^ n : ℕ) * (2 * cb - 2)) ≤ 0) :
    2 * movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n ≤
      movingProductExponent (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
        (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) n := by
  have he := selectedProductExponent_gap G Y cb cd width Dlog top cs n
  rw [scheduledSmallLower_sum] at hgap
  have hs := list_sum_sub_one ((cs.drop (n + 1)).map (fun j : ℕ => (j : ℝ)))
  simp only [List.map_map, Function.comp_def, List.length_map] at hs
  rw [hs] at hgap
  push_cast at hgap
  have hr : 0 ≤ (2 : ℝ) ^ n := by positivity
  have hd := mul_nonneg hr (show 0 ≤ 2 * cd - Dlog + 2 by linarith only [hD])
  have hw := mul_nonneg hr hwidth
  have hl := mul_nonneg hr (Nat.cast_nonneg (cs.drop (n + 1)).length (α := ℝ))
  nlinarith only [he, hgap, hd, hw, hl, hr]

theorem selectedProductExponent_budget
    (G Y cb cd width Dlog : ℝ) (top : ℕ) (cs : List ℕ)
    (hcb : 0 ≤ cb) (hD : Dlog ≤ 2 * cd + 2) (hwidth : 0 ≤ width)
    (hgap : ∀ n < cs.length,
      1 + ((2 ^ n : ℕ) * 4) * (((cs.drop n).headD 0 : ℝ) + 1) -
        ((∑ i, scheduledSmallLower top (cs.drop (n + 1)) n i) +
          (2 ^ n : ℕ) * (2 * cb - 2)) ≤ 0) :
    ∀ n, 2 * movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n ≤
      movingProductExponent (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
        (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) n := by
  intro n
  by_cases hn : n < cs.length
  · exact selectedProductExponent_gap_from_diagonal G Y cb cd width Dlog top cs n hD hwidth (hgap n hn)
  · have he := selectedProductExponent_gap G Y cb cd width Dlog top cs n
    have hdrop : cs.drop n = [] := List.drop_eq_nil_of_le (by omega)
    have hdrop' : cs.drop (n + 1) = [] := List.drop_eq_nil_of_le (by omega)
    simp only [hdrop, hdrop', List.map_nil, List.sum_nil, List.headD_nil, Nat.cast_zero,
      mul_zero, add_zero, sub_zero] at he
    have hterm : 0 ≤ 2 * cb + 2 * cd - Dlog + 6 * top + width + 2 := by
      nlinarith only [hD, hcb, hwidth, Nat.cast_nonneg top (α := ℝ)]
    have hnonneg := mul_nonneg (show 0 ≤ (2 : ℝ) ^ n by positivity) hterm
    linarith only [he, hnonneg]

/-- The chosen compensation cells give the actual recursive product budget. -/
theorem selectedProductExponent_budget_of_cells
    {A B : Set ℕ} {N hi top : ℕ} {a C L X J G Y cb cd width Dlog BD Bz : ℝ}
    {D : Finset ℕ} {cs : List ℕ} (k : ℕ)
    (hk0 : 1 ≤ k) (hL : 1 ≤ L) (hX : 0 < X) (hXupper : X ≤ Real.exp L)
    (hk : 1024 * tailCellLinearRate a C + 52 ≤ (k : ℝ) ^ 4)
    (hcount : (8 + 4 * cs.length : ℕ) ≤ L)
    (hcb : 0 ≤ cb) (hD : Dlog ≤ 2 * cd + 2) (hwidth : 0 ≤ width)
    (hBD : 1 ≤ BD) (hBz : 0 ≤ Bz)
    (htop : SelectedSmallTailCell A B N a C L X hi D ((J - 2 * cb) / 6) top)
    (hcs : List.Forall₂
      (fun j t => SelectedSmallTailCell A B N a C L X hi D (t / 4) j)
      cs (movingCompensationTargets J (movingCompensationGaps k BD Bz L))) :
    ∀ n, 2 * movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n ≤
      movingProductExponent (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
        (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) n := by
  apply selectedProductExponent_budget G Y cb cd width Dlog top cs hcb hD hwidth
  intro n hn
  have hlen : cs.length = k := by
    simpa only [movingCompensationTargets_length, movingCompensationGaps_length] using
      hcs.length_eq
  have h := selected_scheduled_drop_diagonal_gap k n (by omega) hL hX hXupper hk
    hcount (cg := 0) (by linarith) htop hcs
  have hz : 0 ≤ Real.log ((k : ℝ) ^ 4) :=
    Real.log_nonneg (one_le_pow₀ (by exact_mod_cast hk0))
  have hr : 0 ≤ Real.log (2 ^ n : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))))
  have hm : 0 ≤ (spectatorBulkCount k L : ℝ) := Nat.cast_nonneg _
  have hstep : 0 ≤ spectatorStepGap (BD - 1) Bz ((k : ℝ) ^ 4)
      (2 ^ n : ℕ) (spectatorBulkCount k L) := by
    unfold spectatorStepGap
    have hBD' : 0 ≤ BD - 1 := by linarith
    positivity
  simpa only [mul_zero, zero_add] using h.trans (neg_nonpos.mpr hstep)

theorem selected_cell_pivot_nonneg (G : ℝ) (hG : 1 ≤ G) (cs : List ℕ) (n : ℕ) :
    0 ≤ movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n := by
  rw [selected_cell_pivot_exponent]
  have hg : 0 ≤ G - 1 := by linarith
  positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedProductFrequency
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual product schedule satisfies the finite frequency budget -/
namespace Ostmann
open scoped Classical BigOperators

theorem selectedProductExponent_gap_upper
    {A B : Set ℕ} {N hi top : ℕ} {a C L X J G Y cb cd width Dlog BD Bz : ℝ}
    {D : Finset ℕ} {cs : List ℕ} (k n : ℕ) (hn : n < k)
    (hD : 2 * cd - 2 ≤ Dlog)
    (htop : SelectedSmallTailCell A B N a C L X hi D ((J - 2 * cb) / 6) top)
    (hcs : List.Forall₂
      (fun j t => SelectedSmallTailCell A B N a C L X hi D (t / 4) j)
      cs (movingCompensationTargets J (movingCompensationGaps k BD Bz L))) :
    movingProductExponent (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
        (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) n -
      2 * movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n ≤
    spectatorStepGap BD Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ) (spectatorBulkCount k L) +
      (2 : ℝ) ^ n * ((6 + 4 * (cs.drop (n + 1)).length) *
        (64 * tailDefectBudget a C X + 1) + width + 4) := by
  have hlen : cs.length = k := by
    simpa only [movingCompensationTargets_length, movingCompensationGaps_length] using
      hcs.length_eq
  have hpivot := (forall₂_headD_drop hcs n (by omega)).1
  have htail := (selected_compensation_centers_sum_bounds
    (List.forall₂_drop (n + 1) hcs)).2
  have htop' := htop.2.1
  have hbalance := movingCompensationTargets_drop_balance J BD Bz L k n hn
  dsimp only at hbalance
  have he := selectedProductExponent_gap G Y cb cd width Dlog top cs n
  have hr : 0 ≤ (2 : ℝ) ^ n := by positivity
  have hp := mul_le_mul_of_nonneg_left hpivot (show 0 ≤ (2 : ℝ) ^ n * 4 by positivity)
  have ht := mul_le_mul_of_nonneg_left htail hr
  have hu := mul_le_mul_of_nonneg_left htop' (show 0 ≤ (2 : ℝ) ^ n * 6 by positivity)
  have hd := mul_le_mul_of_nonneg_left hD hr
  push_cast at hp ht hu hd hbalance ⊢
  nlinarith only [he, hp, ht, hu, hd, hbalance]

/-- Each rounding loss is paid once, in the fixed per-step reserve. -/
theorem selectedProductExponent_gap_budget
    {A B : Set ℕ} {N hi top : ℕ} {a C L X J G Y cb cd width Dlog BD Bz R : ℝ}
    {D : Finset ℕ} {cs : List ℕ} (k n : ℕ) (hk : 2 ≤ k) (hn : n < k)
    (hL : 1 ≤ L) (hR : 0 ≤ R) (hdef0 : 0 ≤ tailDefectBudget a C X)
    (hdef : tailDefectBudget a C X ≤ R * L)
    (hlarge : 14 * (64 * R + 3) ≤ (k : ℝ) ^ 3)
    (hscale : 4 ≤ (k : ℝ) ^ 4 * L)
    (hm : 4 ≤ (spectatorBulkCount k L : ℝ))
    (hwidth : width = 2 * ((initialSmallCellList top cs).length + 3))
    (hD : 2 * cd - 2 ≤ Dlog)
    (htop : SelectedSmallTailCell A B N a C L X hi D ((J - 2 * cb) / 6) top)
    (hcs : List.Forall₂
      (fun j t => SelectedSmallTailCell A B N a C L X hi D (t / 4) j)
      cs (movingCompensationTargets J (movingCompensationGaps k BD Bz L))) :
    movingProductExponent (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
        (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) n -
      2 * movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n ≤
    spectatorStepGap (BD + 2) Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ) (spectatorBulkCount k L) := by
  have hlen : cs.length = k := by
    simpa only [movingCompensationTargets_length, movingCompensationGaps_length] using
      hcs.length_eq
  have hround := initial_cell_rounding_budget k R (tailDefectBudget a C X) L
    hk hR hL hdef hlarge hscale
  have hdrop : ((cs.drop (n + 1)).length : ℝ) ≤ k := by
    exact_mod_cast (show (cs.drop (n + 1)).length ≤ k by simp only [List.length_drop, hlen]; omega)
  have hwidth' : width = 2 * ((3 + 2 * k : ℕ) + 3) := by
    rw [hwidth, initialSmallCellList_length, hlen]
  have hsmall : (6 + 4 * (cs.drop (n + 1)).length) *
      (64 * tailDefectBudget a C X + 1) + width + 4 ≤ 2 * spectatorBulkCount k L := by
    rw [hwidth']
    nlinarith only [hround, hm, mul_le_mul_of_nonneg_right hdrop
      (show 0 ≤ 4 * (64 * tailDefectBudget a C X + 1) by positivity)]
  have hu := selectedProductExponent_gap_upper (G := G) (Y := Y) (width := width) k n hn hD htop hcs
  have hh := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ (2 : ℝ) ^ n by positivity)
  unfold spectatorStepGap at hu ⊢
  push_cast at hu ⊢
  nlinarith only [hu, hh]

theorem movingProductFrequency_le_movingCutoff (T : ℕ → ℝ) (W Y Bs BD Bz z m : ℝ)
    (k : ℕ) (hzero : W - Y ≤ spectatorBaseGap Bs z m)
    (hsteps : ∀ j < k, movingProductExponent T W j - 2 * T j ≤
      spectatorStepGap BD Bz z ((2 : ℝ) ^ j) m) :
    ∀ n ≤ k, movingProductFrequencyExponent T W Y (m / 4) n ≤
      movingCutoffExponent Bs BD Bz z m n := by
  have hs : Real.sqrt (4 * (m / 4)) ≤ Real.sqrt (4 * m) := by
    rw [show 4 * (m / 4) = m by ring]
    by_cases hm : 0 ≤ m
    · exact Real.sqrt_le_sqrt (by linarith)
    · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hm),
        Real.sqrt_eq_zero_of_nonpos (by linarith)]
  intro n hn
  induction n with
  | zero =>
    rw [movingCutoffExponent_zero]
    simp only [movingProductFrequencyExponent, movingProductExponent, pow_zero, one_mul]
    linarith
  | succ n ih =>
    have hi := ih (by omega)
    have hj := hsteps n (by omega)
    have he := movingProductFrequency_reserve T W Y (m / 4) n
    have hr := mul_le_mul_of_nonneg_left hs (show 0 ≤ (2 : ℝ) ^ n by positivity)
    rw [movingCutoffExponent_succ]
    linarith only [hi, hj, he, hr]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedProductBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual tail-cell errors fit both numerical transfer reserves -/
namespace Ostmann
open Filter

theorem eventual_tailDefectBudget_nonneg (a C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ X : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ X → 0 ≤ tailDefectBudget a C X := by
  let K := 4 * C + 4 * Real.log 2 + 2 * Real.log 4 / a
  filter_upwards [eventually_ge_atTop (-5 * K / 4)] with L hL X hX
  have hx : 0 < X := (Real.exp_pos _).trans_le hX
  have hl := (Real.le_log_iff_exp_le hx).mpr hX
  dsimp only [tailDefectBudget, K] at *
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedScheduledCutoffs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical cutoff data for the literal scheduled cell priors -/
namespace Ostmann
open scoped Classical BigOperators

theorem selected_scheduled_cutoff_data
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y G cb cd width Dlog Bs BD Bz R : ℝ}
    {D : Finset ℕ} {cs : List ℕ} (k : ℕ) (hk : 2 ≤ k)
    (hL : 1 ≤ L) (hY : 0 < Y) (hYupper : Y ≤ Real.exp L)
    (hR : 0 ≤ R) (hdef0 : 0 ≤ tailDefectBudget a C Y)
    (hdef : tailDefectBudget a C Y ≤ R * L)
    (hlarge : 14 * (64 * R + 3) ≤ (k : ℝ) ^ 3)
    (hscale : 4 ≤ (k : ℝ) ^ 4 * L)
    (hcell : 1024 * tailCellLinearRate a C + 52 ≤ (k : ℝ) ^ 4)
    (hcount : (8 + 4 * cs.length : ℕ) ≤ L)
    (hm : 256 ≤ (spectatorBulkCount k L : ℝ))
    (hG : 1 ≤ G) (hcb : 0 ≤ cb) (hD : |Dlog - 2 * cd| ≤ 2)
    (hwidth : width = 2 * ((initialSmallCellList top cs).length + 3))
    (hBs : 0 ≤ Bs) (hBD : 1 ≤ BD) (hBz : 0 ≤ Bz)
    (htop : SelectedSmallTailCell A B N a C L Y hi D
      ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top)
    (hcs : List.Forall₂
      (fun j t => SelectedSmallTailCell A B N a C L Y hi D (t / 4) j)
      cs (movingCompensationTargets
        (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
        (movingCompensationGaps k BD Bz L))) :
    let m : ℝ := spectatorBulkCount k L
    let T := movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs)
    let W := Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog
    let V := movingProductNaturalCutoff T W (Y - Dlog) (m / 4)
    Monotone V ∧ Y - Dlog ≤ W ∧
      (∀ n, 0 ≤ movingProductExponent T W n - T n) ∧
      (∀ n ≤ k,
        (V n : ℝ) ≤ Real.exp (movingFrequencyRate (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4) n * m) ∧
        ((transferFrequencyRange (V n)).card : ℝ) ≤
          Real.exp (movingFrequencyRate (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4) n * m)) := by
  intro m T W V
  have hlen : cs.length = k := by
    simpa only [movingCompensationTargets_length, movingCompensationGaps_length] using hcs.length_eq
  have hDl : 2 * cd - 2 ≤ Dlog := by linarith only [(abs_le.mp hD).1]
  have hDu : Dlog ≤ 2 * cd + 2 := by linarith only [(abs_le.mp hD).2]
  have hwidth0 : 0 ≤ width := by rw [hwidth]; positivity
  have hb := selectedProductExponent_budget_of_cells (G := G) (Y := Y) k (by omega)
    hL hY hYupper hcell hcount hcb hDu hwidth0 hBD hBz htop hcs
  change ∀ n, 2 * T n ≤ movingProductExponent T W n at hb
  have hwin := selected_initial_window_rate k hk hL hR hdef hlarge hscale htop hcs hlen
  have hz : 1 ≤ (k : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ k by omega))
  have hzlog := Real.log_nonneg hz
  have hcenter := (selected_initial_center_bounds k htop hcs).1
  have hcenter0 : 0 ≤ selectedInitialLogCenter G Y cb cd top cs := by
    have hbase0 : 0 ≤ spectatorBaseGap Bs ((k : ℝ) ^ 4) m := by
      unfold spectatorBaseGap
      positivity
    exact hbase0.trans hcenter
  have hzero : W - (Y - Dlog) ≤ spectatorBaseGap (Bs + 1) ((k : ℝ) ^ 4) m := by
    dsimp only [W]
    rw [hwidth]
    dsimp only [spectatorBaseGap, m]
    linarith only [hwin.2]
  refine ⟨movingProductNaturalCutoff_monotone T W (Y - Dlog) (m / 4) hb, ?_, ?_, ?_⟩
  · dsimp only [W]
    linarith
  · intro n
    have ht := selected_cell_pivot_nonneg G hG cs n
    change 0 ≤ T n at ht
    linarith [hb n]
  · intro n hn
    have hsteps : ∀ j < k, movingProductExponent T W j - 2 * T j ≤
        spectatorStepGap (BD + 2) Bz ((k : ℝ) ^ 4) ((2 : ℝ) ^ j) m := by
      intro j hj
      have hh := selectedProductExponent_gap_budget (G := G) (Y := Y) k j hk hj hL hR
        hdef0 hdef hlarge hscale (by linarith) hwidth hDl htop hcs
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hh
    have hfreq := movingProductFrequency_le_movingCutoff T W (Y - Dlog)
      (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4) m k hzero hsteps n hn
    have hVle : V n ≤ movingNaturalCutoff (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4) m n :=
      Nat.floor_mono (Real.exp_le_exp.mpr hfreq)
    have hbound := movingNaturalCutoff_frequency_bound (Bs + 1) (BD + 2) Bz
      ((k : ℝ) ^ 4) m n (by linarith) (by linarith) hBz hz (by linarith)
    have hVreal : (V n : ℝ) ≤
        movingNaturalCutoff (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4) m n := by exact_mod_cast hVle
    refine ⟨hVreal.trans hbound.1, ?_⟩
    apply le_trans _ hbound.2
    rw [card_transferFrequencyRange, card_transferFrequencyRange]
    exact_mod_cast (show 2 * V n + 1 ≤ 2 * movingNaturalCutoff (Bs + 1) (BD + 2) Bz
      ((k : ℝ) ^ 4) m n + 1 by omega)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledIterationThresholds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The remaining scalar reserves for the selected finite iteration -/
namespace Ostmann
open Filter

theorem eventual_scheduled_iteration_thresholds (k : ℕ) (hk : 2 ≤ k) (a C : ℝ)
    (hklarge : 20480 * tailCellLinearRate a C + 720 ≤ (k : ℝ) ^ 4) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ, 0 < Y → Y ≤ Real.exp L →
      ∀ (top : ℕ) (cs : List ℕ), cs.length = k →
      256 ≤ (spectatorBulkCount k L : ℝ) ∧
      (8 + 4 * cs.length : ℕ) ≤ L ∧
      256 * tailDefectBudget a C Y + 9 ≤ (spectatorBulkCount k L : ℝ) / 40 ∧
      40 * (2 * ((initialSmallCellList top cs).length + 3) + 14 + 4 * cs.length) +
        20 * Real.log 2 < (spectatorBulkCount k L : ℝ) := by
  have hkt : 0 < k := by omega
  have hm := spectatorBulkCount_tendsto k hkt
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop ((8 + 4 * k : ℕ) : ℝ),
    hm.eventually (eventually_ge_atTop (256 : ℝ)),
    hm.eventually (eventually_gt_atTop (40 * (2 * ((3 + 2 * k : ℕ) + 3) + 14 + 4 * k) +
      20 * Real.log 2))] with L hL hcount hmass hround
  intro Y hY hYupper top cs hlen
  have hR := tailCellLinearRate_nonneg a C
  have hscale : 4 ≤ (k : ℝ) ^ 4 * L := by
    have hk4 : (16 : ℝ) ≤ (k : ℝ) ^ 4 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
        (show (2 : ℝ) ≤ k by exact_mod_cast hk) 4
      norm_num at hh
      exact hh
    nlinarith only [hk4, hL]
  have hhalf := spectatorBulkCount_half k L hscale
  have hdef := tailDefectBudget_linear a C L Y hL hY hYupper
  have hlinear := mul_le_mul_of_nonneg_right hklarge (show 0 ≤ L by linarith)
  refine ⟨hmass, ?_, ?_, ?_⟩
  · simpa only [hlen] using hcount
  · nlinarith only [hlinear, hhalf, hdef, hL]
  · simpa only [initialSmallCellList_length, hlen] using hround

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledAnalyticParameters
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed gap constants and a common large depth for the constructed schedule -/
namespace Ostmann
open Filter

/-- Both gap constants are chosen before the depth and before any selected cells. -/
theorem scheduled_gap_parameters : ∃ Bs BD : ℝ,
    1 ≤ Bs ∧ Bs + 1 ≤ BD ∧
    2 * ((4 - 2 * Real.log (1 / 320000)) + 2 + 2 * Real.log 4 +
      (4 * (Real.log 2 + 2) + 2 * Real.log 2 + 4) + 3) ≤ Bs - 1 ∧
    (Bs + 1) + 2 * scheduledIterationRate +
      (Real.log 2 - Real.log (1 / 16000 : ℝ) + 5 / 4 + 1 + Real.log 12 + 1 + 1) + 6 ≤
      BD - 1 := by
  let gap := 2 * ((4 - 2 * Real.log (1 / 320000)) + 2 + 2 * Real.log 4 +
    (4 * (Real.log 2 + 2) + 2 * Real.log 2 + 4) + 3)
  let Bs := 1 + max 0 gap
  let E := Real.log 2 - Real.log (1 / 16000 : ℝ) + 5 / 4 + 1 + Real.log 12 + 1 + 1
  let BD := max (Bs + 2) (Bs + 2 * scheduledIterationRate + E + 9)
  have hBs : 1 ≤ Bs := by dsimp only [Bs]; linarith only [le_max_left (0 : ℝ) gap]
  have hBD := le_max_left (Bs + 2) (Bs + 2 * scheduledIterationRate + E + 9)
  have hBDE := le_max_right (Bs + 2) (Bs + 2 * scheduledIterationRate + E + 9)
  refine ⟨Bs, BD, hBs, ?_, ?_, ?_⟩
  · dsimp only [BD]
    linarith only [hBD]
  · dsimp only [Bs]
    change gap ≤ 1 + max 0 gap - 1
    linarith only [le_max_right 0 gap]
  · change Bs + 1 + 2 * scheduledIterationRate + E + 6 ≤ BD - 1
    dsimp only [BD]
    linarith only [hBDE]

theorem eventual_scheduled_depth_reserves (R : ℝ) :
    ∀ᶠ k : ℕ in atTop, 2 ≤ k ∧
      120 ≤ (k : ℝ) ^ 3 ∧
      14 * (64 * R + 3) ≤ (k : ℝ) ^ 3 ∧
      20480 * R + 720 ≤ (k : ℝ) ^ 4 ∧
      1024 * R + 52 ≤ (k : ℝ) ^ 4 := by
  have h₃ : Tendsto (fun k : ℕ => (k : ℝ) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have h₄ : Tendsto (fun k : ℕ => (k : ℝ) ^ 4) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    h₃.eventually (eventually_ge_atTop (120 : ℝ)),
    h₃.eventually (eventually_ge_atTop (14 * (64 * R + 3))),
    h₄.eventually (eventually_ge_atTop (20480 * R + 720)),
    h₄.eventually (eventually_ge_atTop (1024 * R + 52))] with k hk h₁ h₂ h₃ h₄
  exact ⟨hk, h₁, h₂, h₃, h₄⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledInitialWindow
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The measured initial window meets the energy and cutoff budgets -/
namespace Ostmann
open Filter

theorem eventual_selected_initial_energy_window (k : ℕ) (hk : 2 ≤ k)
    (Bs BD Bz R : ℝ) (hBs : 1 ≤ Bs) (hR : 0 ≤ R)
    (hlarge : 14 * (64 * R + 3) ≤ (k : ℝ) ^ 3) :
    ∀ᶠ L : ℝ in atTop, ∀ {A B : Set ℕ} {N hi top : ℕ}
      {a C Y G cb cd : ℝ} {D : Finset ℕ} {cs : List ℕ},
      tailDefectBudget a C Y ≤ R * L →
      SelectedSmallTailCell A B N a C L Y hi D
        ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top →
      List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j)
        cs (movingCompensationTargets
          (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
          (movingCompensationGaps k BD Bz L)) → cs.length = k →
      let m := (spectatorBulkCount k L : ℝ)
      let center := selectedInitialLogCenter G Y cb cd top cs
      let width : ℝ := 2 * ((initialSmallCellList top cs).length + 3)
      let Δ := center - width
      64 ≤ m / 4 ∧ 0 ≤ Δ ∧ Δ ≤ spectatorBaseGap (Bs + 1) ((k : ℝ) ^ 4) m ∧
      Real.exp Δ ≤ Real.exp (center + width) ∧
      Real.exp (center + width) - Real.exp Δ ≤
        Real.exp ((Bs + 1 + 8 * Real.log ((k : ℝ) ^ 4)) * m) ∧
      Y ≤ Y + center + width ∧
      ∀ T : ℕ → ℝ,
        (movingProductNaturalCutoff T (Y + center + width) Y (m / 4) 0 : ℝ) ≤
          Real.exp (Δ + Real.sqrt (4 * m)) := by
  have hk0 : 0 < k := by omega
  have hreserve := (spectatorBulkCount_tendsto k hk0).eventually
    (eventually_initial_product_reserve (4 * (((3 + 2 * k : ℕ) : ℝ) + 3)))
  filter_upwards [hreserve, eventually_ge_atTop (1 : ℝ)] with L hreserve hL
  intro A B N hi top a C Y G cb cd D cs hdef htop hcs hlen m center width Δ
  have hscale : 4 ≤ (k : ℝ) ^ 4 * L := by
    have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hk4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hkr 4
    norm_num at hk4
    nlinarith
  have hwin := selected_initial_window_rate k hk hL hR hdef hlarge hscale htop hcs hlen
  have hwidth : 0 ≤ width := by dsimp only [width]; positivity
  have hwidth2 : 2 * width ≤ Real.sqrt m := by
    have he : 2 * width = 4 * (((3 + 2 * k : ℕ) : ℝ) + 3) := by
      dsimp only [width]
      rw [initialSmallCellList_length, hlen]
      push_cast
      ring
    rw [he]
    exact hreserve.2
  have hlog : 0 ≤ Real.log ((k : ℝ) ^ 4) := by
    apply Real.log_nonneg
    exact one_le_pow₀ (by exact_mod_cast hk0)
  have hΔ : 0 ≤ Δ := by
    have hm : 0 ≤ m := Nat.cast_nonneg _
    have hbase : 0 ≤ (Bs - 1 + 8 * Real.log ((k : ℝ) ^ 4)) * m := by positivity
    exact hbase.trans hwin.1
  have hupper : center + width ≤ spectatorBaseGap (Bs + 1) ((k : ℝ) ^ 4) m := hwin.2
  refine ⟨hreserve.1, hΔ, ?_, Real.exp_le_exp.mpr (by dsimp only [Δ]; linarith), ?_, ?_, ?_⟩
  · dsimp only [Δ]
    linarith
  · have hh := Real.exp_le_exp.mpr hupper
    dsimp only [spectatorBaseGap] at hh
    linarith [Real.exp_pos Δ]
  · dsimp only [Δ] at hΔ
    linarith
  · intro T
    exact movingProductNaturalCutoff_zero_window T (Y + center + width) Y Δ m (2 * width)
      (by dsimp only [Δ]; linarith) hwidth2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledPrimeCutoffs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every finite scheduled frequency stays below the live prime bands -/
namespace Ostmann
open Filter
open scoped BigOperators

theorem eventual_finite_frequency_band (k N : ℕ) (A : ℕ → ℝ) (β : ℝ) (hβ : 0 < β) :
    ∀ᶠ L : ℝ in atTop, ∀ n ≤ N,
      Real.exp (A n * spectatorBulkCount k L) < Real.exp (Real.exp (β * L)) := by
  have hi (i : Fin (N + 1)) : ∀ᶠ L : ℝ in atTop,
      A i * spectatorBulkCount k L < Real.exp (β * L) := by
    filter_upwards [eventual_polynomial_log_budget (|A i| + 1) ((k : ℝ) ^ 4) β (1 / 2) 1
      (by positivity) (by positivity) hβ (by norm_num), eventually_ge_atTop (0 : ℝ)]
      with L hbound hL
    have hm : 0 ≤ (spectatorBulkCount k L : ℝ) := Nat.cast_nonneg _
    have hh := hbound _ hm (spectatorBulkCount_upper k L hL)
    simp only [pow_one] at hh
    have ha : A i * spectatorBulkCount k L ≤ |A i| * spectatorBulkCount k L :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hm
    have hn : 0 ≤ |A i| := abs_nonneg _
    nlinarith only [hh, ha, hn, hm, Real.exp_pos (β * L)]
  filter_upwards [eventually_all.mpr hi] with L hL n hn
  exact Real.exp_lt_exp.mpr (hL ⟨n, by omega⟩)

theorem eventual_selected_frequency_band (k : ℕ) (Bs BD Bz β : ℝ) (hβ : 0 < β) :
    ∀ᶠ L : ℝ in atTop, ∀ n ≤ k, ∀ V : ℕ → ℕ,
      (V n : ℝ) ≤ Real.exp (movingFrequencyRate (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4) n *
        spectatorBulkCount k L) →
      (V n : ℝ) < Real.exp (Real.exp (β * L)) := by
  filter_upwards [eventual_finite_frequency_band k k
    (movingFrequencyRate (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4)) β hβ]
    with L hL n hn V hV
  exact hV.trans_lt (hL n hn)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedFrequencySeparation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform frequency separation below the two actual prime bands -/
namespace Ostmann
open Filter

theorem eventual_selected_frequency_separation (k : ℕ) (Bs BD Bz : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (V : ℕ → ℕ) (G : ℝ),
      (∀ n ≤ k, (V n : ℝ) ≤
        Real.exp (movingFrequencyRate (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4) n *
          spectatorBulkCount k L)) →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ G - 1 →
      ∀ n ≤ k, (V n : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ∧
        (V n : ℝ) < Real.exp (G - 1) := by
  filter_upwards [eventual_selected_frequency_band k Bs BD Bz (39 / 10000) (by norm_num),
    eventually_ge_atTop (0 : ℝ)] with L hfreq hL
  intro V G hV hG n hn
  have hf := hfreq n hn V (hV n hn)
  refine ⟨hf, hf.trans_le ?_⟩
  apply Real.exp_le_exp.mpr
  apply le_trans _ hG
  apply Real.exp_le_exp.mpr
  nlinarith only [hL]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedInitialUnshiftedCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Classical BigOperators

theorem selected_initial_unshifted_cutoff
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y G cb cd Bs BD Bz R : ℝ}
    {D : Finset ℕ} {cs : List ℕ} (k : ℕ) (hk : 2 ≤ k)
    (hL : 1 ≤ L) (hY : 0 < Y) (hYupper : Y ≤ Real.exp L)
    (hR : 0 ≤ R) (hdef0 : 0 ≤ tailDefectBudget a C Y)
    (hdef : tailDefectBudget a C Y ≤ R * L)
    (hlarge : 14 * (64 * R + 3) ≤ (k : ℝ) ^ 3)
    (hscale : 4 ≤ (k : ℝ) ^ 4 * L)
    (hcell : 1024 * tailCellLinearRate a C + 52 ≤ (k : ℝ) ^ 4)
    (hcount : (8 + 4 * cs.length : ℕ) ≤ L)
    (hm : 256 ≤ (spectatorBulkCount k L : ℝ))
    (hG : 1 ≤ G) (hcb : 0 ≤ cb)
    (hBs : 0 ≤ Bs) (hBD : 1 ≤ BD) (hBz : 0 ≤ Bz)
    (htop : SelectedSmallTailCell A B N a C L Y hi D
      ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top)
    (hcs : List.Forall₂ (fun j t => SelectedSmallTailCell A B N a C L Y hi D (t / 4) j)
      cs (movingCompensationTargets
        (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
        (movingCompensationGaps k BD Bz L))) :
    let m : ℝ := spectatorBulkCount k L
    let T := movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs)
    let W := Y + selectedInitialLogCenter G Y cb cd top cs +
      2 * ((initialSmallCellList top cs).length + 3)
    let V₀ := movingProductNaturalCutoff T W Y (m / 4) 0
    (V₀ : ℝ) ≤ Real.exp (movingFrequencyRate (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4) 0 * m) ∧
    ((transferFrequencyRange V₀).card : ℝ) ≤
      Real.exp (movingFrequencyRate (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4) 0 * m) := by
  intro m T W V₀
  have hdata := selected_scheduled_cutoff_data (Dlog := 2 * cd) k hk hL hY hYupper
    hR hdef0 hdef hlarge hscale hcell hcount hm hG hcb
    (by simp) rfl hBs hBD hBz htop hcs
  dsimp only at hdata
  have hzero := hdata.2.2.2 0 (Nat.zero_le k)
  rw [movingProductNaturalCutoff_zero_translate] at hzero
  exact hzero

theorem movingFrequencyRate_uniform_bounds (Bs BD Bz z m : ℝ) (k : ℕ) (V : ℕ → ℕ)
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) (hz : 1 ≤ z) (hm : 0 ≤ m)
    (hV : ∀ n ≤ k,
      (V n : ℝ) ≤ Real.exp (movingFrequencyRate Bs BD Bz z n * m) ∧
      ((transferFrequencyRange (V n)).card : ℝ) ≤
        Real.exp (movingFrequencyRate Bs BD Bz z n * m)) :
    ∀ n ≤ k,
      (V n : ℝ) ≤ Real.exp (movingFrequencyRate Bs BD Bz z k * m) ∧
      ((transferFrequencyRange (V n)).card : ℝ) ≤
        Real.exp (movingFrequencyRate Bs BD Bz z k * m) := by
  intro n hn
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
    (movingFrequencyRate_monotone Bs BD Bz z hBs hBD hBz hz hn) hm)
  exact ⟨(hV n hn).1.trans he, (hV n hn).2.trans he⟩

theorem frozen_spectator_window (P : ℝ) (hP : 0 < P) (Y center width : ℝ) :
    0 < Real.exp Y / P ∧
      Real.exp Y / P * Real.exp (center + width) =
        Real.exp (Y + center + width - Real.log P) := by
  refine ⟨div_pos (Real.exp_pos Y) hP, ?_⟩
  rw [Real.exp_sub, Real.exp_log hP]
  simp only [Real.exp_add, div_eq_mul_inv]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FrozenInitialSpectatorData
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Classical

theorem frozenInitialSpectatorPrimes_injective {P : Finset ℕ} {d : ℕ}
    (sl sr : Fin d → P) (hinj : Function.Injective (Fin.append sl sr)) :
    Function.Injective (frozenInitialSpectatorPrimes sl sr) :=
  Subtype.val_injective.comp hinj

theorem frozenInitialSpectatorPrimes_mem {P Q : Finset ℕ} {d : ℕ}
    (sl sr : Fin d → P) (hl : ∀ i, (sl i : ℕ) ∈ Q) (hr : ∀ i, (sr i : ℕ) ∈ Q) :
    ∀ i, frozenInitialSpectatorPrimes sl sr i ∈ Q := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [frozenInitialSpectatorPrimes, Fin.append_left] using hl j
  · simpa only [frozenInitialSpectatorPrimes, Fin.append_right] using hr j

theorem frozen_initial_spectator_data {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    {P Q D : Finset ℕ} {d cutoff : ℕ} {L ε : ℝ} (hcutoff : 3 ≤ cutoff)
    (hQ : Q ⊆ primeLogCellSet 1 0 (Real.exp ((4 / 10000 : ℝ) * L))
      (Real.exp ((6 / 10000 : ℝ) * L)) \ D)
    (hgood : ∀ p ∈ Q, cutoff ≤ p ∧
      ((1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
        residueDensity (tailDensityMask A N p) ≤ 2 / 3) ∧ tailCharacterBias A N p ≤ ε / 2)
    (sl sr : Fin d → P) (hinj : Function.Injective (Fin.append sl sr))
    (hl : ∀ i, (sl i : ℕ) ∈ Q) (hr : ∀ i, (sr i : ℕ) ∈ Q) :
    FrozenInitialSpectatorData A N (frozenInitialSpectatorPrimes sl sr) L ε cutoff D := by
  let p := frozenInitialSpectatorPrimes sl sr
  have hmem := frozenInitialSpectatorPrimes_mem sl sr hl hr
  have hp (i) : (p i).Prime :=
    (mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp (hQ (hmem i))).1).1
  have hc (i) : cutoff ≤ p i := (hgood _ (hmem i)).1
  have hne (i) : p i ≠ 2 := by have := hcutoff.trans (hc i); omega
  refine ⟨frozenInitialSpectatorPrimes_injective sl sr hinj, hp, hc,
    fun i => (Finset.mem_sdiff.mp (hQ (hmem i))).2, ?_, ?_,
    fun i => (hgood _ (hmem i)).2.1.1, fun i => (hgood _ (hmem i)).2.1.2,
    fun i => tailDensityMask_nonempty hA N (p i) (hp i).pos, ?_, ?_⟩
  · intro i
    have hb := mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp (hQ (hmem i))).1
    exact ((Real.lt_log_iff_exp_lt (by exact_mod_cast (hp i).pos)).mp hb.2.2.1).le
  · intro i
    have hb := mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp (hQ (hmem i))).1
    exact (Real.log_le_iff_le_exp (by exact_mod_cast (hp i).pos)).mp hb.2.2.2
  · intro i
    let : NeZero (p i) := ⟨(hp i).ne_zero⟩
    exact tailDensityMask_card_lt hB N (p i) (hp i).pos (hN _ (hp i))
  · intro i χ hχ a
    let : Fact (p i).Prime := ⟨hp i⟩
    exact (tailDensityMask_reverse_character_mean_bound A N (p i) (hne i) χ hχ a).trans
      (hgood _ (hmem i)).2.2

theorem FrozenInitialSpectatorData.mono {A : Set ℕ} {N d cutoff cutoff' : ℕ}
    {p : Fin (d + d) → ℕ} {L ε ε' : ℝ} {D : Finset ℕ}
    (F : FrozenInitialSpectatorData A N p L ε cutoff D)
    (hε : ε ≤ ε') (hcutoff : cutoff' ≤ cutoff) :
    FrozenInitialSpectatorData A N p L ε' cutoff' D := by
  refine ⟨F.injective, F.prime, fun i => hcutoff.trans (F.ge_cutoff i),
    F.avoids, F.lower, F.upper, F.balanced_lower, F.balanced_upper,
    F.nonempty, F.proper, ?_⟩
  intro i χ hχ a
  exact (F.character_bound i χ hχ a).trans (by linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledPageDeletions
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two actual Page deletions fit the constructed initial prime pool -/
namespace Ostmann
open scoped Classical

theorem pageDeletionPrimes_card (z : Option PrimitiveRealZero) (cutoff : ℕ) :
    (pageDeletionPrimes z cutoff).card ≤ 1 := by
  cases z with
  | none => simp [pageDeletionPrimes]
  | some z =>
    unfold pageDeletionPrimes
    cases h : deletedConductorPrime z.modulus cutoff <;> simp [h]

theorem scheduledPageDeletions_card (P : PublishedProgressionInput) (L : ℝ) (cutoff : ℕ) :
    (scheduledPageDeletions P L cutoff).card ≤ 2 := by
  exact (Finset.card_union_le _ _).trans (by
    have h₁ := pageDeletionPrimes_card (selectedPageZero P (giantProgressionCutoff L)) cutoff
    have h₂ := pageDeletionPrimes_card (selectedPageZero P (bulkProgressionCutoff L)) cutoff
    omega)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedSchedulePrimeData
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime and mass data for every actual selected prior -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem selected_regular_alphabet_nonempty
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y target : ℝ} {D : Finset ℕ}
    (htop : SelectedSmallTailCell A B N a C L Y hi D target top) :
    (initialRegularPrimeRange L).Nonempty := by
  have hmass := htop.2.2.2.2.1
  have hne : (selectedTailCellPrimes A B N Y hi D top).Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Finset.sum_empty, lt_self_iff_false] at hmass
  exact hne.mono htop.subset_initialRegularPrimeRange

theorem selected_bulk_prime_range (L : ℝ) (hL : 0 ≤ L) (D : Finset ℕ) :
    let Qb := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
      (Real.exp ((6 / 1000 : ℝ) * L)) \ D
    Qb ⊆ initialRegularPrimeRange L ∧
      ∀ p ∈ Qb, Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (p : ℝ) := by
  intro Qb
  refine ⟨initial_broad_cell_subset L (4 / 1000) (6 / 1000) hL (by norm_num) D, ?_⟩
  intro p hp
  obtain ⟨hprime, _, hlo, _⟩ := mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp hp).1
  have hl : Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤
      Real.exp (Real.exp ((4 / 1000 : ℝ) * L)) :=
    Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by nlinarith only [hL]))
  exact hl.trans ((Real.lt_log_iff_exp_lt (by exact_mod_cast hprime.pos)).mp hlo).le

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledGiantSeparation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected giant shell is separated from every regular prime -/
namespace Ostmann
open Filter

theorem eventual_scheduled_giant_lower : ∀ᶠ L : ℝ in atTop,
    ∀ lo G : ℝ, Real.exp ((1 / 20 : ℝ) * L) ≤ lo → lo - 2 ≤ G →
      2 ≤ G ∧ Real.exp ((49 / 1000 : ℝ) * L) ≤ G - 1 := by
  have hg : Tendsto (fun L : ℝ => Real.exp ((1 / 1000 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [hg.eventually (eventually_ge_atTop (4 : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with L hratio hL lo G hlo hG
  have he : Real.exp ((1 / 20 : ℝ) * L) =
      Real.exp ((49 / 1000 : ℝ) * L) * Real.exp ((1 / 1000 : ℝ) * L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hE : 1 ≤ Real.exp ((49 / 1000 : ℝ) * L) := Real.one_le_exp (by positivity)
  have hm := mul_le_mul_of_nonneg_left hratio
    (Real.exp_nonneg ((49 / 1000 : ℝ) * L))
  rw [← he] at hm
  constructor <;> nlinarith only [hm, hlo, hG, hE]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedTierConstruction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing finite tiers from the prescribed selected cells -/
namespace Ostmann
open Filter
open scoped Classical

theorem eventual_selected_tier_budgets (k : ℕ) (hk : 0 < k)
    (a C BD Bz : ℝ) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) :
    ∀ᶠ L : ℝ in atTop, ∀ X J : ℝ, 0 < X → X ≤ Real.exp L →
      16 * Real.exp ((1 / 100 : ℝ) * L) ≤ J →
      48 * (64 * tailDefectBudget a C X + 2) ≤ J ∧
        (2 : ℝ) ^ k * (movingCompensationGapRate k BD Bz * L) ≤ J / 4 := by
  let T := 48 * (64 * tailCellLinearRate a C + 2) +
    (2 : ℝ) ^ k * movingCompensationGapRate k BD Bz
  have hrate := movingCompensationGapRate_nonneg k hk BD Bz hBD hBz
  have hT : 0 ≤ T := by
    dsimp only [T]
    positivity [tailCellLinearRate_nonneg a C]
  filter_upwards [arithmetic_exponent_absorption 0 (1 / 100) 0 T 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hbudget hL
  intro X J hX hXL hJ
  simp only [pow_one, zero_mul, Real.exp_zero, mul_one, one_mul] at hbudget
  have hTL : T * L ≤ Real.exp ((1 / 100 : ℝ) * L) := by
    have hnonneg : 0 ≤ T * L := mul_nonneg hT (by linarith)
    linarith
  have hd := tailDefectBudget_linear a C L X hL hX hXL
  have hpow : 0 ≤ (2 : ℝ) ^ k * movingCompensationGapRate k BD Bz := by positivity
  have htail : 0 ≤ 48 * (64 * tailCellLinearRate a C + 2) := by
    positivity [tailCellLinearRate_nonneg a C]
  have hfirst : 48 * (64 * tailCellLinearRate a C + 2) * L ≤ T * L := by
    dsimp only [T]
    nlinarith only [mul_nonneg hpow (show 0 ≤ L by linarith)]
  have hsecond : (2 : ℝ) ^ k * (movingCompensationGapRate k BD Bz * L) ≤ T * L := by
    dsimp only [T]
    nlinarith only [mul_nonneg htail (show 0 ≤ L by linarith)]
  constructor
  · have hh : 48 * (64 * tailDefectBudget a C X + 2) ≤ T * L := by
      nlinarith only [hd, hL, hfirst]
    linarith only [hh, hTL, hJ, Real.exp_nonneg ((1 / 100 : ℝ) * L)]
  · linarith only [hsecond, hTL, hJ, Real.exp_nonneg ((1 / 100 : ℝ) * L)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConditionalMain
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two-infinite-summand theorem from the precise published inputs -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem twoInfiniteSummandsImpossible_of_published_oai
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound) (hBonami : PublishedBonamiBound)
    (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (CM CH : ℝ) (hM : MertensEstimate CM) (hMH : MertensHarmonicEstimate CH)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (Pexplicit : PublishedSmoothExplicitFormula Z)
    (hPNT : PublishedSmoothPrincipalPNT) : TwoInfiniteSummandsImpossible := by
  intro A B hA hB h
  obtain ⟨c, ψ, hc, _hreal, hψ, hψlower, hsupp⟩ := exists_positive_fourier_cutoff
  obtain ⟨N, a, ha, hN, hconstruct⟩ := h.constructed_initial_amplitude P0 ls hsize hBonami
    Hreal hSiegel sieve hA hB CM CH hM hMH Z hD hR Pexplicit hPNT ψ ((3 : ℝ) ^ 2) c
    (by positivity) hc hψ hsupp hψlower
  obtain ⟨Bs, BD, hBs, hBD, hgapInitial, hgapDiagonal⟩ := scheduled_gap_parameters
  obtain ⟨Dφ, hDφ, hloglip⟩ := logCellProfile_lipschitz
  have hfinal := P0.selected_scheduled_final_contradiction CM hM (𝓕 ψ)
    Bs BD 9 scheduledIterationRate Dφ (by linarith) (by linarith) (by norm_num) hDφ hloglip
  obtain ⟨k, hkFinal, hk, hdepth, hlarge, hkReserve, hkCell⟩ :=
    (hfinal.and (eventual_scheduled_depth_reserves (tailCellLinearRate a CM))).exists
  let Wwin := Bs + 1 + 8 * Real.log ((k : ℝ) ^ 4)
  have hz : 1 ≤ (k : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ k by omega))
  have hWwin : 0 ≤ Wwin := by
    have hh := Real.log_nonneg hz
    dsimp only [Wwin]
    linarith
  obtain ⟨εF, hεF, _hεF1, pF, hpF, hFL⟩ := hkFinal Wwin hWwin hdepth
  obtain ⟨εD, hεD, _hεD1, pD, hpD, hDL⟩ := P0.selected_scheduled_diagonal CM hM (𝓕 ψ)
    k hk Bs BD 9 scheduledIterationRate Wwin Dφ hBs (by linarith) (by norm_num)
    hWwin hDφ hloglip hdepth hgapDiagonal
  let ε := min εD εF
  let p₀ := max pD pF
  have hε : 0 < ε := lt_min hεD hεF
  have hp₀ : 3 ≤ p₀ := hpD.trans (le_max_left _ _)
  have hconstruct := hconstruct k hk Bs BD 9 (by linarith) (by linarith) (by norm_num)
    hgapInitial hlarge p₀ ε hε
  have ht : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hfalse : ∀ᶠ reference : ℕ in atTop, False := by
    filter_upwards [hconstruct, ht.eventually hDL, ht.eventually hFL,
      ht.eventually eventual_initial_regular_prime_range,
      ht.eventually (eventual_initial_giant_prime_range k hk),
      ht.eventually (eventual_scheduled_iteration_thresholds k hk a CM hkReserve),
      ht.eventually (eventual_initial_protected_target k hk Bs BD 9
        (by linarith) (by linarith) (by norm_num)),
      ht.eventually (eventual_initial_selected_centers_lower k hk Bs BD 9
        (by linarith) (by linarith) (by norm_num)),
      ht.eventually (eventual_selected_tier_budgets k (by omega) a CM BD 9
        (by linarith) (by norm_num)),
      ht.eventually (eventual_selected_initial_energy_window k hk Bs BD 9
        (tailCellLinearRate a CM) hBs (tailCellLinearRate_nonneg a CM) hlarge),
      ht.eventually eventual_scheduled_giant_lower,
      ht.eventually (eventual_tailDefectBudget_nonneg a CM),
      ht.eventually (eventual_selected_frequency_band k Bs BD 9 (39 / 10000) (by norm_num)),
      ht.eventually (eventual_selected_frequency_separation k Bs BD 9),
      ht.eventually (eventually_gt_atTop (2 : ℝ))]
      with reference hconstruct hDL hFL hregular hgiant hiteration hprotected hcenters
        htiers henergy hGlarge hdefNonneg hsmallFreq hfrequencies hL
    let L := Real.log (Real.log (reference : ℝ))
    obtain ⟨lo, hlo, _hloUpper, favorablePrimes, _hfavorable, Y, endpoint, hendpoint,
      hYlo, hYhi, hYlower, hYupper, G, hGlo, hGhi, hGmass, hGnorm, hselected⟩ := hconstruct
    let D := scheduledPageDeletions P0 L (scheduledComparisonCutoff L)
    have hDcard : (D.card : ℝ) ≤ Real.exp L := by
      have hh : (D.card : ℝ) ≤ 2 := by exact_mod_cast scheduledPageDeletions_card P0 L (scheduledComparisonCutoff L)
      have he := Real.add_one_le_exp L
      linarith
    obtain ⟨Qd, cb, cd, top, cs, hQd, _hQdmass, hgood, hcb, hcd, htop, hcs, hlen, hstart⟩ :=
      hselected D hDcard
    let m := spectatorBulkCount k L
    let b := m / 2
    have hsize : spectatorBulkCount k L = b + b := by
      obtain ⟨d, hd⟩ := spectatorBulkCount_even k L
      dsimp only [b, m]
      omega
    have hsize' : spectatorBulkCount k (Real.log (Real.log (reference : ℝ))) = b + b := hsize
    have hY : 0 < Y := (Real.exp_pos _).trans_le hYlower
    have hL1 : 1 ≤ L := by linarith
    have hcb0 : 0 ≤ (cb : ℝ) := (initial_log_center_bounds m _ cb hcb).1
    have hdef := tailDefectBudget_linear a CM L Y hL1 hY hYupper
    have hdef0 : 0 ≤ tailDefectBudget a CM Y := hdefNonneg Y hYlower
    have hscale : 4 ≤ (k : ℝ) ^ 4 * L := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
        (show (2 : ℝ) ≤ k by exact_mod_cast hk) 4
      norm_num at hh
      nlinarith
    obtain ⟨hm, hcount, herror, hbudget⟩ := hiteration Y hY hYupper top cs hlen
    have hGdata := hGlarge lo G hlo hGlo
    have hlower := hcenters cb cd hcb hcd hYlo hYhi hGlo hGhi htop hcs
    let T := movingCellPivotExponent (fun _ => (G : ℝ)) (selectedCompensationCenter cs)
    let center := selectedInitialLogCenter G Y cb cd top cs
    let width : ℝ := 2 * ((initialSmallCellList top cs).length + 3)
    have hzero := selected_initial_unshifted_cutoff k hk hL1 hY hYupper
      (tailCellLinearRate_nonneg a CM) hdef0 hdef hlarge hscale hkCell hcount hm
      (by linarith only [hGdata.1]) hcb0 (by linarith) (by linarith) (by norm_num) htop hcs
    dsimp only at hzero
    let P := Nat.primesLE (tailCollisionCutoff Y)
    let Q := initialRegularPrimeRange L
    let Qb := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
      (Real.exp ((6 / 1000 : ℝ) * L)) \ D
    let cells := initialSmallCellList top cs
    have hP : ∀ p ∈ P, p.Prime := fun _ hp => Nat.prime_of_mem_primesLE hp
    have hQprime := initialRegularPrimeRange_prime L
    let : ∀ p : P, NeZero (p : ℕ) := fun p => ⟨(hP p p.property).ne_zero⟩
    have hQP : Q ⊆ P := hregular Y hYlower hYupper
    have hgiantP : smoothGiantPrimeRange G ⊆ P := hgiant lo Y G hYlower hYupper hYlo hGhi
    obtain ⟨hbulk, hbulkLower⟩ := selected_bulk_prime_range L (by linarith) D
    have hQdSmall : Qd ⊆ Q := hQd.trans
      (initial_broad_cell_subset L (4 / 10000) (6 / 10000) (by linarith) (by norm_num) D)
    obtain ⟨_hweighted, sl₀, sr₀, hinj₀, hsl₀, hsr₀, hfrozen⟩ := hstart T
    let sl := restrictPrimeSamples sl₀ (fun i => hQdSmall (hsl₀ i))
    let sr := restrictPrimeSamples sr₀ (fun i => hQdSmall (hsr₀ i))
    let e := primeAlphabetEmbedding hQP
    have hslEq : e ∘ sl = sl₀ := restrictPrimeSamples_embedding hQP sl₀ _
    have hsrEq : e ∘ sr = sr₀ := restrictPrimeSamples_embedding hQP sr₀ _
    have hinj : Function.Injective (Fin.append (e ∘ sl) (e ∘ sr)) := by
      rw [hslEq, hsrEq]
      exact hinj₀
    have hsl : ∀ i, ((e ∘ sl) i : ℕ) ∈ Qd := by rw [hslEq]; exact hsl₀
    have hsr : ∀ i, ((e ∘ sr) i : ℕ) ∈ Qd := by rw [hsrEq]; exact hsr₀
    let q : Fin (b + b) → ℕ := fun i => ((Fin.append (e ∘ sl) (e ∘ sr) i : P) : ℕ)
    let : ∀ i, Fact (q i).Prime := fun i => ⟨hP _ (Fin.append (e ∘ sl) (e ∘ sr) i).property⟩
    have hqData : FrozenInitialSpectatorData A N q L ε p₀ D :=
      frozen_initial_spectator_data hA hB N hN hp₀ hQd hgood
        (e ∘ sl) (e ∘ sr) hinj hsl hsr
    let hcq : Pairwise (fun i j => (q i).Coprime (q j)) := fun i j hij =>
      (Nat.coprime_primes (hqData.prime i) (hqData.prime j)).mpr
        (fun heq => hij (hqData.injective heq))
    let Dq := initialSpectatorCofactor q hcq
    let fallback : Q := ⟨(selected_regular_alphabet_nonempty htop).choose,
      (selected_regular_alphabet_nonempty htop).choose_spec⟩
    let Dlog := Real.log ((∏ i, q i : ℕ) : ℝ)
    let X := Real.exp Y / (∏ i, q i : ℕ)
    let lower := Real.exp (center - width)
    let upper := Real.exp (center + width)
    let μ := completedCompensationPrior A B N Y endpoint D Q top cs
    let V := movingProductNaturalCutoff T (Y + center + width - Dlog) (Y - Dlog) ((m : ℝ) / 4)
    let g : ∀ i, ZMod (q i) → ℂ := fun i => normalizedResidueFamily (tailDensityMask A N) (q i)
    let leaf := movingOriginalLeaf Subtype.val q
      (initialMovingDataCutoff Subtype.val b b cells.length cb cd sl sr fallback)
      g Dq Finset.univ (𝓕 ψ) X lower upper
    let favorable := fun p => decide (p ∈ favorablePrimes)
    let η := fun n => scheduledCellAmplitude Subtype.val (List.ofFn q) μ (scheduledChildBound V)
      (scheduledPivotCaps G cs) V leaf logCellProfile (fun _ => (G : ℝ))
      (smoothGiantPrimeRange G) (smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G)
      (fun c => primeSubsetPrior Q (selectedTailCellPrimes A B N Y endpoint D c))
      (primeSubsetPrior Q Qb) top cs n (b + b)
      (normalizedResidueFamily (tailDensityMask A N)) (normalizedResidueFamily (tailDensityMask A N)) favorable
    have hVzero : V 0 = movingProductNaturalCutoff T (Y + center + width) Y ((m : ℝ) / 4) 0 :=
      movingProductNaturalCutoff_zero_translate T (Y + center + width) Y ((m : ℝ) / 4) Dlog
    have hVzeroGiant : (V 0 : ℝ) < Real.exp ((G : ℝ) - 1) := by
      rw [hVzero]
      have hv := hsmallFreq 0 (Nat.zero_le _) (fun _ => movingProductNaturalCutoff T
        (Y + center + width) Y ((m : ℝ) / 4) 0) hzero.1
      apply hv.trans_le
      apply Real.exp_le_exp.mpr
      exact (Real.exp_le_exp.mpr (by linarith : (39 / 10000 : ℝ) * L ≤ (49 / 1000 : ℝ) * L)).trans hGdata.2
    have hid := frozen_initial_small_amplitude (cb := (cb : ℝ)) (cd := (cd : ℝ)) htop hcs
      P hP hQP hgiantP Qb hbulk b b sl sr hinj
      (fun i => hsl₀ i) (fun i => hsr₀ i)
      fallback (tailDensityMask A N) favorable ψ
      (completedCompensationSets A B N Y endpoint D top cs) (scheduledChildBound V)
      (scheduledPivotCaps G cs) V hVzeroGiant
    dsimp only at hid
    change _ = η 0 at hid
    have hinit : Real.exp (-scheduledInitialRate * (m : ℝ)) ≤ ‖η 0‖ := by
      rw [← hid]
      have hp := hfrozen
      rw [← hslEq, ← hsrEq] at hp
      simpa only [scheduledInitialRate, hVzero] using hp
    have hηnonzero : η 0 ≠ 0 := by
      intro hh
      have hn := hinit
      rw [hh, norm_zero] at hn
      exact (not_le_of_gt (Real.exp_pos _)) hn
    have hηsource := hηnonzero
    unfold η scheduledCellAmplitude at hηsource
    rw [List.drop_zero] at hηsource
    have hcertificate := initialTemplateAmplitude_spectator_product Subtype.val
      (fun p : Q => (hQprime p p.property).pos) b b cells.length (scheduledSmallLength cs)
      cb cd sl sr fallback q g Dq Finset.univ (𝓕 ψ) X lower upper (List.ofFn q) μ
      (scheduledChildBound V) (scheduledPivotCaps G cs) V logCellProfile (fun _ => (G : ℝ))
      (smoothGiantPrimeRange G) (smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G)
      (scheduledRegularPrior (fun c => primeSubsetPrior Q
        (selectedTailCellPrimes A B N Y endpoint D c)) (primeSubsetPrior Q Qb) top cs 0 (b + b))
      (normalizedResidueFamily (tailDensityMask A N))
      (normalizedResidueFamily (tailDensityMask A N)) favorable
      hηsource
    have hqProduct : (∏ i, q i : ℕ) = ∏ i, ((Fin.append sl sr i : Q) : ℕ) := by
      apply Finset.prod_congr rfl
      intro i _
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · dsimp only [q]
        rw [Fin.append_left, Fin.append_left]
        rfl
      · dsimp only [q]
        rw [Fin.append_right, Fin.append_right]
        rfl
    have hDlog : |Dlog - 2 * (cd : ℝ)| ≤ 2 := by
      dsimp only [Dlog]
      rw [hqProduct]
      exact hcertificate.le
    have hcut := selected_scheduled_cutoff_data k hk hL1 hY hYupper
      (tailCellLinearRate_nonneg a CM) hdef0 hdef hlarge hscale hkCell hcount hm
      (by linarith only [hGdata.1]) hcb0 hDlog rfl (by linarith) (by linarith) (by norm_num) htop hcs
    dsimp only at hcut
    have hVmono : Monotone V := hcut.1
    have hVbound := hcut.2.2.2
    have hVuniform := movingFrequencyRate_uniform_bounds (Bs + 1) (BD + 2) 9 ((k : ℝ) ^ 4)
      (m : ℝ) k V (by linarith) (by linarith) (by norm_num) hz (Nat.cast_nonneg _) hVbound
    have hVseparated := hfrequencies V G (fun n hn => (hVbound n hn).1) hGdata.2
    have hproduct : 0 < ((∏ i, q i : ℕ) : ℝ) := by
      exact_mod_cast Finset.prod_pos (fun i _ => (hqData.prime i).pos)
    have hXwindow := frozen_spectator_window ((∏ i, q i : ℕ) : ℝ) hproduct Y center width
    obtain ⟨_, hΔ, hΔbound, hlu, hWin, _, hV0bound⟩ := henergy hdef htop hcs hlen
    let J := movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD 9 L)
    have hJ := hprotected cb cd hcb hcd lo G Y hYlo hYhi hGlo hGhi
    have hTier := htiers Y J hY hYupper hJ.1
    have hg : g = (fun i => normalizedResidueTransform (tailDensityMask A N (q i))) := by
      funext i
      exact normalizedResidueFamily_eq (tailDensityMask A N) (q i)
    have hDdata := hqData.mono (min_le_left _ _) (le_max_left _ _)
    have hFdata := hqData.mono (min_le_right _ _) (le_max_right _ _)
    have hU (n : ℕ) (hn : n ≤ k) :
        (V n : ℝ) ≤ Real.exp (movingFrequencyRate (Bs + 1) (BD + 2) 9 ((k : ℝ) ^ 4) k * (b + b : ℕ)) ∧
        ((transferFrequencyRange (V n)).card : ℝ) ≤
          Real.exp (movingFrequencyRate (Bs + 1) (BD + 2) 9 ((k : ℝ) ^ 4) k * (b + b : ℕ)) := by
      simpa only [m, hsize] using hVuniform n hn
    have hV0Window : (V 0 : ℝ) ≤ Real.exp (center - width + Real.sqrt (4 * (b + b : ℕ))) := by
      rw [hVzero]
      simpa only [center, width, m, L, hsize'] using hV0bound T
    have hΔbound' : center - width ≤ spectatorBaseGap (Bs + 1) ((k : ℝ) ^ 4) (b + b : ℕ) := by
      simpa only [center, width, hsize'] using hΔbound
    have hWin' : upper - lower ≤ Real.exp (Wwin * (b + b : ℕ)) := by
      simpa only [upper, lower, center, width, Wwin, hsize'] using hWin
    have hdiagonal := hDL A B hA hB N hN b endpoint top a Y G J cb cd (center - width)
      upper X cs hsize hlen hY hYupper hcb0 hkCell hcount hJ.1 hTier.1 hTier.2
      htop hcs hlower hGdata.2 hGnorm q hDdata sl sr fallback Dq
      (scheduledChildBound V) (scheduledPivotCaps G cs) V hVmono
      (fun n hn => (hU n hn).1) (fun n hn => (hU n hn).2) hV0Window hΔ hΔbound' hlu hWin' favorable
    dsimp only at hdiagonal
    have hdiagTransfer : ∀ n < k,
        scheduledCellDiagonal Subtype.val (List.ofFn q) μ (scheduledChildBound V)
          (scheduledPivotCaps G cs) V leaf logCellProfile (fun _ => (G : ℝ))
          (smoothGiantPrimeRange G) (Finset.Ioc ⌊Real.exp ((G : ℝ) - 1)⌋₊ ⌊Real.exp ((G : ℝ) + 1)⌋₊)
          (smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G)
          (fun c => primeSubsetPrior Q (selectedTailCellPrimes A B N Y endpoint D c))
          (primeSubsetPrior Q Qb) top cs n (b + b)
          (normalizedResidueFamily (tailDensityMask A N))
          (normalizedResidueFamily (tailDensityMask A N)) favorable ≤
          Real.exp (-(2 * (scheduledInitialRate + 1) + 3) * (2 : ℝ) ^ n * m) := by
      intro n hn
      simpa only [leaf, hg, μ, cells, lower, upper, m, hsize, scheduledIterationRate,
        Nat.cast_pow, Nat.cast_ofNat] using hdiagonal n hn
    have hmassG : 0 < smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G :=
      (Real.exp_pos _).trans_le hGmass
    have hIter := selected_scheduled_iteration hA hB k hk hQprime (fun _ hp => hp)
      hL1 hY hYupper hkCell hcount hm (by linarith only [hGdata.1]) hcb0 hDlog
      (by linarith) hBD (by norm_num) herror hbudget htop hcs hlower hbulk hbulkLower
      (fun p hp => hN p (hQprime p hp)) b b sl sr fallback q g Dq Finset.univ (𝓕 ψ)
      X lower upper hXwindow.1 logCellProfile logCellProfile_nonneg logCellProfile_zero_outside hmassG
      (List.ofFn q) favorable scheduledInitialRate
      hXwindow.2.le (fun n hn => (hVseparated n hn).1) (fun n hn => (hVseparated n hn).2)
      (by nlinarith only [hGnorm, hL]) hinit hdiagTransfer
    have hFinalAmplitude := hIter k le_rfl
    conv at hFinalAmplitude =>
      lhs
      rw [hsize]
    apply hFL A B hA hB N hN b endpoint top a Y G J cb cd (center - width) upper X cs
      hsize hlen hcb0 hJ.1 hTier.1 hTier.2 htop hcs hlower hGdata.2
      (by nlinarith only [hGnorm, hL]) q hFdata sl sr fallback Dq
      (scheduledChildBound V) (scheduledPivotCaps G cs) V hVmono (hU k le_rfl).1
      (hU k le_rfl).2 hV0Window hΔ hΔbound' hlu hWin' favorable
    simpa only [η, μ, leaf, hg, cells, lower, upper, scheduledIterationRate] using hFinalAmplitude
  obtain ⟨_, hf⟩ := hfalse.exists
  exact hf

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.twoInfiniteSummandsImpossible_of_published_oai := @OAI.Ostmann.twoInfiniteSummandsImpossible_of_published_oai
