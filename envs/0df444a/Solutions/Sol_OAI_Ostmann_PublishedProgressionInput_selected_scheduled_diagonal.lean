-- Prove2me | solution 1 for OAI.Ostmann.PublishedProgressionInput.selected_scheduled_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:32:27.670642+00:00
-- url     : https://prove2.me/submissions/e66e3726-5006-4a78-9fa0-c50b5c76639b

import Mathlib
import Definitions.Def_OAIQ095D008
import Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_moving_selected_initial_diagonal_uniform

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicWordPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic laws for all word roles on one common prime sample space -/

namespace Ostmann

open scoped BigOperators Classical

theorem primeSubsetPrior_nonneg (P Q : Finset ℕ) (p : P) :
    0 ≤ primeSubsetPrior P Q p := by
  unfold primeSubsetPrior
  split_ifs
  · exact div_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => by positivity))
  · exact le_rfl

theorem primeSubsetPrior_support (P Q : Finset ℕ) (p : P)
    (hp : primeSubsetPrior P Q p ≠ 0) : (p : ℕ) ∈ Q := by
  by_contra hn
  simp [primeSubsetPrior, hn] at hp

theorem primeSubsetPrior_mass (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hm : (∑ q ∈ Q, (q : ℝ)⁻¹) ≠ 0) : (∑ p : P, primeSubsetPrior P Q p) = 1 := by
  unfold primeSubsetPrior
  rw [Finset.sum_coe_sort P (fun p => if p ∈ Q then
    (p : ℝ)⁻¹ / (∑ q ∈ Q, (q : ℝ)⁻¹) else 0), ← Finset.sum_filter]
  have hf : P.filter (fun p => p ∈ Q) = Q := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hQP h, h⟩⟩
  rw [hf, ← Finset.sum_div]
  exact div_self hm

theorem primeSubsetPrior_atom (P Q : Finset ℕ) (p : P) :
    primeSubsetPrior P Q p ≤ (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * (p : ℝ)⁻¹ := by
  unfold primeSubsetPrior
  split_ifs
  · exact le_of_eq (by ring)
  · positivity

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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkDeletionCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deleted-atom costs in the actual original bulk prior -/

namespace Ostmann
open scoped Classical BigOperators

theorem bulk_deleted_reciprocal_mass_le (S D : Finset ℕ) (T : ℝ)
    (hlow : ∀ q ∈ S, Real.exp T ≤ (q : ℝ)) :
    (∑ q ∈ S ∩ D, (q : ℝ)⁻¹) ≤ (D.card : ℝ) * Real.exp (-T) := by
  calc
    _ ≤ ∑ _q ∈ S ∩ D, Real.exp (-T) := by
      apply Finset.sum_le_sum
      intro q hq
      simpa only [Real.exp_neg] using inv_anti₀ (Real.exp_pos T)
        (hlow q (Finset.mem_inter.mp hq).1)
    _ = ((S ∩ D).card : ℝ) * Real.exp (-T) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card Finset.inter_subset_right)
      (Real.exp_nonneg _)

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

theorem movingFrequencyRate_nonneg (Bs BD Bz z : ℝ)
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) (hz : 1 ≤ z) (n : ℕ) :
    0 ≤ movingFrequencyRate Bs BD Bz z n := by
  have hl := Real.log_nonneg hz
  have hr := Real.log_nonneg (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := n))
  unfold movingFrequencyRate
  positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRegularTemplate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual small and bulk slots at a moving-giant level -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingRegularSlot_card (n r m : ℕ) :
    Fintype.card (MovingRegularSlot n r m) = 2 ^ n * (r + m) := by
  simp only [MovingRegularSlot, Fintype.card_prod, card_treeLeafIndex, Fintype.card_sum,
    Fintype.card_fin]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite support for the actual positive-integer giant extension -/

namespace Ostmann
open scoped Classical BigOperators

theorem smoothGiantPrimeRange_prime (G : ℝ) :
    ∀ p ∈ smoothGiantPrimeRange G, p.Prime := fun _ hp => (Finset.mem_filter.mp hp).2

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeMaskExtension
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Completing the regular mask family without changing sampled primes -/
namespace Ostmann
open scoped Classical

theorem primeMaskExtension_eq (P : Finset ℕ) (sets : ∀ p : ℕ, Finset (ZMod p))
    (p : ℕ) (hp : p ∈ P) : primeMaskExtension P sets p = sets p := by
  simp only [primeMaskExtension, ite_eq_left hp]

theorem primeMaskExtension_data (P : Finset ℕ) (sets : ∀ p : ℕ, Finset (ZMod p))
    (hsets : ∀ p ∈ P, (sets p).Nonempty ∧ (sets p).card < p)
    (p : ℕ) (hp : p.Prime) :
    (primeMaskExtension P sets p).Nonempty ∧ (primeMaskExtension P sets p).card < p := by
  by_cases hmem : p ∈ P
  · rw [primeMaskExtension_eq P sets p hmem]
    exact hsets p hmem
  · simp only [primeMaskExtension, ite_eq_right hmem, Finset.singleton_nonempty,
      Finset.card_singleton, true_and]
    exact hp.one_lt

theorem tailPrimeMaskExtension_data {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hdis : ∀ p ∈ P, Disjoint (tailResidues A N p) (negTailResidues B N p)) :
    ∀ p, p.Prime →
      (primeMaskExtension P (tailDensityMask A N) p).Nonempty ∧
      (primeMaskExtension P (tailDensityMask A N) p).card < p := by
  apply primeMaskExtension_data P (tailDensityMask A N)
  intro p hp
  let : NeZero p := ⟨(hP p hp).ne_zero⟩
  exact ⟨tailDensityMask_nonempty hA N p (hP p hp).pos,
    tailDensityMask_card_lt hB N p (hP p hp).pos (hdis p hp)⟩

theorem normalizedResidueFamily_primeMaskExtension (P : Finset ℕ)
    (sets : ∀ p : ℕ, Finset (ZMod p)) (p : ℕ) (hp : p ∈ P) :
    normalizedResidueFamily (primeMaskExtension P sets) p = normalizedResidueFamily sets p := by
  unfold normalizedResidueFamily
  split
  · rfl
  · rw [primeMaskExtension_eq P sets p hp]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRegularTransformCongruence
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Changing regular tests away from the sampled alphabet changes no statistic -/
namespace Ostmann
open scoped Classical BigOperators

theorem movingTaggedTransform_regular_congr {I J : Type*} [Fintype I] [Fintype J]
    (p : I → ℕ) (q : J → ℕ) (greg hreg ggiant : ∀ r : ℕ, ZMod r → ℂ)
    (favorable : ℕ → Bool) (D : ℕ) (s : ℤ) (hregEq : ∀ j, greg (q j) = hreg (q j)) :
    movingTaggedTransform (Sum.elim p q) (Sum.elim (fun _ => true) (fun _ => false))
      greg ggiant favorable D s =
    movingTaggedTransform (Sum.elim p q) (Sum.elim (fun _ => true) (fun _ => false))
      hreg ggiant favorable D s := by
  unfold movingTaggedTransform
  apply Finset.prod_congr rfl
  intro i _
  cases i with
  | inl i => rfl
  | inr j => simp only [Sum.elim_inr, Bool.false_eq_true, ↓reduceIte, hregEq j]

theorem movingAmplitudeDiagonal_regular_congr {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (Pg I : Finset ℕ) (ρ : Pg → ℝ)
    (ν : MovingRegularSlot n r m → σ → ℝ)
    (greg hreg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (hregEq : ∀ a, greg (value a) = hreg (value a)) :
    movingAmplitudeDiagonal value outside μ childBound pivotBound V F φ G n r m
      Pg I ρ ν greg ggiant favorable =
    movingAmplitudeDiagonal value outside μ childBound pivotBound V F φ G n r m
      Pg I ρ ν hreg ggiant favorable := by
  unfold movingAmplitudeDiagonal
  dsimp only
  simp_rw [show ∀ X (y : MovingRegularSlot n r m → σ) D s,
    movingTaggedTransform (movingOneGiantModuli X (value ∘ y))
      (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable D s =
    movingTaggedTransform (movingOneGiantModuli X (value ∘ y))
      (Sum.elim (fun _ => true) (fun _ => false)) hreg ggiant favorable D s from
    fun X y D s => movingTaggedTransform_regular_congr (fun _ : Unit => X)
      (value ∘ y) greg hreg ggiant favorable D s (fun i => hregEq _)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterBandCutoffs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer endpoints for the separated character prime bands -/
namespace Ostmann
open Filter

/-- A fixed positive gap in log-log scale supplies the factor two required
by the one-sided character estimate, even after rounding upward. -/
theorem eventual_double_exp_integer_margin (α β : ℝ) (hβ : 0 < β) (hαβ : α < β) :
    ∀ᶠ L : ℝ in atTop,
      2 * (⌈Real.exp (Real.exp (α * L))⌉₊ : ℝ) ≤ Real.exp (Real.exp (β * L)) := by
  filter_upwards [arithmetic_exponent_absorption α β 0 4 1 0 hβ hαβ hβ (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hgap hL
  simp only [pow_zero, zero_mul, Real.exp_zero, one_mul] at hgap
  have hlog4 : Real.log 4 ≤ 3 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hm := mul_le_mul_of_nonneg_right hL (Real.exp_nonneg (α * L))
  have he : Real.log 4 + Real.exp (α * L) ≤ Real.exp (β * L) := by
    nlinarith only [hgap, hm, Real.exp_nonneg (α * L), hlog4]
  have hceil := (Nat.ceil_lt_add_one (Real.exp_nonneg (Real.exp (α * L)))).le
  have hexp : 1 ≤ Real.exp (Real.exp (α * L)) :=
    Real.one_le_exp (Real.exp_nonneg _)
  calc
    _ ≤ 4 * Real.exp (Real.exp (α * L)) := by linarith
    _ = Real.exp (Real.log 4 + Real.exp (α * L)) := by
      rw [Real.exp_add, Real.exp_log (by norm_num)]
    _ ≤ _ := Real.exp_le_exp.mpr he

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_CompensationCellSeparation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Distinct compensation types occupy disjoint prime cells -/

namespace Ostmann

theorem movingCompensationTargets_upper (J B : ℝ) (ds : List ℝ)
    (hJ : 0 ≤ J) (hd : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ B) :
    ∀ w ∈ movingCompensationTargets J ds, w ≤ 2 ^ ds.length * J / 2 := by
  induction ds with
  | nil => simp [movingCompensationTargets]
  | cons d ds ih =>
    have hd0 := hd d (by simp)
    have hds : ∀ e ∈ ds, 0 ≤ e ∧ e ≤ B := fun e he => hd e (by simp [he])
    have herr := (movingCompensationTargetError_bounds B ds hds).1
    have hsum := movingCompensationTargets_sum J ds
    have hpJ : 0 ≤ (2 : ℝ) ^ ds.length * J := by positivity
    intro w hw
    simp only [movingCompensationTargets, List.mem_cons] at hw
    simp only [List.length_cons, pow_succ]
    rcases hw with rfl | hw
    · linarith
    · have hh := ih hds w hw
      linarith

theorem movingCompensationTargets_separated (J B : ℝ) (ds : List ℝ)
    (hJ : 0 ≤ J) (hB : B ≤ J / 4)
    (hd : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ B) :
    (movingCompensationTargets J ds).Pairwise (fun x y => y + J / 4 ≤ x) := by
  induction ds with
  | nil => simp [movingCompensationTargets]
  | cons d ds ih =>
    have hd0 := hd d (by simp)
    have hds : ∀ e ∈ ds, 0 ≤ e ∧ e ≤ B := fun e he => hd e (by simp [he])
    have herr := (movingCompensationTargetError_bounds B ds hds).2
    have hsum := movingCompensationTargets_sum J ds
    change ((J + (movingCompensationTargets J ds).sum - d) ::
      movingCompensationTargets J ds).Pairwise _
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih hds⟩
    intro w hw
    have hu := movingCompensationTargets_upper J B ds hJ hds w hw
    have hp : (1 : ℝ) ≤ 2 ^ ds.length := one_le_pow₀ (by norm_num)
    have hpB := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ (2 : ℝ) ^ ds.length)
    have hpJ := mul_le_mul_of_nonneg_right hp hJ
    nlinarith only [hu, herr, hsum, hpB, hpJ, hd0.2]

theorem compensation_cell_separation (J E w v c d : ℝ)
    (hgap : v + J / 4 ≤ w) (hbudget : 16 * (E + 1) ≤ J)
    (hc : w / 4 ≤ c) (hd : d ≤ v / 4 + E) :
    d + 1 ≤ c := by linarith

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailFourierMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One total Fourier-mass function for the actual tail masks -/
namespace Ostmann
open scoped Classical BigOperators

theorem tailDensityMask_balanced_iff (A : Set ℕ) (N p : ℕ) (hp : 0 < p) :
    ((1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
      residueDensity (tailDensityMask A N p) ≤ 2 / 3) ↔
    ((p : ℝ) / 3 ≤ (tailSupport A N p).card ∧
      ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3) := by
  unfold residueDensity
  rw [tailDensityMask_card]
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  constructor
  · rintro ⟨hl, hu⟩
    rw [le_div_iff₀ hp'] at hl
    rw [div_le_iff₀ hp'] at hu
    constructor <;> linarith
  · rintro ⟨hl, hu⟩
    constructor
    · apply (le_div_iff₀ hp').mpr
      linarith
    · apply (div_le_iff₀ hp').mpr
      linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedInitialCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Top and compensation cells for the actual initial cutoff centers -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem SelectedSmallTailCell.prior_data
    {A B : Set ℕ} {N hi j : ℕ} {a C L Y target : ℝ} {D : Finset ℕ}
    (h : SelectedSmallTailCell A B N a C L Y hi D target j)
    (P : Finset ℕ) (hQP : selectedTailCellPrimes A B N Y hi D j ⊆ P) :
    let Q := selectedTailCellPrimes A B N Y hi D j
    (∑ p : P, primeSubsetPrior P Q p) = 1 ∧
    (∀ p : P, 0 ≤ primeSubsetPrior P Q p ∧
      (p : ℝ) * primeSubsetPrior P Q p ≤ Real.exp (2 * L)) ∧
    (∀ p : P, primeSubsetPrior P Q p ≠ 0 →
      (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
        residueDensity (tailDensityMask A N p) ≤ 2 / 3) := by
  intro Q
  obtain ⟨_, _, _, _, hpos, hinv, hsupport⟩ := h
  refine ⟨primeSubsetPrior_mass P Q hQP hpos.ne', ?_, ?_⟩
  · intro p
    refine ⟨primeSubsetPrior_nonneg P Q p, ?_⟩
    by_cases hp : (p : ℕ) ∈ Q
    · have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hsupport p hp).1.ne_zero
      calc
        _ ≤ (p : ℝ) * ((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * (p : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left (primeSubsetPrior_atom P Q p) (Nat.cast_nonneg _)
        _ = (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ := by field_simp
        _ ≤ _ := hinv
    · simp only [primeSubsetPrior, hp, ite_false, if_false, mul_zero]
      positivity
  · intro p hp
    have hs := hsupport p (primeSubsetPrior_support P Q p hp)
    exact (tailDensityMask_balanced_iff A N p hs.1.pos).mpr ⟨hs.2.2.2.1, hs.2.2.2.2⟩

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

theorem initial_selected_cells_valid
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y target : ℝ} {D : Finset ℕ}
    {centers : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y hi D target top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) centers targets) :
    ∀ j ∈ initialSmallCellList top centers,
      ∃ t, SelectedSmallTailCell A B N a C L Y hi D t j := by
  refine initialSmallCellList_property top centers
    (fun j => ∃ t, SelectedSmallTailCell A B N a C L Y hi D t j) ⟨target, htop⟩ ?_
  induction hcenters with
  | nil => simp
  | @cons j w js ws hj hrest ih =>
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact ⟨w / 4, hj⟩
    · exact ih i hi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantActiveSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Size and separation on the support of the smooth giant law -/

namespace Ostmann

theorem smoothGiantPrior_active_bounds (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (p : P) (hp : smoothGiantPrior P φ G p ≠ 0) :
    Real.exp (G - 1) < (p : ℝ) ∧ (p : ℝ) < Real.exp (G + 1) := by
  have hφ : φ (Real.log (p : ℕ) - G) ≠ 0 := by
    intro h
    apply hp
    simp only [smoothGiantPrior, h, mul_zero, zero_div]
  have habs : |Real.log (p : ℕ) - G| < 1 := lt_of_not_ge (fun h => hφ (hout _ h))
  have hpos : (0 : ℝ) < (p : ℕ) := by exact_mod_cast (hP _ p.property).pos
  constructor
  · apply (Real.exp_lt_exp.mpr (show G - 1 < Real.log (p : ℕ) by linarith [(abs_lt.mp habs).1])).trans_eq
    exact Real.exp_log hpos
  · rw [← Real.exp_log hpos]
    exact Real.exp_lt_exp.mpr (by linarith [(abs_lt.mp habs).2])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialCellSchedule
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual four-at-a-time compensation cell schedule -/
namespace Ostmann
open scoped Classical

theorem scheduledSmallLength_eq (cs : List ℕ) :
    scheduledSmallLength cs = 6 + 4 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [scheduledSmallLength, List.length_cons, ih]; omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialScheduledPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected original priors in compensation order -/
namespace Ostmann
open scoped Classical

theorem scheduledRegularPrior_prime (cell : ℕ → Finset ℕ) (bulk P : Finset ℕ)
    (top : ℕ) (cs : List ℕ) (n m : ℕ) :
    scheduledRegularPrior (fun j => primeSubsetPrior P (cell j))
      (primeSubsetPrior P bulk) top cs n m =
      fun i => primeSubsetPrior P (scheduledRegularPrimeSets cell bulk top cs n m i) := by
  funext i
  rcases i with ⟨j, i | i⟩ <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledCellSteps
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual selected cell removed by each transfer -/
namespace Ostmann
open scoped Classical

theorem scheduled_drop_length_balance (top : ℕ) (cs : List ℕ) (n : ℕ)
    (hn : n < cs.length) :
    4 + scheduledSmallLength (cs.drop (n + 1)) + 4 * n =
      (initialSmallCellList top cs).length + (initialSmallCellList top cs).length := by
  rw [scheduledSmallLength_eq, List.length_drop, initialSmallCellList_length]
  omega

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledComparisonCutoffs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer cutoffs below the actual spectator band and above all finite frequencies -/
namespace Ostmann
open Filter

theorem eventual_scheduled_comparison_cutoffs (k N p₀ : ℕ) (A : ℕ → ℝ) :
    ∀ᶠ L : ℝ in atTop,
      p₀ ≤ scheduledComparisonCutoff L ∧
      scheduledComparisonCutoff L ≤ scheduledComparisonPrimeLo L ∧
      (scheduledComparisonPrimeLo L : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ∧
      (∀ p : ℕ, Real.exp (Real.exp ((4 / 10000 : ℝ) * L)) ≤ p →
        (p : ℝ) ≤ Real.exp (Real.exp ((6 / 10000 : ℝ) * L)) →
        scheduledComparisonCutoff L ≤ p ∧ p ≤ scheduledComparisonPrimeLo L) ∧
      (∀ n ≤ N, ∀ V : ℕ, (V : ℝ) ≤ Real.exp (A n * spectatorBulkCount k L) →
        V < scheduledComparisonCutoff L ∧ V ≤ scheduledComparisonPrimeLo L) := by
  have hgrow : Tendsto (fun L : ℝ => Real.exp (Real.exp ((2 / 10000 : ℝ) * L))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (Real.tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atTop (by norm_num)))
  filter_upwards [eventual_finite_frequency_band k N A (2 / 10000) (by norm_num),
    eventual_double_exp_integer_margin (2 / 10000) (4 / 10000) (by norm_num) (by norm_num),
    hgrow.eventually (eventually_ge_atTop (p₀ : ℝ)), eventually_gt_atTop (0 : ℝ)]
    with L hfreq hgap hp₀ hL
  have hcpos : 0 < (scheduledComparisonCutoff L : ℝ) := by
    exact_mod_cast (Nat.ceil_pos.mpr (Real.exp_pos _))
  have hc4 : (scheduledComparisonCutoff L : ℝ) ≤
      Real.exp (Real.exp ((4 / 10000 : ℝ) * L)) := by
    dsimp only [scheduledComparisonCutoff]
    linarith
  have h47 : Real.exp (Real.exp ((4 / 10000 : ℝ) * L)) ≤
      Real.exp (Real.exp ((7 / 10000 : ℝ) * L)) :=
    Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith))
  have hcut : scheduledComparisonCutoff L ≤ scheduledComparisonPrimeLo L :=
    Nat.le_floor (hc4.trans h47)
  refine ⟨?_, hcut, ?_, ?_, ?_⟩
  · exact_mod_cast hp₀.trans (Nat.le_ceil _)
  · exact (Nat.floor_le (Real.exp_nonneg _)).trans_lt
      (Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr (by linarith)))
  · intro p hp hpu
    constructor
    · exact_mod_cast hc4.trans hp
    · apply Nat.le_floor
      exact hpu.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith)))
  · intro n hn V hV
    have hv : (V : ℝ) < scheduledComparisonCutoff L :=
      (hV.trans_lt (hfreq n hn)).trans_le (Nat.le_ceil _)
    have hvNat : V < scheduledComparisonCutoff L := by exact_mod_cast hv
    exact ⟨hvNat, hvNat.le.trans hcut⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_MertensPrimeBands
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact published Mertens input for logarithmic prime bands

F. Mertens, J. reine angew. Math. 78 (1874), 46–62, first theorem,
DOI 10.1515/crll.1874.78.46. Both sides of the bounded-error estimate
are needed to subtract the lower cutoff; the collision argument uses
only its previously recorded lower-bound consequence.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem MertensEstimate.lower {C : ℝ} (h : MertensEstimate C) : MertensLowerBound C := by
  intro Q hQ
  have hh := (abs_le.mp (h Q hQ)).1
  linarith

theorem MertensEstimate.upper {C : ℝ} (h : MertensEstimate C) (Q : ℕ) (hQ : 1 ≤ Q) :
    (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p) ≤ Real.log Q + C := by
  have hh := (abs_le.mp (h Q hQ)).2
  linarith

theorem floor_exp_log_bounds (T : ℝ) (hT : 1 ≤ T) :
    1 ≤ ⌊Real.exp T⌋₊ ∧ T - Real.log 2 ≤ Real.log (⌊Real.exp T⌋₊ : ℝ) ∧
      Real.log (⌊Real.exp T⌋₊ : ℝ) ≤ T := by
  have he : 2 ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  have hfloor : (1 : ℕ) ≤ ⌊Real.exp T⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (by linarith)
  have hfp : (0 : ℝ) < ⌊Real.exp T⌋₊ := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hfloor)
  have hhalf : Real.exp T / 2 ≤ (⌊Real.exp T⌋₊ : ℝ) := by
    have := Nat.sub_one_lt_floor (Real.exp T)
    linarith
  have hlo := Real.log_le_log (show 0 < Real.exp T / 2 by positivity) hhalf
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at hlo
  have hhi := Real.log_le_log hfp (Nat.floor_le (Real.exp_nonneg T))
  rw [Real.log_exp] at hhi
  exact ⟨hfloor, hlo, hhi⟩

theorem logPrimeBand_mem {T : ℝ} {p : ℕ} (hp : p ∈ logPrimeBand T) :
    p.Prime ∧ T < Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 2 * T := by
  obtain ⟨hhi, hlo⟩ := Finset.mem_sdiff.mp hp
  have hprime := Nat.prime_of_mem_primesLE hhi
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hlo' : ⌊Real.exp T⌋₊ < p := by
    by_contra hn
    exact hlo (Nat.mem_primesLE.mpr ⟨Nat.le_of_not_gt hn, hprime⟩)
  have hloR : Real.exp T < (p : ℝ) := (Nat.floor_lt (Real.exp_nonneg _)).mp hlo'
  have hhiR : (p : ℝ) ≤ Real.exp (2 * T) :=
    (by exact_mod_cast Nat.le_of_mem_primesLE hhi : (p : ℝ) ≤ ⌊Real.exp (2 * T)⌋₊).trans
      (Nat.floor_le (Real.exp_nonneg _))
  exact ⟨hprime, (Real.lt_log_iff_exp_lt hp0).mpr hloR,
    (Real.log_le_iff_le_exp hp0).mpr hhiR⟩

theorem logPrimeBand_weight_bounds (T C : ℝ) (hT : 1 ≤ T) (hM : MertensEstimate C) :
    T - Real.log 2 - 2 * C ≤ (∑ p ∈ logPrimeBand T, Real.log (p : ℝ) / p) ∧
      (∑ p ∈ logPrimeBand T, Real.log (p : ℝ) / p) ≤ T + Real.log 2 + 2 * C := by
  have hT0 : 0 ≤ T := by linarith
  have hlo := floor_exp_log_bounds T hT
  have hhi := floor_exp_log_bounds (2 * T) (by linarith)
  have hsub : Nat.primesLE ⌊Real.exp T⌋₊ ⊆ Nat.primesLE ⌊Real.exp (2 * T)⌋₊ := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE hp).trans
      (Nat.floor_mono (Real.exp_le_exp.mpr (by linarith))), Nat.prime_of_mem_primesLE hp⟩
  rw [logPrimeBand, Finset.sum_sdiff_eq_sub hsub]
  constructor
  · have h1 := hM.lower _ hhi.1
    have h2 := hM.upper _ hlo.1
    linarith [hhi.2.1, hlo.2.2]
  · have h1 := hM.upper _ hhi.1
    have h2 := hM.lower _ hlo.1
    linarith [hhi.2.2, hlo.2.1]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WholeShellLinearMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear harmonic mass in the full original bulk shell -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem logPrimeBand_mass_quarter {C : ℝ} (hM : MertensEstimate C)
    (u : ℝ) (hu : 1 ≤ u) (he : 2 * (Real.log 2 + 2 * C) ≤ u) :
    (1 / 4 : ℝ) ≤ ∑ p ∈ logPrimeBand u, (p : ℝ)⁻¹ := by
  have hw := (logPrimeBand_weight_bounds u C hu hM).1
  have hb : (∑ p ∈ logPrimeBand u, Real.log (p : ℝ) / p) ≤
      (2 * u) * ∑ p ∈ logPrimeBand u, (p : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right (logPrimeBand_mem hp).2.2 (by positivity : 0 ≤ (p : ℝ)⁻¹)
  nlinarith

theorem whole_shell_geometric_mass {C : ℝ} (hM : MertensEstimate C)
    (u v : ℝ) (hu : 1 ≤ u) (he : 2 * (Real.log 2 + 2 * C) ≤ u)
    (N : ℕ) (hN : (2 : ℝ) ^ N * u ≤ v) :
    (N : ℝ) / 4 ≤ ∑ p ∈ primeLogCellSet 1 0 u v, (p : ℝ)⁻¹ := by
  let B := fun i : Fin N => logPrimeBand ((2 : ℝ) ^ i.val * u)
  have hpow (i : ℕ) : u ≤ (2 : ℝ) ^ i * u :=
    le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
  have hband (i : Fin N) : (1 / 4 : ℝ) ≤ ∑ p ∈ B i, (p : ℝ)⁻¹ :=
    logPrimeBand_mass_quarter hM _ (hu.trans (hpow _)) (he.trans (hpow _))
  have hdisj (i j : Fin N) (hij : i.val < j.val) : Disjoint (B i) (B j) := by
    apply Finset.disjoint_left.mpr
    intro p hi hj
    have hip := (logPrimeBand_mem hi).2.2
    have hjp := (logPrimeBand_mem hj).2.1
    have hp := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.succ_le_of_lt hij)) (by linarith : 0 ≤ u)
    rw [pow_succ] at hp
    nlinarith
  have hpair : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin N))) B := by
    intro i _ j _ hij
    rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun h => hij (Fin.ext h)) with h | h
    · exact hdisj i j h
    · exact (hdisj j i h).symm
  have hsub : (Finset.univ.biUnion B) ⊆ primeLogCellSet 1 0 u v := by
    intro p hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hprime, hlo, hhi⟩ := logPrimeBand_mem hi
    apply mem_primeLogCellSet_iff.mpr
    refine ⟨hprime, by simp only [Nat.modEq_one], (hpow i.val).trans_lt hlo, ?_⟩
    have hp := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.succ_le_of_lt i.isLt)) (by linarith : 0 ≤ u)
    rw [pow_succ] at hp
    exact hhi.trans ((by nlinarith : 2 * ((2 : ℝ) ^ i.val * u) ≤ (2 : ℝ) ^ N * u).trans hN)
  calc
    (N : ℝ) / 4 = ∑ _i : Fin N, (1 / 4 : ℝ) := by simp; ring
    _ ≤ ∑ i : Fin N, ∑ p ∈ B i, (p : ℝ)⁻¹ := Finset.sum_le_sum (fun i _ => hband i)
    _ = ∑ p ∈ Finset.univ.biUnion B, (p : ℝ)⁻¹ := (Finset.sum_biUnion hpair).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

theorem whole_shell_linear_mass {C : ℝ} (hM : MertensEstimate C) :
    ∀ᶠ L : ℝ in atTop, L / 8000 ≤
      ∑ p ∈ primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L)), (p : ℝ)⁻¹ := by
  have ht := (Real.tendsto_exp_atTop.comp
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 4 / 1000))).eventually
      (eventually_ge_atTop (2 * (Real.log 2 + 2 * C)))
  filter_upwards [ht, eventually_ge_atTop (2000 : ℝ)] with L hlarge hL
  let N : ℕ := ⌊L / 1000⌋₊
  have hL0 : 0 ≤ L := by linarith
  have hNu : (N : ℝ) ≤ L / 1000 := Nat.floor_le (by positivity)
  have hNl : L / 1000 - 1 < (N : ℝ) := Nat.sub_one_lt_floor _
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hp : (2 : ℝ) ^ N = Real.exp ((N : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hN : (2 : ℝ) ^ N * Real.exp ((4 / 1000 : ℝ) * L) ≤
      Real.exp ((6 / 1000 : ℝ) * L) := by
    rw [hp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hn := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg N (α := ℝ))
    nlinarith
  have hmass := whole_shell_geometric_mass hM
    (Real.exp ((4 / 1000 : ℝ) * L)) (Real.exp ((6 / 1000 : ℝ) * L))
    (Real.one_le_exp (by positivity)) hlarge N hN
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WholeShellRetainedLinearMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear bulk mass after every allowed finite deletion -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem whole_shell_retained_linear_mass {C : ℝ} (hM : MertensEstimate C)
    (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop, ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp (K * L) →
      L / 16000 ≤ ∑ p ∈ primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L)) \ D, (p : ℝ)⁻¹ := by
  filter_upwards [whole_shell_linear_mass hM,
    arithmetic_exponent_absorption 0 (4 / 1000) 0 K 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (16000 : ℝ)] with L hmass hrate hL
  intro D hD
  let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
    (Real.exp ((6 / 1000 : ℝ) * L))
  have hL0 : 0 ≤ L := by linarith
  have hlo : ∀ p ∈ S, Real.exp (Real.exp ((4 / 1000 : ℝ) * L)) ≤ (p : ℝ) := by
    intro p hp
    obtain ⟨hp, _, hlo, _⟩ := mem_primeLogCellSet_iff.mp hp
    exact ((Real.lt_log_iff_exp_lt (by exact_mod_cast hp.pos)).mp hlo).le
  have hdel : (∑ p ∈ S ∩ D, (p : ℝ)⁻¹) ≤ 1 := by
    apply (bulk_deleted_reciprocal_mass_le S D _ hlo).trans
    apply (mul_le_mul_of_nonneg_right hD (Real.exp_nonneg _)).trans
    rw [← Real.exp_add]
    apply (Real.exp_le_exp.mpr (show K * L + -Real.exp ((4 / 1000 : ℝ) * L) ≤ 0 from ?_)).trans_eq
    · exact Real.exp_zero
    · simp only [zero_mul, Real.exp_zero, mul_one, one_mul, pow_one] at hrate
      nlinarith [mul_nonneg hK hL0]
  have hs := Finset.sum_inter_add_sum_sdiff S D (fun p : ℕ => (p : ℝ)⁻¹)
  change L / 16000 ≤ ∑ p ∈ S \ D, (p : ℝ)⁻¹
  change L / 8000 ≤ ∑ p ∈ S, (p : ℝ)⁻¹ at hmass
  linarith

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

theorem FrozenInitialSpectatorData.comparison_upper {A : Set ℕ} {N d cutoff : ℕ}
    {p : Fin (d + d) → ℕ} {L ε : ℝ} {D : Finset ℕ}
    (F : FrozenInitialSpectatorData A N p L ε cutoff D) (hL : 0 ≤ L) (i) :
    (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L)) :=
  (F.upper i).trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by nlinarith only [hL])))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledComparisonCounts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complexity of the actual bounded cell schedule and spectator list -/
namespace Ostmann
open Filter

theorem scheduled_comparison_count (k n r m : ℕ) (hn : n ≤ k) (hr : r ≤ 10 + 4 * k)
    (D : Finset ℕ) (outside : List ℕ) (hD : D.card ≤ 2) (hout : outside.length ≤ m) :
    D.card + (Fintype.card (MovingRegularSlot n r m) + 4 * n * 2 ^ n) + outside.length ≤
      scheduledComparisonCount k m := by
  have hp : 2 ^ n ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hn
  have hslot := Nat.mul_le_mul hp (Nat.add_le_add_right hr m)
  have hi := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hn) hp
  rw [movingRegularSlot_card]
  unfold scheduledComparisonCount
  omega

theorem eventual_scheduled_comparison_count (k : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      (scheduledComparisonCount k (spectatorBulkCount k L) : ℝ) ≤ Real.exp (3 * L) := by
  let X : ℝ := 2 + (2 : ℝ) ^ k * (10 + 4 * k) + 4 * k * (2 : ℝ) ^ k
  let Y : ℝ := (2 : ℝ) ^ k + 1
  let C := X + Y * (k : ℝ) ^ 4
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hY : 0 ≤ Y := by dsimp only [Y]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  filter_upwards [arithmetic_exponent_absorption 0 3 0 C 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hbound hL
  have hm := spectatorBulkCount_upper k L (by linarith)
  have hn : (scheduledComparisonCount k (spectatorBulkCount k L) : ℝ) =
      X + Y * spectatorBulkCount k L := by
    simp only [scheduledComparisonCount, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    dsimp only [X, Y]
    ring
  have hCL : C * L ≤ Real.exp (3 * L) := by
    simp only [pow_zero, zero_mul, Real.exp_zero, mul_one, one_mul] at hbound
    linarith
  rw [hn]
  apply le_trans _ hCL
  calc
    _ ≤ X * L + Y * ((k : ℝ) ^ 4 * L) :=
      add_le_add (le_mul_of_one_le_right hX hL) (mul_le_mul_of_nonneg_left hm hY)
    _ = _ := by dsimp only [C]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledDiagonalLengths
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The deterministic small-slot counts in the finite diagonal family -/
namespace Ostmann

theorem scheduledTailLength_eq (cs : List ℕ) (k n : ℕ) (hlen : cs.length = k) :
    scheduledSmallLength (cs.drop (n + 1)) = scheduledTailLength k n := by
  rw [scheduledSmallLength_eq, List.length_drop, hlen]
  rfl

theorem scheduledTailLength_budget (k n : ℕ) (hn : n < k) (K : ℝ) (hK : 0 ≤ K)
    (hdepth : 40 * (K + 1) ≤ (k : ℝ) ^ 3) :
    4 * (K + 1) * scheduledTailLength k n ≤ (k : ℝ) ^ 4 := by
  have hk : 1 ≤ k := by omega
  have hr : scheduledTailLength k n ≤ 10 * k := by
    unfold scheduledTailLength
    omega
  have hkr : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hrr : (scheduledTailLength k n : ℝ) ≤ 10 * k := by exact_mod_cast hr
  have hh := mul_le_mul_of_nonneg_right hdepth (show 0 ≤ (k : ℝ) by positivity)
  have hb := mul_le_mul_of_nonneg_left hrr (show 0 ≤ 4 * (K + 1) by linarith)
  nlinarith only [hh, hb]

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

theorem scheduledPageDeletions_giant (P : PublishedProgressionInput) (L : ℝ) (cutoff : ℕ)
    (z : PrimitiveRealZero) (hz : selectedPageZero P (giantProgressionCutoff L) = some z)
    (p : ℕ) (hp : deletedConductorPrime z.modulus cutoff = some p) :
    p ∈ scheduledPageDeletions P L cutoff := by
  apply Finset.mem_union_left
  simp [pageDeletionPrimes, hz, hp]

theorem scheduledPageDeletions_bulk (P : PublishedProgressionInput) (L : ℝ) (cutoff : ℕ)
    (z : PrimitiveRealZero) (hz : selectedPageZero P (bulkProgressionCutoff L) = some z)
    (p : ℕ) (hp : deletedConductorPrime z.modulus cutoff = some p) :
    p ∈ scheduledPageDeletions P L cutoff := by
  apply Finset.mem_union_right
  simp [pageDeletionPrimes, hz, hp]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CompletedCompensationPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A total prior extending precisely the used compensation cells

Unused indices reuse the selected top cell. The pivot exponent retains its
original zero default beyond the finite list; no extra transfer is performed.
-/
namespace Ostmann
open scoped Classical BigOperators

theorem completedCompensationCell_used (top : ℕ) (cs : List ℕ) (n : ℕ)
    (hn : n < cs.length) : completedCompensationCell top cs n = (cs.drop n).headD 0 := by
  unfold completedCompensationCell
  rw [list_headD_drop_get cs top n hn, list_headD_drop_get cs 0 n hn]

theorem completedCompensationCell_selected
    {A B : Set ℕ} {N hi top : ℕ} {a C L X target : ℝ} {D : Finset ℕ}
    {cs : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L X hi D target top)
    (hcs : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) cs targets)
    (n : ℕ) :
    ∃ t, SelectedSmallTailCell A B N a C L X hi D t (completedCompensationCell top cs n) := by
  by_cases hn : n < cs.length
  · refine ⟨(targets.drop n).headD 0 / 4, ?_⟩
    rw [completedCompensationCell_used top cs n hn]
    exact forall₂_headD_drop hcs n hn
  · refine ⟨target, ?_⟩
    simpa only [completedCompensationCell, List.drop_eq_nil_of_le (Nat.le_of_not_gt hn),
      List.headD_nil] using htop

theorem completedCompensationPrior_data
    {A B : Set ℕ} {N hi top : ℕ} {a C L X target : ℝ} {D : Finset ℕ}
    {cs : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L X hi D target top)
    (hcs : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) cs targets)
    (P : Finset ℕ) (hP : initialRegularPrimeRange L ⊆ P) (n : ℕ) :
    let Q := completedCompensationSets A B N X hi D top cs n
    Q ⊆ P ∧ Real.exp (-(2 * L)) ≤ ∑ p ∈ Q, (p : ℝ)⁻¹ ∧
      (∑ p : P, completedCompensationPrior A B N X hi D P top cs n p) = 1 ∧
      (∀ p : P, 0 ≤ completedCompensationPrior A B N X hi D P top cs n p ∧
        (p : ℝ) * completedCompensationPrior A B N X hi D P top cs n p ≤ Real.exp (2 * L)) := by
  intro Q
  obtain ⟨t, ht⟩ := completedCompensationCell_selected htop hcs n
  have hQP := ht.subset_initialRegularPrimeRange.trans hP
  have hd := ht.prior_data P hQP
  exact ⟨hQP, ht.2.2.2.1, hd.1, hd.2.1⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledPrimeRanges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Live prime ranges of the selected finite schedule -/
namespace Ostmann
open scoped Classical

theorem scheduledSmallCell_property (P : ℕ → Prop) (top : ℕ) (cs : List ℕ)
    (htop : P top) (hcs : ∀ c ∈ cs, P c) :
    ∀ i, P (scheduledSmallCell top cs i) := by
  induction cs with
  | nil => exact fun _ => htop
  | cons c cs ih =>
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [scheduledSmallCell, Fin.append_left] using hcs c (by simp)
    · simpa only [scheduledSmallCell, Fin.append_right] using
        ih (fun d hd => hcs d (by simp [hd])) j

theorem mem_initialSmallCellList_of_eq_or_mem (top : ℕ) (cs : List ℕ) (j : ℕ)
    (h : j = top ∨ j ∈ cs) : j ∈ initialSmallCellList top cs := by
  rcases h with rfl | hj
  · simp [initialSmallCellList]
  · simp only [initialSmallCellList, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨j, hj, by simp⟩

theorem completedCompensationCell_mem_initial (top : ℕ) (cs : List ℕ) (n : ℕ) :
    completedCompensationCell top cs n ∈ initialSmallCellList top cs := by
  apply mem_initialSmallCellList_of_eq_or_mem
  by_cases hn : n < cs.length
  · right
    rw [completedCompensationCell_used top cs n hn, list_headD_drop_get cs 0 n hn]
    exact List.get_mem _ _
  · left
    simp only [completedCompensationCell, List.drop_eq_nil_of_le (Nat.le_of_not_gt hn),
      List.headD_nil]

theorem scheduledSmallCell_mem_initial (top : ℕ) (cs : List ℕ) (j : ℕ)
    (i : Fin (scheduledSmallLength (cs.drop j))) :
    scheduledSmallCell top (cs.drop j) i ∈ initialSmallCellList top cs := by
  apply scheduledSmallCell_property
  · exact mem_initialSmallCellList_of_eq_or_mem top cs top (Or.inl rfl)
  · intro c hc
    exact mem_initialSmallCellList_of_eq_or_mem top cs c
      (Or.inr (List.mem_of_mem_drop hc))

theorem selected_cell_prime_range
    {A B : Set ℕ} {N hi j : ℕ} {a C L X target : ℝ} {D : Finset ℕ}
    (h : SelectedSmallTailCell A B N a C L X hi D target j)
    (hindex : Real.exp ((1 / 100 : ℝ) * L) ≤ (j : ℝ))
    (p : ℕ) (hp : p ∈ selectedTailCellPrimes A B N X hi D j) :
    p ∈ initialRegularPrimeRange L ∧
      Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (p : ℝ) := by
  refine ⟨h.subset_initialRegularPrimeRange hp, ?_⟩
  exact (Real.exp_le_exp.mpr hindex).trans (h.2.2.2.2.2.2 p hp).2.1.le

theorem completedCompensationSets_range
    {A B : Set ℕ} {N hi top : ℕ} {a C L X target : ℝ} {D : Finset ℕ}
    {cs : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L X hi D target top)
    (hcs : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) cs targets)
    (hlower : ∀ j ∈ initialSmallCellList top cs, Real.exp ((1 / 100 : ℝ) * L) ≤ (j : ℝ))
    (n p : ℕ) (hp : p ∈ completedCompensationSets A B N X hi D top cs n) :
    p ∈ initialRegularPrimeRange L ∧
      Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (p : ℝ) := by
  obtain ⟨t, ht⟩ := completedCompensationCell_selected htop hcs n
  exact selected_cell_prime_range ht
    (hlower _ (completedCompensationCell_mem_initial top cs n)) p hp

theorem scheduledRegularPrimeSets_range
    {A B : Set ℕ} {N hi top : ℕ} {a C L X target : ℝ} {D Qb : Finset ℕ}
    {cs : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L X hi D target top)
    (hcs : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) cs targets)
    (hL : 0 ≤ L)
    (hlower : ∀ j ∈ initialSmallCellList top cs, Real.exp ((1 / 100 : ℝ) * L) ≤ (j : ℝ))
    (hbulk : Qb ⊆ initialRegularPrimeRange L)
    (hbulklower : ∀ p ∈ Qb, Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (p : ℝ))
    (n m j : ℕ) (i : MovingRegularSlot n (scheduledSmallLength (cs.drop j)) m)
    (p : ℕ) (hp : p ∈ scheduledRegularPrimeSets
      (selectedTailCellPrimes A B N X hi D) Qb top (cs.drop j) n m i) :
    p ∈ initialRegularPrimeRange L ∧
      Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (p : ℝ) := by
  rcases i with ⟨u, i | i⟩
  · have hm := scheduledSmallCell_mem_initial top cs j i
    obtain ⟨t, ht⟩ := initial_selected_cells_valid htop hcs _ hm
    obtain ⟨hmem, hlow⟩ := selected_cell_prime_range ht (hlower _ hm) p hp
    refine ⟨hmem, (le_trans ?_ hlow)⟩
    apply Real.exp_le_exp.mpr
    apply Real.exp_le_exp.mpr
    nlinarith only [hL]
  · exact ⟨hbulk hp, hbulklower p hp⟩

theorem scheduledSmallLower_prime_bound (A B : Set ℕ) (N hi top : ℕ)
    (X : ℝ) (D Qb : Finset ℕ) (cs : List ℕ) (n m : ℕ)
    (i : TreeLeafIndex n × Fin (scheduledSmallLength cs)) (p : ℕ)
    (hp : p ∈ scheduledRegularPrimeSets
      (selectedTailCellPrimes A B N X hi D) Qb top cs n m (i.1, .inl i.2)) :
    Real.exp (scheduledSmallLower top cs n i) ≤ (p : ℝ) := by
  have hmem := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hp).1).1
  obtain ⟨hprime, _, hlo, _⟩ := mem_primeLogCellSet_iff.mp hmem
  apply (Real.le_log_iff_exp_le (by exact_mod_cast hprime.pos)).mp
  dsimp only [scheduledSmallLower]
  linarith

theorem scheduledRegularPrimeSets_sub_mass
    {A B : Set ℕ} {N hi top : ℕ} {a C L X target : ℝ} {D Qb : Finset ℕ}
    {cs : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L X hi D target top)
    (hcs : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) cs targets)
    (P : Finset ℕ) (hP : initialRegularPrimeRange L ⊆ P) (hbulk : Qb ⊆ P)
    (hmass : Real.exp (-(2 * L)) ≤ ∑ p ∈ Qb, (p : ℝ)⁻¹)
    (n m j : ℕ) (i : MovingRegularSlot n (scheduledSmallLength (cs.drop j)) m) :
    let Q := scheduledRegularPrimeSets (selectedTailCellPrimes A B N X hi D)
      Qb top (cs.drop j) n m i
    Q ⊆ P ∧ Real.exp (-(2 * L)) ≤ ∑ p ∈ Q, (p : ℝ)⁻¹ := by
  intro Q
  rcases i with ⟨u, i | i⟩
  · have hm := scheduledSmallCell_mem_initial top cs j i
    obtain ⟨t, ht⟩ := initial_selected_cells_valid htop hcs _ hm
    exact ⟨ht.subset_initialRegularPrimeRange.trans hP, ht.2.2.2.1⟩
  · exact ⟨hbulk, hmass⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledPageAvoidance
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Classical

theorem selectedTailCellPrimes_avoids (A B : Set ℕ) (N hi : ℕ) (Y : ℝ)
    (D : Finset ℕ) (j p : ℕ) (hp : p ∈ D) :
    p ∉ selectedTailCellPrimes A B N Y hi D j := by
  intro h
  exact (Finset.mem_sdiff.mp h).2 hp

theorem completedCompensationSets_avoids (A B : Set ℕ) (N hi : ℕ) (Y : ℝ)
    (D : Finset ℕ) (top : ℕ) (cs : List ℕ) (p : ℕ) (hp : p ∈ D) (n : ℕ) :
    p ∉ completedCompensationSets A B N Y hi D top cs n :=
  selectedTailCellPrimes_avoids A B N hi Y D _ p hp

theorem scheduledRegularPrimeSets_avoids (A B : Set ℕ) (N hi : ℕ) (Y : ℝ)
    (D bulk : Finset ℕ) (hbulk : Disjoint bulk D) (top : ℕ) (cs : List ℕ)
    (n m p : ℕ) (hp : p ∈ D) (i : MovingRegularSlot n (scheduledSmallLength cs) m) :
    p ∉ scheduledRegularPrimeSets (selectedTailCellPrimes A B N Y hi D) bulk top cs n m i := by
  rcases i with ⟨u, i | i⟩
  · exact selectedTailCellPrimes_avoids A B N hi Y D _ p hp
  · exact fun h => Finset.disjoint_left.mp hbulk h hp

theorem selected_schedule_avoids_giant_page
    (P : PublishedProgressionInput) (A B : Set ℕ) (N hi : ℕ) (Y L : ℝ)
    (cutoff top : ℕ) (cs : List ℕ) (bulk : Finset ℕ)
    (hbulk : Disjoint bulk (scheduledPageDeletions P L cutoff))
    (z : PrimitiveRealZero) (hz : selectedPageZero P (giantProgressionCutoff L) = some z)
    (p : ℕ) (hp : deletedConductorPrime z.modulus cutoff = some p) :
    (∀ n, p ∉ completedCompensationSets A B N Y hi
      (scheduledPageDeletions P L cutoff) top cs n) ∧
    (∀ n m offset i, p ∉ scheduledRegularPrimeSets
      (selectedTailCellPrimes A B N Y hi (scheduledPageDeletions P L cutoff))
      bulk top (cs.drop offset) n m i) := by
  have hd := scheduledPageDeletions_giant P L cutoff z hz p hp
  exact ⟨completedCompensationSets_avoids A B N hi Y _ top cs p hd,
    fun n m offset i => scheduledRegularPrimeSets_avoids A B N hi Y _ bulk
      hbulk top (cs.drop offset) n m p hd i⟩

theorem FrozenInitialSpectatorData.avoids_giant_page
    {P : PublishedProgressionInput} {A : Set ℕ} {N d cutoff c₀ : ℕ}
    {p : Fin (d + d) → ℕ} {L ε : ℝ}
    (F : FrozenInitialSpectatorData A N p L ε c₀ (scheduledPageDeletions P L cutoff))
    (z : PrimitiveRealZero) (hz : selectedPageZero P (giantProgressionCutoff L) = some z)
    (q : ℕ) (hq : deletedConductorPrime z.modulus cutoff = some q) (i) : p i ≠ q := by
  intro h
  exact F.avoids i (h ▸ scheduledPageDeletions_giant P L cutoff z hz q hq)

theorem FrozenInitialSpectatorData.avoids_bulk_page
    {P : PublishedProgressionInput} {A : Set ℕ} {N d cutoff c₀ : ℕ}
    {p : Fin (d + d) → ℕ} {L ε : ℝ}
    (F : FrozenInitialSpectatorData A N p L ε c₀ (scheduledPageDeletions P L cutoff))
    (z : PrimitiveRealZero) (hz : selectedPageZero P (bulkProgressionCutoff L) = some z)
    (q : ℕ) (hq : deletedConductorPrime z.modulus cutoff = some q) (i) : p i ≠ q := by
  intro h
  exact F.avoids i (h ▸ scheduledPageDeletions_bulk P L cutoff z hz q hq)

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

theorem initialRegularPrimeRange_upper (L : ℝ) (p : ℕ)
    (hp : p ∈ initialRegularPrimeRange L) :
    (p : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L)) := by
  have h := (Nat.mem_primesLE.mp hp).1
  have h' : (p : ℝ) ≤ ⌊Real.exp (Real.exp ((11 / 1000 : ℝ) * L))⌋₊ := by
    exact_mod_cast h
  exact h'.trans (Nat.floor_le (Real.exp_nonneg _))

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

theorem eventual_selected_bulk_mass {C : ℝ} (hM : MertensEstimate C) :
    ∀ᶠ L : ℝ in atTop, ∀ D : Finset ℕ, D.card ≤ 2 →
      1 / Real.exp (2 * L) ≤
        ∑ p ∈ primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
          (Real.exp ((6 / 1000 : ℝ) * L)) \ D, (p : ℝ)⁻¹ := by
  filter_upwards [whole_shell_retained_linear_mass hM 1 (by norm_num),
    eventually_ge_atTop (16000 : ℝ)] with L hmass hL D hD
  have hcard : (D.card : ℝ) ≤ Real.exp (1 * L) := by
    rw [one_mul]
    have hd : (D.card : ℝ) ≤ 2 := by exact_mod_cast hD
    have he := Real.add_one_le_exp L
    nlinarith only [hd, he, hL]
  apply le_trans _ (hmass D hcard)
  have he : Real.exp (-(2 * L)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [one_div, ← Real.exp_neg]
  linarith

theorem selected_schedule_prime_data
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y target : ℝ} {D Qb : Finset ℕ}
    {cs : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y hi D target top)
    (hcs : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) cs targets)
    (hL : 0 ≤ L)
    (hlower : ∀ j ∈ initialSmallCellList top cs, Real.exp ((1 / 100 : ℝ) * L) ≤ (j : ℝ))
    (hbulk : Qb ⊆ initialRegularPrimeRange L)
    (hbulklower : ∀ p ∈ Qb, Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (p : ℝ))
    (hbulkmass : 1 / Real.exp (2 * L) ≤ ∑ p ∈ Qb, (p : ℝ)⁻¹) :
    (∀ j, completedCompensationSets A B N Y hi D top cs j ⊆ initialRegularPrimeRange L ∧
      1 / Real.exp (2 * L) ≤ ∑ p ∈ completedCompensationSets A B N Y hi D top cs j, (p : ℝ)⁻¹) ∧
    (∀ j p, p ∈ completedCompensationSets A B N Y hi D top cs j →
      Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (p : ℝ)) ∧
    (∀ n m offset (i : MovingRegularSlot n (scheduledSmallLength (cs.drop offset)) m),
      let Q := scheduledRegularPrimeSets (selectedTailCellPrimes A B N Y hi D)
        Qb top (cs.drop offset) n m i
      Q ⊆ initialRegularPrimeRange L ∧
      1 / Real.exp (2 * L) ≤ ∑ p ∈ Q, (p : ℝ)⁻¹) ∧
    (∀ n m offset (i : MovingRegularSlot n (scheduledSmallLength (cs.drop offset)) m),
      ∀ p, p ∈ scheduledRegularPrimeSets (selectedTailCellPrimes A B N Y hi D)
        Qb top (cs.drop offset) n m i →
        Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (p : ℝ)) := by
  have he : 1 / Real.exp (2 * L) = Real.exp (-(2 * L)) := by
    rw [one_div, Real.exp_neg]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    have hd := completedCompensationPrior_data htop hcs (initialRegularPrimeRange L)
      (fun _ h => h) j
    exact ⟨hd.1, he ▸ hd.2.1⟩
  · intro j p hp
    exact (completedCompensationSets_range htop hcs hlower j p hp).2
  · intro n m offset i
    have hd := scheduledRegularPrimeSets_sub_mass htop hcs (initialRegularPrimeRange L)
      (fun _ h => h) hbulk (he ▸ hbulkmass) n m offset i
    exact ⟨hd.1, he ▸ hd.2⟩
  · intro n m offset i p hp
    exact (scheduledRegularPrimeSets_range htop hcs hL hlower hbulk hbulklower
      n m offset i p hp).2

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

theorem scheduled_giant_regular_separation (L G : ℝ) (hL : 0 < L)
    (hG : Real.exp ((49 / 1000 : ℝ) * L) ≤ G - 1)
    (p : smoothGiantPrimeRange G)
    (hp : smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G p ≠ 0)
    (q : ℕ) (hq : q ∈ initialRegularPrimeRange L) : (p : ℕ) ≠ q := by
  have hlo := (smoothGiantPrior_active_bounds (smoothGiantPrimeRange G)
    (smoothGiantPrimeRange_prime G) logCellProfile G
    logCellProfile_zero_outside p hp).1
  have hu := initialRegularPrimeRange_upper L q hq
  have hsmall : Real.exp ((11 / 1000 : ℝ) * L) < G - 1 :=
    (Real.exp_lt_exp.mpr (by linarith)).trans_le hG
  have hq' : (q : ℝ) < (p : ℝ) :=
    hu.trans_lt ((Real.exp_lt_exp.mpr hsmall).trans hlo)
  intro heq
  exact (ne_of_lt hq') (by exact_mod_cast heq.symm)

theorem completedCompensationSets_upper_used (A B : Set ℕ) (N hi : ℕ) (Y : ℝ)
    (D : Finset ℕ) (top : ℕ) (cs : List ℕ) (n : ℕ) (hn : n < cs.length)
    (p : ℕ) (hp : p ∈ completedCompensationSets A B N Y hi D top cs n) :
    (p : ℝ) ≤ Real.exp (((cs.drop n).headD 0 : ℝ) + 1) := by
  unfold completedCompensationSets at hp
  rw [completedCompensationCell_used top cs n hn] at hp
  obtain ⟨hpp, _, _, hhi⟩ :=
    mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hp).1).1
  exact (Real.log_le_iff_le_exp (by exact_mod_cast hpp.pos)).mp hhi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedCellTiers
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite tier labels for the actual disjoint compensation cells -/
namespace Ostmann
open scoped Classical

theorem selected_centers_pairwise_separated
    {A B : Set ℕ} {N hi : ℕ} {a C L X J : ℝ} {D : Finset ℕ}
    {cs : List ℕ} {ws : List ℝ}
    (hcs : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) cs ws)
    (hw : ws.Pairwise (fun x y => y + J / 4 ≤ x))
    (hJ : 16 * (64 * tailDefectBudget a C X + 2) ≤ J) :
    cs.Pairwise (fun x y => y + 1 ≤ x) := by
  apply List.pairwise_iff_get.mpr
  intro i j hij
  have hi : (i : ℕ) < ws.length := by rw [← hcs.length_eq]; exact i.isLt
  have hj : (j : ℕ) < ws.length := by rw [← hcs.length_eq]; exact j.isLt
  have hci := hcs.get i.isLt hi
  have hcj := hcs.get j.isLt hj
  have ht := hw.rel_get_of_lt (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) hij
  have hs := compensation_cell_separation J (64 * tailDefectBudget a C X + 1)
    (ws.get ⟨i, hi⟩) (ws.get ⟨j, hj⟩) (cs.get i) (cs.get j)
    ht (by linarith) hci.1 (by simpa only [add_assoc] using hcj.2.1)
  exact_mod_cast hs

theorem selectedTailCellPrimes_disjoint_of_gap (A B : Set ℕ) (N hi : ℕ)
    (X : ℝ) (D : Finset ℕ) (i j : ℕ) (h : j + 1 ≤ i) :
    Disjoint (selectedTailCellPrimes A B N X hi D i)
      (selectedTailCellPrimes A B N X hi D j) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hi := mem_primeLogCellSet_iff.mp
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hp).1).1
  have hj := mem_primeLogCellSet_iff.mp
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hq).1).1
  have hcast : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
  linarith [hi.2.2.1, hj.2.2.2]

theorem selected_cells_pairwiseDisjoint (A B : Set ℕ) (N hi : ℕ)
    (X : ℝ) (D : Finset ℕ) (cs : List ℕ)
    (h : cs.Pairwise (fun x y => y + 1 ≤ x)) :
    Pairwise (fun i j : Fin cs.length =>
      Disjoint (selectedTailCellPrimes A B N X hi D (cs.get i))
        (selectedTailCellPrimes A B N X hi D (cs.get j))) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact selectedTailCellPrimes_disjoint_of_gap A B N hi X D _ _ (h.rel_get_of_lt hij)
  · exact (selectedTailCellPrimes_disjoint_of_gap A B N hi X D _ _
      (h.rel_get_of_lt hij)).symm

theorem finitePrimeCellTier_of_mem {k : ℕ} (Q : Fin k → Finset ℕ)
    (hQ : Pairwise (fun i j => Disjoint (Q i) (Q j)))
    (fallback : ℕ) (i : Fin k) (p : ℕ) (hp : p ∈ Q i) :
    finitePrimeCellTier Q fallback p = i := by
  have hex : ∃ i, p ∈ Q i := ⟨i, hp⟩
  rw [finitePrimeCellTier, dite_eq_left hex]
  have he : Classical.choose hex = i := by
    by_contra hne
    exact (Finset.disjoint_left.mp (hQ hne)) (Classical.choose_spec hex) hp
  exact congrArg Fin.val he

theorem finitePrimeCellTier_outside {k : ℕ} (Q : Fin k → Finset ℕ)
    (fallback p : ℕ) (hp : ∀ i, p ∉ Q i) :
    finitePrimeCellTier Q fallback p = fallback := by
  rw [finitePrimeCellTier, dite_eq_right]
  rintro ⟨i, hi⟩
  exact hp i hi

theorem selected_top_compensation_gap
    {A B : Set ℕ} {N hi top j : ℕ} {a C L X J cb w : ℝ} {D : Finset ℕ}
    (htop : SelectedSmallTailCell A B N a C L X hi D ((J - 2 * cb) / 6) top)
    (hj : SelectedSmallTailCell A B N a C L X hi D (w / 4) j)
    (hcb : 0 ≤ cb) (hw : 3 * J / 4 ≤ w)
    (hJ : 48 * (64 * tailDefectBudget a C X + 2) ≤ J) : top + 1 ≤ j := by
  have ht := htop.2.1
  have hc := hj.1
  have he : (top : ℝ) + 1 ≤ j := by linarith
  exact_mod_cast he

theorem finitePrimeCellTier_rest {k : ℕ} (Q : Fin k → Finset ℕ) (R : Finset ℕ)
    (hR : ∀ i, Disjoint R (Q i)) (p : ℕ) (hp : p ∈ R) :
    finitePrimeCellTier Q k p = k := by
  apply finitePrimeCellTier_outside
  intro i hpi
  exact (Finset.disjoint_left.mp (hR i)) hp hpi

theorem exists_selected_prime_tiers (A B : Set ℕ) (N hi : ℕ) (X : ℝ)
    (D R : Finset ℕ) (cs : List ℕ)
    (hcs : cs.Pairwise (fun x y => y + 1 ≤ x))
    (hR : ∀ i : Fin cs.length,
      Disjoint R (selectedTailCellPrimes A B N X hi D (cs.get i))) :
    ∃ tier : ℕ → ℕ,
      (∀ i : Fin cs.length, ∀ p ∈ selectedTailCellPrimes A B N X hi D (cs.get i),
        tier p = i) ∧ (∀ p ∈ R, tier p = cs.length) := by
  let Q := fun i : Fin cs.length => selectedTailCellPrimes A B N X hi D (cs.get i)
  refine ⟨finitePrimeCellTier Q cs.length, ?_, ?_⟩
  · exact finitePrimeCellTier_of_mem Q (selected_cells_pairwiseDisjoint A B N hi X D cs hcs)
      cs.length
  · exact finitePrimeCellTier_rest Q R hR

theorem mem_drop_index {A : Type} (cs : List A) (n : ℕ) (c : A) (hc : c ∈ cs.drop n) :
    ∃ i : Fin cs.length, n ≤ i ∧ cs.get i = c := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hc
  have hij : n + j.val < cs.length := by
    have h := j.isLt
    simp only [List.length_drop] at h
    omega
  refine ⟨⟨n + j.val, hij⟩, by simp, ?_⟩
  simpa only [List.get_eq_getElem, List.getElem_drop, Nat.add_comm] using hj

theorem exists_scheduled_prime_tiers (A B : Set ℕ) (N hi : ℕ) (X : ℝ)
    (D Qb : Finset ℕ) (top : ℕ) (cs : List ℕ) (tier : ℕ → ℕ)
    (hcomp : ∀ i : Fin cs.length,
      ∀ p ∈ selectedTailCellPrimes A B N X hi D (cs.get i), tier p = i)
    (htop : ∀ p ∈ selectedTailCellPrimes A B N X hi D top, tier p = cs.length)
    (hbulk : ∀ p ∈ Qb, tier p = cs.length) (n m offset : ℕ) (hoffset : offset ≤ cs.length) :
    ∃ tierB : MovingRegularSlot n (scheduledSmallLength (cs.drop offset)) m → ℕ,
      (∀ i, offset ≤ tierB i) ∧
      (∀ i p, p ∈ scheduledRegularPrimeSets (selectedTailCellPrimes A B N X hi D)
        Qb top (cs.drop offset) n m i → tier p = tierB i) := by
  have hex (i : MovingRegularSlot n (scheduledSmallLength (cs.drop offset)) m) :
      ∃ b, offset ≤ b ∧ ∀ p,
        p ∈ scheduledRegularPrimeSets (selectedTailCellPrimes A B N X hi D)
          Qb top (cs.drop offset) n m i → tier p = b := by
    rcases i with ⟨u, i | i⟩
    · have hs : scheduledSmallCell top (cs.drop offset) i = top ∨
          scheduledSmallCell top (cs.drop offset) i ∈ cs.drop offset :=
        scheduledSmallCell_property (fun c => c = top ∨ c ∈ cs.drop offset) top
          (cs.drop offset) (Or.inl rfl) (fun c hc => Or.inr hc) i
      rcases hs with hs | hs
      · refine ⟨cs.length, hoffset, ?_⟩
        intro p hp
        change p ∈ selectedTailCellPrimes A B N X hi D
          (scheduledSmallCell top (cs.drop offset) i) at hp
        exact htop p (hs ▸ hp)
      · obtain ⟨j, hj, he⟩ := mem_drop_index cs offset _ hs
        refine ⟨j.val, hj, ?_⟩
        intro p hp
        apply hcomp j p
        change p ∈ selectedTailCellPrimes A B N X hi D
          (scheduledSmallCell top (cs.drop offset) i) at hp
        rwa [he]
    · exact ⟨cs.length, hoffset, hbulk⟩
  choose b hb ht using hex
  exact ⟨b, hb, ht⟩

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

theorem selected_cells_prime_tiers
    {A B : Set ℕ} {N hi top : ℕ} {a C L X J cb BD Bz : ℝ} {D : Finset ℕ}
    {cs : List ℕ} (k : ℕ) (hk : 0 < k) (hL : 0 ≤ L)
    (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) (hcb : 0 ≤ cb)
    (hJ : 16 * Real.exp ((1 / 100 : ℝ) * L) ≤ J)
    (herror : 48 * (64 * tailDefectBudget a C X + 2) ≤ J)
    (hgap : (2 : ℝ) ^ k * (movingCompensationGapRate k BD Bz * L) ≤ J / 4)
    (htop : SelectedSmallTailCell A B N a C L X hi D ((J - 2 * cb) / 6) top)
    (hcs : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j)
      cs (movingCompensationTargets J (movingCompensationGaps k BD Bz L))) :
    let Qb := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
      (Real.exp ((6 / 1000 : ℝ) * L)) \ D
    ∃ tier : ℕ → ℕ,
      (∀ n < cs.length, ∀ p ∈ completedCompensationSets A B N X hi D top cs n,
        tier p = n) ∧
      (∀ n m offset, offset ≤ cs.length →
        ∃ tierB : MovingRegularSlot n (scheduledSmallLength (cs.drop offset)) m → ℕ,
          (∀ i, offset ≤ tierB i) ∧
          (∀ i p, p ∈ scheduledRegularPrimeSets (selectedTailCellPrimes A B N X hi D)
            Qb top (cs.drop offset) n m i → tier p = tierB i)) := by
  intro Qb
  let ds := movingCompensationGaps k BD Bz L
  let ws := movingCompensationTargets J ds
  let E := movingCompensationGapRate k BD Bz * L
  have hJ0 : 0 ≤ J := (by positivity : 0 ≤ 16 * Real.exp ((1 / 100 : ℝ) * L)).trans hJ
  have hE0 : 0 ≤ E := mul_nonneg (movingCompensationGapRate_nonneg k hk BD Bz hBD hBz) hL
  have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hEJ : E ≤ J / 4 := by
    have h := mul_le_mul_of_nonneg_right hp hE0
    simpa only [one_mul] using h.trans hgap
  have hd : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ E :=
    movingCompensationGaps_bounds k hk BD Bz L hBD hBz hL
  have hw := movingCompensationTargets_separated J E ds hJ0 hEJ hd
  have hlow (w : ℝ) (hw : w ∈ ws) : 3 * J / 4 ≤ w := by
    have h := (movingCompensationTargets_mem_bounds J E ds hJ0 hE0 hd w hw).1
    simp only [ds, movingCompensationGaps_length] at h
    linarith only [h, hgap]
  have hpair := selected_centers_pairwise_separated hcs hw (by linarith only [herror, hJ0])
  let R := selectedTailCellPrimes A B N X hi D top ∪ Qb
  have hR (i : Fin cs.length) :
      Disjoint R (selectedTailCellPrimes A B N X hi D (cs.get i)) := by
    have hi' : i.val < ws.length := by rw [← hcs.length_eq]; exact i.isLt
    have hc := hcs.get i.isLt hi'
    have hwi : ws.get ⟨i, hi'⟩ ∈ ws := List.get_mem _ _
    have hj := selected_top_compensation_gap htop hc hcb (hlow _ hwi) herror
    have htopdis := (selectedTailCellPrimes_disjoint_of_gap A B N hi X D _ _ hj).symm
    apply Finset.disjoint_left.mpr
    intro p hp hpi
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.disjoint_left.mp htopdis) hp hpi
    · have hb := mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp hp).1
      have hiLog := mem_primeLogCellSet_iff.mp
        (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hpi).1).1
      have hsmall : Real.exp ((6 / 1000 : ℝ) * L) ≤ (cs.get i : ℝ) := by
        have he : Real.exp ((6 / 1000 : ℝ) * L) ≤ Real.exp ((1 / 100 : ℝ) * L) :=
          Real.exp_le_exp.mpr (by nlinarith only [hL])
        have hwlo := hlow _ hwi
        have hci := hc.1
        linarith only [he, hwlo, hci, hJ, Real.exp_nonneg ((1 / 100 : ℝ) * L)]
      linarith only [hb.2.2.2, hiLog.2.2.1, hsmall]
  obtain ⟨tier, htier, hrest⟩ := exists_selected_prime_tiers A B N hi X D R cs hpair hR
  refine ⟨tier, ?_, ?_⟩
  · intro n hn p hp
    have he := completedCompensationCell_used top cs n hn
    unfold completedCompensationSets at hp
    rw [he, list_headD_drop_get cs 0 n hn] at hp
    exact htier ⟨n, hn⟩ p hp
  · intro n m offset hoffset
    exact exists_scheduled_prime_tiers A B N hi X D Qb top cs tier htier
      (fun p hp => hrest p (Finset.mem_union_left _ hp))
      (fun p hp => hrest p (Finset.mem_union_right _ hp)) n m offset hoffset

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedScheduledDiagonal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published-input diagonal estimate on the actual selected cell schedule -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.selected_scheduled_diagonal_oai
    (P0 : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (k : ℕ) (hk : 2 ≤ k)
    (Bs BD Bz B Wwin Dφ : ℝ) (hBs : 1 ≤ Bs) (hBD : 1 ≤ BD) (hBz : 9 ≤ Bz)
    (hWwin : 0 ≤ Wwin) (hDφ : 0 ≤ Dφ)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dφ * |x - y|)
    (hdepth : 120 ≤ (k : ℝ) ^ 3)
    (hgap : (Bs + 1) + 2 * B +
      (Real.log 2 - Real.log (1 / 16000 : ℝ) + 5 / 4 + 1 + Real.log 12 + 1 + 1) + 6 ≤ BD - 1) :
    let Afreq := movingFrequencyRate (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4) k
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ p₀ : ℕ, 3 ≤ p₀ ∧
    ∀ᶠ L : ℝ in atTop, ∀ (Aset Bset : Set ℕ), Aset.Infinite → Bset.Infinite →
    ∀ (N : ℕ), (∀ p, p.Prime → Disjoint (tailResidues Aset N p) (negTailResidues Bset N p)) →
    ∀ (b endpoint top : ℕ) (a Y G J cb cd Δ upper X : ℝ) (cs : List ℕ),
      spectatorBulkCount k L = b + b → cs.length = k →
      0 < Y → Y ≤ Real.exp L → 0 ≤ cb →
      1024 * tailCellLinearRate a C + 52 ≤ (k : ℝ) ^ 4 →
      (8 + 4 * cs.length : ℕ) ≤ L →
      16 * Real.exp ((1 / 100 : ℝ) * L) ≤ J →
      48 * (64 * tailDefectBudget a C Y + 2) ≤ J →
      (2 : ℝ) ^ k * (movingCompensationGapRate k BD Bz * L) ≤ J / 4 →
      let Q := initialRegularPrimeRange L
      let D := scheduledPageDeletions P0 L (scheduledComparisonCutoff L)
      let Qb := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L)) \ D
      SelectedSmallTailCell Aset Bset N a C L Y endpoint D ((J - 2 * cb) / 6) top →
      List.Forall₂ (fun j w => SelectedSmallTailCell Aset Bset N a C L Y endpoint D (w / 4) j)
        cs (movingCompensationTargets J (movingCompensationGaps k BD Bz L)) →
      (∀ j ∈ initialSmallCellList top cs, Real.exp ((1 / 100 : ℝ) * L) ≤ (j : ℝ)) →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ G - 1 →
      smoothGiantLogNormalizer (smoothGiantPrimeRange G) logCellProfile G ≤ (91 / 100) * L →
      ∀ (q : Fin (b + b) → ℕ) [∀ i, Fact (q i).Prime],
      FrozenInitialSpectatorData Aset N q L ε p₀ D →
      ∀ (sl sr : Fin b → Q) (fallback : Q)
        (Dq : ∀ i, (ZMod (q i))ˣ) (childBound pivotBound V : ℕ → ℕ),
      Monotone V →
      (∀ n ≤ k, (V n : ℝ) ≤ Real.exp (Afreq * (b + b : ℕ))) →
      (∀ n ≤ k, ((transferFrequencyRange (V n)).card : ℝ) ≤ Real.exp (Afreq * (b + b : ℕ))) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * (b + b : ℕ))) →
      0 ≤ Δ → Δ ≤ spectatorBaseGap (Bs + 1) ((k : ℝ) ^ 4) (b + b : ℕ) →
      Real.exp Δ ≤ upper → upper - Real.exp Δ ≤ Real.exp (Wwin * (b + b : ℕ)) →
      ∀ favorable : ℕ → Bool,
      let F := movingOriginalLeaf Subtype.val q
        (initialMovingDataCutoff Subtype.val b b (initialSmallCellList top cs).length cb cd sl sr fallback)
        (fun i => normalizedResidueTransform (tailDensityMask Aset N (q i))) Dq Finset.univ
        ψ X (Real.exp Δ) upper
      ∀ n < k,
        scheduledCellDiagonal Subtype.val (List.ofFn q)
          (completedCompensationPrior Aset Bset N Y endpoint D Q top cs)
          childBound pivotBound V F logCellProfile (fun _ => G)
          (smoothGiantPrimeRange G) (Finset.Ioc ⌊Real.exp (G - 1)⌋₊ ⌊Real.exp (G + 1)⌋₊)
          (smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G)
          (fun c => primeSubsetPrior Q (selectedTailCellPrimes Aset Bset N Y endpoint D c))
          (primeSubsetPrior Q Qb) top cs n (b + b)
          (normalizedResidueFamily (tailDensityMask Aset N))
          (normalizedResidueFamily (tailDensityMask Aset N)) favorable ≤
        Real.exp (-(2 * B + 3) * (2 ^ n : ℕ) * (b + b : ℕ)) := by
  intro Afreq
  have hk0 : 0 < k := by omega
  have hz : 1 ≤ (k : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ k by omega))
  have hAfreq : 0 ≤ Afreq := movingFrequencyRate_nonneg _ _ _ _ (by linarith)
    (by linarith) (by linarith) hz k
  obtain ⟨ε, hε, hε1, p₀, hp₀, he⟩ := P0.moving_selected_initial_diagonal_uniform C hM ψ k
    (fun i => scheduledTailLength k i) hk0 Afreq Wwin 1 Dφ 1 2 1
    (Bs + 1) (BD - 1) Bz B hAfreq hWwin (by norm_num) hDφ (by norm_num)
    (by norm_num) (by norm_num) (by linarith) Dφ hDφ hloglip (by linarith)
    (by linarith) hBz
    (fun i => scheduledTailLength_budget k i i.isLt 2 (by norm_num) (by norm_num at hdepth ⊢; exact hdepth)) hgap
  refine ⟨ε, hε, hε1, p₀, hp₀, ?_⟩
  filter_upwards [he, eventual_scheduled_comparison_cutoffs k k p₀ (fun _ => Afreq),
    eventual_scheduled_comparison_count k, eventual_selected_bulk_mass hM,
    (spectatorBulkCount_tendsto k hk0).eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with L he hcut hcount hmass hm hL
  intro Aset Bset hA hB N hN b endpoint top a Y G J cb cd Δ upper X cs hsize hlen hY hYupper hcb
    hcell hcsCount hJ hJerr hJgap Q D Qb htop hcs hlower hG hcg q inst hq sl sr fallback Dq
    childBound pivotBound V hV hVbound hVcard hV0 hΔ hΔbound hupper hwindow favorable F n hn
  have hm' : 1 ≤ b + b := by exact_mod_cast (show (1 : ℝ) ≤ (b + b : ℕ) by simpa only [hsize] using hm)
  have hQprime := initialRegularPrimeRange_prime L
  let : Nonempty Q := ⟨⟨(selected_regular_alphabet_nonempty htop).choose,
    (selected_regular_alphabet_nonempty htop).choose_spec⟩⟩
  obtain ⟨hbulk, hbulklower⟩ := selected_bulk_prime_range L (by linarith) D
  have hDcard : D.card ≤ 2 := scheduledPageDeletions_card P0 L _
  have hmass' := hmass D hDcard
  obtain ⟨hμdata, hμlower, hνdata, hνlower⟩ :=
    selected_schedule_prime_data htop hcs (by linarith) hlower hbulk hbulklower hmass'
  obtain ⟨tier, hμtier, hνtier⟩ := selected_cells_prime_tiers k hk0 (by linarith)
    (by linarith) (by linarith) hcb hJ hJerr hJgap htop hcs
  obtain ⟨tierB, hTierBound, hBtier⟩ := hνtier n (b + b) (n + 1) (by omega)
  have hd := he ⟨n, hn⟩ b hsize
  dsimp only at hd
  rw [← scheduledTailLength_eq cs k n hlen] at hd
  let Qν := scheduledRegularPrimeSets (selectedTailCellPrimes Aset Bset N Y endpoint D)
    Qb top (cs.drop (n + 1)) n (b + b)
  let setsReg := primeMaskExtension Q (tailDensityMask Aset N)
  have hsmallsets : ∀ p, p.Prime → (setsReg p).Nonempty ∧ (setsReg p).card < p :=
    tailPrimeMaskExtension_data hA hB N Q hQprime (fun p hp => hN p (hQprime p hp))
  have hlen' := scheduled_drop_length_balance top cs n (by omega)
  have hlength : 4 + scheduledSmallLength (cs.drop (n + 1)) ≤ 10 + 4 * k := by
    rw [scheduledSmallLength_eq, List.length_drop, hlen]
    omega
  have hcomplex :
      ((D.card + (Fintype.card (MovingRegularSlot n (4 + scheduledSmallLength (cs.drop (n + 1))) (b + b)) +
        4 * n * 2 ^ n)) + (List.ofFn q).length : ℕ) ≤
      scheduledComparisonCount k (spectatorBulkCount k L) := by
    rw [hsize]
    exact scheduled_comparison_count k n _ _ (by omega) hlength D (List.ofFn q) hDcard (by simp)
  have hcuts := hcut.2.2.2.2 n (by omega) (V n) (by simpa only [hsize] using hVbound n (by omega))
  have hprimeBand (i) := hcut.2.2.2.1 (q i) (hq.lower i) (hq.upper i)
  have hfrequency : (V n : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) := by
    have hnat : (V n : ℝ) ≤ scheduledComparisonPrimeLo L := by exact_mod_cast hcuts.2
    exact hnat.trans_lt hcut.2.2.1
  have hbulkD : Disjoint Qb D := Finset.disjoint_left.mpr (fun _ hp hd => (Finset.mem_sdiff.mp hp).2 hd)
  have hpage := selected_schedule_avoids_giant_page P0 Aset Bset N endpoint Y L
    (scheduledComparisonCutoff L) top cs Qb hbulkD
  have hbtop : ∀ p ∈ completedCompensationSets Aset Bset N Y endpoint D top cs n,
      (p : ℝ) ≤ Real.exp (((cs.drop n).headD 0 : ℝ) + 1) :=
    completedCompensationSets_upper_used Aset Bset N endpoint Y D top cs n (by omega)
  have hfreqCard : (((transferFrequencyRange (V n)).erase 0).card : ℝ) ≤
      Real.exp (Afreq * (b + b : ℕ)) := by
    have he : (((transferFrequencyRange (V n)).erase 0).card : ℝ) ≤
        (transferFrequencyRange (V n)).card := by exact_mod_cast Finset.card_erase_le
    exact he.trans (hVcard n (by omega))
  have hcomplexReal :
      ((D.card + (Fintype.card (MovingRegularSlot n (4 + scheduledSmallLength (cs.drop (n + 1))) (b + b)) +
        4 * n * 2 ^ n)) + (List.ofFn q).length : ℕ) ≤ Real.exp ((2 + 1) * L) := by
    have hh : (((D.card + (Fintype.card (MovingRegularSlot n (4 + scheduledSmallLength (cs.drop (n + 1))) (b + b)) +
        4 * n * 2 ^ n)) + (List.ofFn q).length : ℕ) : ℝ) ≤
        scheduledComparisonCount k (spectatorBulkCount k L) := by exact_mod_cast hcomplex
    exact hh.trans (by norm_num; exact hcount)
  have hShell : primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
      (Real.exp ((6 / 1000 : ℝ) * L)) ⊆ Q := by
    simpa only [Finset.sdiff_empty] using initial_broad_cell_subset L (4 / 1000)
      (6 / 1000) (by linarith) (by norm_num) ∅
  have hdiag := hd tierB Q hQprime b (initialSmallCellList top cs).length sl sr fallback
    childBound pivotBound V (List.ofFn q) q Dq (fun i => tailDensityMask Aset N (q i))
    (fun _ => ε / 2) (scheduledComparisonPrimeLo L) (scheduledComparisonCutoff L)
    (fun p => tier p) X Δ upper logCellProfile (fun _ => G) D
    (completedCompensationSets Aset Bset N Y endpoint D top cs) Qν setsReg cb cd
    (((cs.drop n).headD 0 : ℝ) + 1) (scheduledSmallLower top (cs.drop (n + 1)) n)
    (normalizedResidueFamily (tailDensityMask Aset N)) favorable
    hlen' hV
    hfreqCard
    (hVbound n (by omega)) hV0 hΔ hΔbound hupper hwindow
    (by have he := Real.one_le_exp (show 0 ≤ (49 / 1000 : ℝ) * L by positivity); linarith)
    (fun i => (Nat.le_succ n).trans (hTierBound i)) hm' hq.ge_cutoff hq.nonempty hq.proper
    (hq.comparison_upper (by linarith)) hq.balanced_lower hq.balanced_upper (fun _ => by linarith)
    hq.character_bound logCellProfile_nonneg
    (fun x => (abs_of_nonneg (logCellProfile_nonneg x)).trans_le (logCellProfile_le_one x))
    hloglip logCellProfile_zero_outside hShell
    hcomplexReal
    (by intro p hp; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp; exact (inferInstance : Fact (q i).Prime).out)
    (fun _ => rfl) (fun j => (hμdata j).1) (fun i => (hνdata n (b + b) (n + 1) i).1)
    (fun j => (hμdata j).2) (fun i => (hνdata n (b + b) (n + 1) i).2)
    hμlower (hνlower n (b + b) (n + 1))
    (by intro p hp; exact List.mem_ofFn.mp hp) hq.injective hG
    (by intro j hj p hp; exact hμtier j (by omega) p hp) (fun i p hp => hBtier i p hp)
    hcuts.2 hcuts.1 hcut.2.1 hcut.2.2.1 (fun p => initialRegularPrimeRange_upper L p p.property)
    hprimeBand (fun z hz p hp j => (hpage z hz p hp).1 j) (hq.avoids_giant_page)
    (fun z hz p hp i => (hpage z hz p hp).2 n (b + b) (n + 1) i) (hq.avoids_bulk_page)
    hsmallsets hbtop logCellProfile_le_one
    (fun i p hp => scheduledSmallLower_prime_bound Aset Bset N endpoint top Y D Qb
      (cs.drop (n + 1)) n (b + b) i p hp)
    (by intro i p hp; exact_mod_cast hfrequency.trans_le (hνlower n (b + b) (n + 1) i p hp))
    (by intro p hp i z hz; exact scheduled_giant_regular_separation L G (by linarith) hG p hp z
          ((hνdata n (b + b) (n + 1) i).1 hz))
    (by simpa only [hsize, Nat.cast_mul, Nat.cast_ofNat] using
      selected_scheduled_drop_diagonal_gap k n hn (by linarith) hY hYupper hcell hcsCount hcg htop hcs)
  unfold scheduledCellDiagonal
  rw [scheduledRegularPrior_prime]
  rw [movingAmplitudeDiagonal_regular_congr Subtype.val (List.ofFn q)
    (completedCompensationPrior Aset Bset N Y endpoint D Q top cs) childBound pivotBound V
    F logCellProfile (fun _ => G) n _ (b + b) _ _ _ _
    (normalizedResidueFamily (tailDensityMask Aset N)) (normalizedResidueFamily setsReg)
    (normalizedResidueFamily (tailDensityMask Aset N)) favorable
    (fun p => (normalizedResidueFamily_primeMaskExtension Q (tailDensityMask Aset N) p p.property).symm)]
  exact hdiag

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.PublishedProgressionInput.selected_scheduled_diagonal_oai := @OAI.Ostmann.PublishedProgressionInput.selected_scheduled_diagonal_oai
