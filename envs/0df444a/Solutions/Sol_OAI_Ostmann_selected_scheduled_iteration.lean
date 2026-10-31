-- Prove2me | solution 1 for OAI.Ostmann.selected_scheduled_iteration
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:36:52.485996+00:00
-- url     : https://prove2.me/submissions/9a8d8ec9-7048-4860-a57f-52db39c98f95

import Mathlib
import Definitions.Def_OAIQ095D008
import Theorems.Thm_OAI_Ostmann_movingTemplatePrimeAmplitude_step_full_coefficients

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AdditiveFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Probability-normalized additive Fourier identities

These finite identities provide the normalization used in Section 6.
Fourier inversion is the library's discrete Fourier inversion theorem.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem stdAddChar_conj {p : ℕ} [NeZero p] (x : ZMod p) :
    conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have hn : ‖ZMod.stdAddChar x‖ = 1 := by simp [ZMod.stdAddChar_apply]; exact Circle.norm_coe _
  rw [← Complex.inv_eq_conj hn, AddChar.map_neg_eq_inv]

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferredPivotSubstitution
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Eliminating the extended integer by its exact signed quotient -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem reconstructedPivot_of_eq (N s : ℤ) (hs : s ≠ 0) (M : ℕ)
    (h : N = s * M) : reconstructedPivot N s = M := by
  rw [reconstructedPivot, Int.ediv_eq_of_eq_mul_right hs h, Int.toNat_natCast]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RecursiveTransferWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The recursive weight with its actual reconstructed integer pivots -/

namespace Ostmann

open scoped BigOperators Classical

theorem ValidTransferNode.historyPivot_eq {State : Type*} {sys : TransferHistorySystem State}
    {σ : State} {s v w : ℤ} {P : ℕ} (h : ValidTransferNode sys σ s v w P) :
    historyPivot sys σ s v w = P :=
  reconstructedPivot_of_eq _ _ h.root_ne_zero P h.relation

/-- No witness choices enter the recursive weight: the integer equation
forces the pivot at every valid node. -/
theorem recursiveTransferWeight_node {State : Type*} (sys : TransferHistorySystem State)
    (leaf : State → ℤ → ℂ) (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ (n + 1)) (P : ℕ)
    (hP : ValidTransferNode sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P) :
    recursiveTransferWeight sys leaf cutoff (n + 1) σ t =
      (cutoff σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) : ℂ) *
        recursiveTransferWeight sys leaf cutoff n (sys.leftState σ P) t.2.1 *
        star (recursiveTransferWeight sys leaf cutoff n (sys.rightState σ P) t.2.2) := by
  simp only [recursiveTransferWeight, hP.historyPivot_eq, hP, ite_true, if_true]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferGapRanges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's gaps give both frequency cutoffs and history rigidity -/

namespace Ostmann

open Filter
open scoped Topology

/-- The positive-product ranges make the determinant gap strict. -/
theorem transfer_integer_rigidity_gap (K B R : ℕ) (T Δ E C : ℝ)
    (hK : (K : ℝ) ≤ Real.exp (T + C)) (hB : (B : ℝ) ≤ Real.exp E)
    (hR : Real.exp (T + Δ - C) ≤ R) (hgap : Real.log 2 + 2 * C < Δ - E) :
    2 * K * B < R := by
  have h : (2 : ℝ) * K * B < R := by
    calc
      _ ≤ 2 * Real.exp (T + C) * Real.exp E := by gcongr
      _ = Real.exp (Real.log 2 + (T + C) + E) := by
        simp only [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ < Real.exp (T + Δ - C) := Real.exp_lt_exp.mpr (by linarith)
      _ ≤ R := hR
  exact_mod_cast h

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

theorem spectatorBulkCount_half (k : ℕ) (L : ℝ)
    (hL : 4 ≤ (k : ℝ) ^ 4 * L) :
    (k : ℝ) ^ 4 * L / 2 ≤ (spectatorBulkCount k L : ℝ) := by
  linarith [spectatorBulkCount_lower k L]

theorem spectatorBulkCount_iteration_budget (k : ℕ) (hk : 2 ≤ k)
    (L : ℝ) (hL : 1 ≤ L) (hscale : 4 ≤ (k : ℝ) ^ 4 * L)
    (loss : ℕ → ℝ) (hloss : ∀ j < k, loss j ≤ L) :
    ∑ j ∈ Finset.range k, (loss j + Real.log 2) ≤ (spectatorBulkCount k L : ℝ) := by
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk3 : (4 : ℝ) ≤ (k : ℝ) ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hk2 3
    norm_num at h
    linarith
  have hk4 : 4 * (k : ℝ) ≤ (k : ℝ) ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hk3 hk0]
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  calc
    _ ≤ ∑ _j ∈ Finset.range k, (L + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      exact add_le_add (hloss j (Finset.mem_range.mp hj)) hlog
    _ = (k : ℝ) * (L + 1) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ 2 * (k : ℝ) * L := by nlinarith
    _ ≤ (k : ℝ) ^ 4 * L / 2 := by nlinarith [mul_le_mul_of_nonneg_right hk4 (by linarith : 0 ≤ L)]
    _ ≤ _ := spectatorBulkCount_half k L hscale

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCutoffReserve
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual Section 7 gaps supply both integer-transfer reserves -/

namespace Ostmann

private theorem moving_sqrt_reserve (m : ℝ) (hm : 64 ≤ m) : Real.sqrt (4 * m) ≤ m / 4 := by
  have hm0 : 0 ≤ m := by linarith
  have hs := Real.sq_sqrt (show 0 ≤ 4 * m by positivity)
  have hp := mul_nonneg hm0 (sub_nonneg.mpr hm)
  nlinarith [Real.sqrt_nonneg (4 * m)]

theorem movingStepGap_succ (BD Bz z m : ℝ) (n : ℕ) :
    spectatorStepGap BD Bz z ((2 : ℝ) ^ (n + 1)) m =
      2 * spectatorStepGap BD Bz z ((2 : ℝ) ^ n) m +
        (4 / 5 : ℝ) * (2 : ℝ) ^ n * Real.log 2 * m := by
  unfold spectatorStepGap
  rw [Real.log_pow, Real.log_pow]
  push_cast
  rw [pow_succ]
  ring

/-- The next pivot gap exceeds the current Fourier exponent by a positive
linear amount, uniformly over all tree levels. -/
theorem movingCutoff_diagonal_reserve (Bs BD Bz z m : ℝ)
    (hBD : Bs + 1 ≤ BD) (hBz : 8 ≤ Bz)
    (hz : 1 ≤ z) (hm : 64 ≤ m) (n : ℕ) :
    (3 / 20 : ℝ) * (2 : ℝ) ^ n * m ≤
      spectatorStepGap BD Bz z ((2 : ℝ) ^ n) m - movingCutoffExponent Bs BD Bz z m n := by
  have hsqrt := moving_sqrt_reserve m hm
  have hm0 : 0 ≤ m := by linarith
  have hlogz := Real.log_nonneg hz
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  induction n with
  | zero =>
    rw [movingCutoffExponent_zero]
    simp only [spectatorStepGap, spectatorBaseGap, pow_zero, one_mul, Real.log_one,
      mul_zero, add_zero]
    have hb : Bs + 8 * Real.log z + 1 ≤ BD + Bz * Real.log z := by
      nlinarith [mul_nonneg (show 0 ≤ Bz - 8 by linarith) hlogz]
    nlinarith [mul_le_mul_of_nonneg_right hb hm0]
  | succ n ih =>
    rw [movingStepGap_succ, movingCutoffExponent_succ, pow_succ]
    have hr : 0 ≤ (2 : ℝ) ^ n := by positivity
    have hsl := mul_le_mul_of_nonneg_left hsqrt hr
    have hl := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog2 hr) hm0
    nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Symmetries of the mixed Fourier bound

Conjugation and multiplication of the field argument by a unit preserve
both the energy hypothesis and the mixed character/Fourier bound. These
are the orientation changes used by the bottom pairs.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem additiveFourier_conj {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => conj (f x)) a = conj (additiveFourier f (-a)) := by
  simp only [additiveFourier_apply, map_mul, map_inv₀, map_natCast, map_sum,
    stdAddChar_conj, mul_neg, neg_neg]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotSystem
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original recursive weight on moving-giant states

A reconstructed pivot is the composite `u*p`; only its quotient `p` becomes
the new giant. The compensation primes remain in the regular child lists.
-/

namespace Ostmann
open scoped Classical

theorem MovingSlotData.Follows.root {σ : Type*} {n : ℕ} {T : MovingSlotData σ n}
    {t : FrequencyTree ℤ n} (h : T.Follows t) : T.frequency = frequencyRoot n t := by
  cases T with
  | leaf => exact h
  | node => exact h.1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteEnumeration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An explicit bridge between equivalent finite enumerations -/

namespace Ostmann

theorem finite_univ_canonical {A : Type*} [Finite A] (F : Fintype A) :
    @Finset.univ A F = @Finset.univ A (Fintype.ofFinite A) := by
  cases Subsingleton.elim F (Fintype.ofFinite A)
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRecursiveSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full original support as local guards in the sampled recursion

All current-state coprimalities and all descendant-frequency unit tests are
retained. This puts the existing fully supported coefficient into the local
recursion form, without conditioning any internal sample prior.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem movingFullSupport_node {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (s : ℤ) (CL CR u : List σ) (l r : MovingSlotData σ n) (XL XR : ℕ) :
    let T := MovingSlotData.node s CL CR u l r
    let p := (MovingSlotData.step s CL CR u l r false).naturalPivot value XL XR
    movingFullSupport value outside T XL XR ↔
      movingLocalSupport value outside ⟨n + 1, T, XL, XR⟩ ∧
      movingFullSupport value outside l p XL ∧ movingFullSupport value outside r p XR := by
  simp only [movingFullSupport, movingLocalSupport, movingFullOutsidePairwise, movingNaturalGiantUnits]
  tauto

theorem movingSlotCutoff_guarded {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (x : MovingSlotState σ) (s v w : ℤ) :
    movingSlotCutoff value childBound pivotBound (movingGuardedExtra value outside E) x s v w =
      if movingLocalSupport value outside x then
        movingSlotCutoff value childBound pivotBound E x s v w else 0 := by
  unfold movingSlotCutoff movingGuardedExtra
  split_ifs <;> rfl

/-- The fully supported original history coefficient equals the recursive
coefficient with the literal local support test at each node and leaf. -/
theorem movingSupportedWeight_recursive {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (XL XR : ℕ) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
      (movingGuardedLeaf value outside F)
      (movingSlotCutoff value childBound pivotBound (movingGuardedExtra value outside E))
      n ⟨n, T, XL, XR⟩ t =
        movingSupportedWeight value outside T XL XR
          (recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
            (movingSlotCutoff value childBound pivotBound E) n ⟨n, T, XL, XR⟩ t) := by
  let sys := movingSlotSystem value childBound pivotBound
  let cut := movingSlotCutoff value childBound pivotBound E
  let cutg := movingSlotCutoff value childBound pivotBound (movingGuardedExtra value outside E)
  induction T generalizing XL XR with
  | leaf s regular => rfl
  | @node n s CL CR u l r hl hr =>
      let x : MovingSlotState σ := ⟨n + 1, .node s CL CR u l r, XL, XR⟩
      let P := historyPivot sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      let p := (MovingSlotData.step s CL CR u l r false).naturalPivot value XL XR
      have hp : P / MovingSlotReversal.naturalProduct value u = p := by
        simp only [P, p, historyPivot, sys, movingSlotSystem, x, MovingSlotState.leftProduct,
          MovingSlotState.rightProduct, MovingSlotReversal.naturalPivot, MovingSlotData.step,
          movingGiantPivot, Nat.mul_one, ← hT.1, ← hT.2.1.root, ← hT.2.2.root]
      by_cases hv : ValidTransferNode sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P
      · rw [recursiveTransferWeight_node sys _ cutg n x t P hv]
        change (cutg x t.1 _ _ : ℂ) *
            recursiveTransferWeight sys _ cutg n ⟨n, l, P / MovingSlotReversal.naturalProduct value u, XL⟩ t.2.1 *
            star (recursiveTransferWeight sys _ cutg n ⟨n, r, P / MovingSlotReversal.naturalProduct value u, XR⟩ t.2.2) = _
        rw [hp, hl t.2.1 hT.2.1 p XL, hr t.2.2 hT.2.2 p XR]
        have hg := movingSlotCutoff_guarded value outside childBound pivotBound E x
          t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
        change cutg x t.1 _ _ = if movingLocalSupport value outside x then cut x t.1 _ _ else 0 at hg
        rw [hg]
        unfold movingSupportedWeight
        have hs := movingFullSupport_node value outside s CL CR u l r XL XR
        dsimp only at hs
        rw [hs]
        rw [recursiveTransferWeight_node sys F cut n x t P hv]
        have hleft : sys.leftState x P =
            ⟨n, l, P / MovingSlotReversal.naturalProduct value u, XL⟩ := rfl
        have hright : sys.rightState x P =
            ⟨n, r, P / MovingSlotReversal.naturalProduct value u, XR⟩ := rfl
        rw [hleft, hright, hp]
        by_cases hA : movingLocalSupport value outside x <;>
          by_cases hB : movingFullSupport value outside l p XL <;>
          by_cases hC : movingFullSupport value outside r p XR
        all_goals dsimp only [x, p] at hA hB hC ⊢
        all_goals simp only [hA, hB, hC, and_true, and_false,
          ite_true, if_true, ite_false, if_false, Complex.ofReal_zero, zero_mul, mul_zero, star_zero]
        rfl
      · have hz₁ : recursiveTransferWeight sys (movingGuardedLeaf value outside F) cutg
            (n + 1) x t = 0 := by simp only [recursiveTransferWeight, P, hv, ite_false, if_false]
        have hz₂ : recursiveTransferWeight sys F cut (n + 1) x t = 0 := by
          simp only [recursiveTransferWeight, P, hv, ite_false, if_false]
        rw [hz₁, hz₂]
        unfold movingSupportedWeight
        split_ifs <;> rfl

theorem movingFrequencySkeleton_frequencyTree (σ : Type*) (n : ℕ)
    (t : FrequencyTree ℤ n) :
    (movingFrequencySkeleton σ n t).frequencyTree = t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [movingFrequencySkeleton, MovingSlotData.frequencyTree, ih]
    rfl

theorem MovingSlotData.skeleton_frequencyProduct {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) :
    (movingFrequencySkeleton σ n T.frequencyTree).frequencyProduct = T.frequencyProduct := by
  induction T with
  | leaf => rfl
  | node s CL CR u l r hl hr =>
    simp only [MovingSlotData.frequencyTree, movingFrequencySkeleton, frequencyProduct, hl, hr]

theorem MovingSlotData.rootData_regularSlots {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) : T.rootData.regularSlots = T.regularSlots := by
  cases T <;> rfl

theorem MovingSlotData.rootData_frequencyProduct {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) : T.rootData.frequencyProduct = T.frequencyProduct := by
  cases T with
  | leaf => rfl
  | node s CL CR u l r =>
    simp only [rootData, frequencyProduct, skeleton_frequencyProduct]

theorem MovingSlotData.rootData_idempotent {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) : T.rootData.rootData = T.rootData := by
  cases T with
  | leaf => rfl
  | node s CL CR u l r =>
    simp only [rootData, movingFrequencySkeleton_frequencyTree]

theorem movingLocalSupport_rootData {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    (x : MovingSlotState σ) :
    movingLocalSupport value outside ⟨x.depth, x.data.rootData, x.leftGiant, x.rightGiant⟩ ↔
      movingLocalSupport value outside x := by
  simp only [movingLocalSupport, MovingSlotData.currentSlots, movingLocalGiantUnits,
    MovingSlotData.rootData_regularSlots, MovingSlotData.rootData_frequencyProduct]

theorem movingLocalExtra_guarded {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ) :
    movingLocalExtra (movingGuardedExtra value outside (movingLocalExtra E)) =
      movingGuardedExtra value outside (movingLocalExtra E) := by
  funext x s v w
  simp only [movingLocalExtra, movingGuardedExtra, movingLocalSupport_rootData,
    MovingSlotData.rootData_idempotent]

/-- The sample expansion of the fully supported original coefficient. Every
sample retains its original weight, including samples whose support fails. -/
theorem movingSampledWeight_supported {σ : Type*} [Fintype σ] (value : σ → ℕ)
    (outside : List ℕ) (μ : ℕ → σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) :
    movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F)
      (movingGuardedExtra value outside (movingLocalExtra E)) n t small bulk XL XR =
      ∑ a : MovingSampleSlots σ n, (movingSamplesPrior μ a : ℂ) *
        movingSupportedWeight value outside (buildMovingSlotData n t small bulk a) XL XR
          (recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
            (movingSlotCutoff value childBound pivotBound (movingLocalExtra E)) n
            ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t) := by
  unfold movingSampledWeight
  rw [movingLocalExtra_guarded]
  apply Finset.sum_congr rfl
  intro a _
  rw [movingSupportedWeight_recursive value outside childBound pivotBound F (movingLocalExtra E)
    _ t (buildMovingSlotData_follows n t small bulk a)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRecursiveCompensation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extracting compensation from the actual supported recursion -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingSlotCutoff_compensated {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (x : MovingSlotState σ) (s v w : ℤ) :
    movingSlotCutoff value childBound pivotBound (movingCompensatedExtra value E) x s v w =
      (x.compensation value : ℝ) * movingSlotCutoff value childBound pivotBound E x s v w := by
  unfold movingSlotCutoff movingCompensatedExtra
  split_ifs <;> simp only [mul_zero]

theorem MovingSlotState.compensation_rootData {σ : Type*} (value : σ → ℕ)
    (x : MovingSlotState σ) :
    (⟨x.depth, x.data.rootData, x.leftGiant, x.rightGiant⟩ : MovingSlotState σ).compensation value =
      x.compensation value := by
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> rfl

theorem movingLocalExtra_compensated {σ : Type*} (value : σ → ℕ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ) :
    movingLocalExtra (movingCompensatedExtra value E) =
      movingCompensatedExtra value (movingLocalExtra E) := by
  funext x s v w
  simp only [movingLocalExtra, movingCompensatedExtra, MovingSlotState.compensation_rootData]

/-- Each node contributes its newly sampled compensation exactly once,
including off-support samples where both sides vanish. -/
theorem movingRecursiveWeight_compensated {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (a : MovingSampleSlots σ n) (XL XR : ℕ) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound (movingCompensatedExtra value E)) n
      ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t =
        (movingSampleProduct value a : ℂ) *
          recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
            (movingSlotCutoff value childBound pivotBound E) n
            ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t := by
  let sys := movingSlotSystem value childBound pivotBound
  let cut := movingSlotCutoff value childBound pivotBound E
  let cutc := movingSlotCutoff value childBound pivotBound (movingCompensatedExtra value E)
  induction a generalizing XL XR with
  | leaf => simp only [movingSampleProduct, Nat.cast_one, one_mul, recursiveTransferWeight]
  | @node n a l r hl hr =>
    let x : MovingSlotState σ :=
      ⟨n + 1, buildMovingSlotData (n + 1) t small bulk (.node a l r), XL, XR⟩
    let P := historyPivot sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    by_cases hv : ValidTransferNode sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P
    · rw [recursiveTransferWeight_node sys F cutc n x t P hv,
        recursiveTransferWeight_node sys F cut n x t P hv]
      change (cutc x t.1 _ _ : ℂ) *
        recursiveTransferWeight sys F cutc n ⟨n, _, _, _⟩ t.2.1 *
        star (recursiveTransferWeight sys F cutc n ⟨n, _, _, _⟩ t.2.2) = _
      simp only [ite_true, if_true, Bool.false_eq_true, ite_false, if_false]
      rw [hl, hr]
      have hc : cutc x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) =
          (x.compensation value : ℝ) * cut x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) :=
        movingSlotCutoff_compensated value childBound pivotBound E x _ _ _
      rw [hc]
      simp only [movingSampleProduct, Complex.ofReal_mul, Complex.ofReal_natCast,
        Nat.cast_mul, star_mul, star_natCast]
      change _ = (x.compensation value : ℂ) * _ * _ * _
      simp only [sys, movingSlotSystem, MovingSlotState.child, x, buildMovingSlotData,
        ite_true, if_true, Bool.false_eq_true, ite_false, if_false]
      ring
    · have hz₁ : recursiveTransferWeight sys F cutc (n + 1) x t = 0 := by
        simp only [recursiveTransferWeight, P, hv, ite_false, if_false]
      have hz₂ : recursiveTransferWeight sys F cut (n + 1) x t = 0 := by
        simp only [recursiveTransferWeight, P, hv, ite_false, if_false]
      rw [hz₁, hz₂, mul_zero]

theorem movingSupportedWeight_mul {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) (c z : ℂ) :
    movingSupportedWeight value outside T XL XR (c * z) =
      c * movingSupportedWeight value outside T XL XR z := by
  unfold movingSupportedWeight
  split_ifs <;> simp only [mul_zero]

/-- Exact compensated prior times the supported coefficient with node
compensations removed. This is the scalar used by the pattern comparison. -/
theorem movingSampledWeight_compensated_supported {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) :
    movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F)
      (movingGuardedExtra value outside (movingLocalExtra (movingCompensatedExtra value E)))
      n t small bulk XL XR =
      ∑ a : MovingSampleSlots σ n,
        (((movingSampleProduct value a : ℝ) * movingSamplesPrior μ a : ℝ) : ℂ) *
          movingSupportedWeight value outside (buildMovingSlotData n t small bulk a) XL XR
            (recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
              (movingSlotCutoff value childBound pivotBound (movingLocalExtra E)) n
              ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t) := by
  rw [movingSampledWeight_supported]
  apply Finset.sum_congr rfl
  intro a _
  rw [movingLocalExtra_compensated, movingRecursiveWeight_compensated,
    movingSupportedWeight_mul, Complex.ofReal_mul, Complex.ofReal_natCast]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSamplePairExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact paired expansion of the fully supported sampled coefficient

The equality-pattern scalar is the literal original prior times all node
compensations. The remaining coefficient retains every support test.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem movingSupportedSampledWeight_eq {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) :
    movingSupportedSampledWeight value outside μ childBound pivotBound F E n t small bulk XL XR =
      movingCompensatedAverage μ value n
        (movingSupportedSampleTerm value outside childBound pivotBound F E n t small bulk XL XR) :=
  movingSampledWeight_compensated_supported value outside μ childBound pivotBound F E n t small bulk XL XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_NormalizedResidueIndicator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's normalized residue indicators and additive transforms -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

theorem normalizedResidueTransform_neg {p : ℕ} [Fact p.Prime] (S : Finset (ZMod p)) (x : ZMod p) :
    normalizedResidueTransform S (-x) = conj (normalizedResidueTransform S x) := by
  have hreal : (fun y => conj (normalizedResidueIndicator S y)) = normalizedResidueIndicator S := by
    funext y
    simp only [normalizedResidueIndicator, Complex.conj_ofReal]
  have hh := additiveFourier_conj (normalizedResidueIndicator S) (-x)
  rw [hreal, neg_neg] at hh
  simp only [normalizedResidueTransform, densityFourier, map_mul, Complex.conj_ofReal]
  rw [hh]

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantIntervalBridge
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized giant prior and its complete logarithmic cell -/

namespace Ostmann
open scoped Classical BigOperators

theorem smoothGiant_nonzero_in_log_cell (φ : ℝ → ℝ) (G : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (p : ℕ) (hp : 0 < p)
    (hφ : φ (Real.log p - G) ≠ 0) :
    p ∈ Finset.Ioc ⌊Real.exp (G - 1)⌋₊ ⌊Real.exp (G + 1)⌋₊ := by
  have hh : |Real.log p - G| < 1 := by
    by_contra h
    exact hφ (hout _ (le_of_not_gt h))
  have hh' := abs_lt.mp hh
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  apply Finset.mem_Ioc.mpr
  constructor
  · apply (Nat.floor_lt (Real.exp_nonneg _)).mpr
    exact (Real.lt_log_iff_exp_lt hp').mp (by linarith)
  · apply Nat.le_floor
    exact (Real.log_le_iff_le_exp hp').mp (by linarith)

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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingLivePrimeDivisors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frequency separation from the live original prime priors -/
namespace Ostmann
open scoped Classical BigOperators

theorem live_prime_product_divisor_large {I P : Type*} [Fintype I]
    (value : P → ℕ) (hvalue : ∀ p, (value p).Prime)
    (ν : I → P → ℝ) (V : ℕ)
    (hlive : ∀ i p, ν i p ≠ 0 → V < value p)
    (y : I → P) (hy : (∏ i, ν i (y i)) ≠ 0)
    (q : ℕ) (hq : q.Prime) (hd : q ∣ ∏ i, value (y i)) : V < q := by
  obtain ⟨i, _, hi⟩ := (hq.prime.dvd_finsetProd_iff _).mp hd
  have he : q = value (y i) := (Nat.dvd_prime (hvalue _)).mp hi |>.resolve_left hq.ne_one
  rw [he]
  exact hlive i (y i) (Finset.prod_ne_zero_iff.mp hy i (Finset.mem_univ _))

theorem live_giant_product_divisor_large {I P : Type*} [Fintype I]
    (value : P → ℕ) (hvalue : ∀ p, (value p).Prime)
    (ν : I → P → ℝ) (V X : ℕ) (hX : X.Prime) (hXV : V < X)
    (hlive : ∀ i p, ν i p ≠ 0 → V < value p)
    (y : I → P) (hy : (∏ i, ν i (y i)) ≠ 0)
    (q : ℕ) (hq : q.Prime) (hd : q ∣ X * ∏ i, value (y i)) : V < q := by
  rcases hq.dvd_mul.mp hd with hd | hd
  · have he : q = X := (Nat.dvd_prime hX).mp hd |>.resolve_left hq.ne_one
    exact he ▸ hXV
  · exact live_prime_product_divisor_large value hvalue ν V hlive y hy q hq hd

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingProductGapBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The recursive product budget is the prescribed compensation gap -/
namespace Ostmann

private theorem drop_sum_head (ws : List ℝ) (n : ℕ) :
    (ws.drop n).sum = (ws.drop n).headD 0 + (ws.drop (n + 1)).sum := by
  induction ws generalizing n with
  | nil => simp
  | cons w ws ih =>
    cases n with
    | zero => simp
    | succ n => simpa only [List.drop_succ_cons] using ih n

/-- With exact target centers, the product remaining at depth `n` is precisely
that of the protected slots and the as-yet unused compensation types. -/
theorem movingProductExponent_targets (G J : ℝ) (ws : List ℝ) (n : ℕ) :
    movingProductExponent (movingTargetPivotExponent G ws) (2 * G + J + ws.sum) n =
      2 * G + (2 : ℝ) ^ n * (J + (ws.drop n).sum) := by
  induction n with
  | zero => simp only [movingProductExponent, pow_zero, List.drop_zero, one_mul, add_assoc]
  | succ n ih =>
    rw [movingProductExponent, ih, movingTargetPivotExponent, pow_succ, drop_sum_head ws n]
    ring

private theorem target_drop_gap (J : ℝ) (ds : List ℝ) (n : ℕ) (hn : n < ds.length) :
    J + ((movingCompensationTargets J ds).drop (n + 1)).sum -
      ((movingCompensationTargets J ds).drop n).headD 0 = (ds.drop n).headD 0 := by
  induction ds generalizing n with
  | nil => simp at hn
  | cons d ds ih =>
    cases n with
    | zero => simp only [movingCompensationTargets, List.drop_zero, List.headD_cons,
        List.drop_succ_cons]; ring
    | succ n =>
      have hn' : n < ds.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hn
      simpa only [movingCompensationTargets, List.drop_succ_cons] using ih n hn'

/-- This is the exact gap from the manuscript's backwards recursion, expressed
in the product budget used by the integer-extended coefficients. -/
theorem movingProductExponent_target_gap (G J : ℝ) (ds : List ℝ)
    (n : ℕ) (hn : n < ds.length) :
    let ws := movingCompensationTargets J ds
    movingProductExponent (movingTargetPivotExponent G ws) (2 * G + J + ws.sum) n -
      2 * movingTargetPivotExponent G ws n = (2 : ℝ) ^ n * (ds.drop n).headD 0 := by
  dsimp only
  rw [movingProductExponent_targets, movingTargetPivotExponent, drop_sum_head]
  have hh := target_drop_gap J ds n hn
  linear_combination (2 : ℝ) ^ n * hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingProductPrescribedCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prescribed cutoff is the exact-target instance of the product schedule -/
namespace Ostmann
open scoped BigOperators

private theorem headD_drop_ofFn {k : ℕ} (f : Fin k → ℝ) (n : ℕ) (hn : n < k) :
    ((List.ofFn f).drop n).headD 0 = f ⟨n, hn⟩ := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    rw [List.ofFn_succ]
    cases n with
    | zero => simp
    | succ n =>
      rw [List.drop_succ_cons]
      exact (ih (fun i => f i.succ) n (by omega)).trans (congrArg f (Fin.ext (by rfl)))

theorem movingProductExponent_sum_gaps (T : ℕ → ℝ) (W : ℝ) (n : ℕ) :
    movingProductExponent T W n = W +
      ∑ j ∈ Finset.range n, (movingProductExponent T W j - 2 * T j) := by
  induction n with
  | zero => simp [movingProductExponent]
  | succ n ih =>
    rw [Finset.sum_range_succ, movingProductExponent]
    linarith

theorem movingProductFrequency_prescribed (G J Y Bs BD Bz L : ℝ) (k n : ℕ)
    (hn : n ≤ k)
    (hbase : 2 * G + J + (movingCompensationTargets J (movingCompensationGaps k BD Bz L)).sum - Y =
      spectatorBaseGap Bs ((k : ℝ) ^ 4) (spectatorBulkCount k L)) :
    let ws := movingCompensationTargets J (movingCompensationGaps k BD Bz L)
    movingProductFrequencyExponent (movingTargetPivotExponent G ws)
      (2 * G + J + ws.sum) Y (spectatorBulkCount k L) n =
      movingCutoffExponent Bs BD Bz ((k : ℝ) ^ 4) (spectatorBulkCount k L) n := by
  intro ws
  unfold movingProductFrequencyExponent movingCutoffExponent
  rw [movingProductExponent_sum_gaps]
  have hsum : (∑ j ∈ Finset.range n,
      (movingProductExponent (movingTargetPivotExponent G ws) (2 * G + J + ws.sum) j -
        2 * movingTargetPivotExponent G ws j)) =
      ∑ j ∈ Finset.range n, spectatorStepGap BD Bz ((k : ℝ) ^ 4)
        ((2 : ℝ) ^ j) (spectatorBulkCount k L) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjk : j < k := (Finset.mem_range.mp hj).trans_le hn
    rw [movingProductExponent_target_gap G J _ j (by simpa using hjk)]
    unfold movingCompensationGaps
    rw [headD_drop_ofFn _ j hjk]
    dsimp only
    exact mul_div_cancel₀ _ (by positivity)
  rw [hsum]
  dsimp only [ws] at *
  linarith

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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingProductRigidity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integer rigidity margin survives the actual selected cell centers -/
namespace Ostmann

theorem movingProductFrequency_gap (T : ℕ → ℝ) (W Y m : ℝ) (n : ℕ) :
    (movingProductExponent T W n - 2 * T n) - movingProductFrequencyExponent T W Y m n =
      Y - 2 * T n - (2 : ℝ) ^ n * Real.sqrt (4 * m) := by
  unfold movingProductFrequencyExponent
  ring

/-- The initial center error cancels from this margin. Only the current
pivot-cell error remains, twice. -/
theorem movingProductFrequency_rigidity_margin (T U : ℕ → ℝ) (W Z Y m R : ℝ) (n : ℕ)
    (hT : T n ≤ U n + (2 : ℝ) ^ n * R) (hR : R ≤ m / 40)
    (hideal : (3 / 20 : ℝ) * (2 : ℝ) ^ n * m ≤
      (movingProductExponent U Z n - 2 * U n) -
        movingProductFrequencyExponent U Z Y m n) :
    (1 / 10 : ℝ) * (2 : ℝ) ^ n * m ≤
      (movingProductExponent T W n - 2 * T n) -
        movingProductFrequencyExponent T W Y m n := by
  rw [movingProductFrequency_gap] at hideal ⊢
  have he := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ (2 : ℝ) ^ n)
  nlinarith only [hideal, hT, he]

theorem movingProductFrequency_prescribed_margin (G J Y Bs BD Bz L : ℝ) (k n : ℕ)
    (hn : n < k) (T : ℕ → ℝ) (W R : ℝ)
    (hbase : 2 * G + J + (movingCompensationTargets J (movingCompensationGaps k BD Bz L)).sum - Y =
      spectatorBaseGap Bs ((k : ℝ) ^ 4) (spectatorBulkCount k L))
    (hT : T n ≤ movingTargetPivotExponent G
      (movingCompensationTargets J (movingCompensationGaps k BD Bz L)) n + (2 : ℝ) ^ n * R)
    (hR : R ≤ (spectatorBulkCount k L : ℝ) / 40)
    (hBD : Bs + 1 ≤ BD) (hBz : 8 ≤ Bz) (hk : 1 ≤ (k : ℝ) ^ 4)
    (hm : 64 ≤ (spectatorBulkCount k L : ℝ)) :
    (1 / 10 : ℝ) * (2 : ℝ) ^ n * spectatorBulkCount k L ≤
      (movingProductExponent T W n - 2 * T n) -
        movingProductFrequencyExponent T W Y (spectatorBulkCount k L) n := by
  let ds := movingCompensationGaps k BD Bz L
  let ws := movingCompensationTargets J ds
  let U := movingTargetPivotExponent G ws
  let Z := 2 * G + J + ws.sum
  apply movingProductFrequency_rigidity_margin T U W Z Y (spectatorBulkCount k L) R n hT hR
  have he := movingProductExponent_target_gap G J ds n (by simpa only [ds, movingCompensationGaps_length] using hn)
  have hfreq := movingProductFrequency_prescribed G J Y Bs BD Bz L k n hn.le hbase
  change movingProductFrequencyExponent U Z Y (spectatorBulkCount k L) n = _ at hfreq
  change movingProductExponent U Z n - 2 * U n = _ at he
  rw [hfreq, he]
  have hg : (2 : ℝ) ^ n * (ds.drop n).headD 0 =
      spectatorStepGap BD Bz ((k : ℝ) ^ 4) ((2 : ℝ) ^ n) (spectatorBulkCount k L) := by
    have hs := movingProductFrequency_prescribed G J Y Bs BD Bz L k (n + 1) (by omega) hbase
    have hr := movingProductFrequency_reserve U Z Y (spectatorBulkCount k L) n
    change movingProductFrequencyExponent U Z Y (spectatorBulkCount k L) (n + 1) = _ at hs
    rw [hs, hfreq, movingCutoffExponent_succ] at hr
    linarith only [hr, he]
  rw [hg]
  exact movingCutoff_diagonal_reserve Bs BD Bz ((k : ℝ) ^ 4) (spectatorBulkCount k L)
    hBD hBz hk hm n

theorem movingProductNaturalCutoff_rigidity (T : ℕ → ℝ) (W Y m C : ℝ)
    (n P R : ℕ)
    (hP : (P : ℝ) ≤ Real.exp (T n + C))
    (hR : Real.exp (movingProductExponent T W n - T n - C) ≤ (R : ℝ))
    (hmargin : Real.log 2 + 2 * C <
      (movingProductExponent T W n - 2 * T n) - movingProductFrequencyExponent T W Y m n) :
    2 * P * movingProductNaturalCutoff T W Y m n < R := by
  apply transfer_integer_rigidity_gap P (movingProductNaturalCutoff T W Y m n) R
    (T n) (movingProductExponent T W n - 2 * T n)
    (movingProductFrequencyExponent T W Y m n) C hP
    (Nat.floor_le (Real.exp_pos _).le) _ hmargin
  convert hR using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSmallProductLower
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining the actual small-cell contribution to the regular modulus -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingTemplate_small_product_lower {A : Type*} (value : A → ℕ)
    (n r m : ℕ) (y : MovingRegularSlot n r m → A)
    (lower : TreeLeafIndex n × Fin r → ℝ)
    (hlower : ∀ j, Real.exp (lower j) ≤ (value (y (j.1, .inl j.2)) : ℝ)) :
    Real.exp (∑ j, lower j) ≤
      ((∏ j : TreeLeafIndex n × Fin r, value (y (j.1, .inl j.2)) : ℕ) : ℝ) := by
  rw [Real.exp_sum, Nat.cast_prod]
  exact Finset.prod_le_prod (fun j _ => Real.exp_nonneg _) (fun j _ => hlower j)

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

theorem mem_initialRegularPrimeRange (L : ℝ) (p : ℕ) (hp : p.Prime)
    (hbound : (p : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) :
    p ∈ initialRegularPrimeRange L := Nat.mem_primesLE.mpr ⟨Nat.le_floor hbound, hp⟩

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingData
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original cutoff weight as a function of the actual leaf data -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem initialRegularFromList_mapped {P : Type*} (b r : ℕ) (fallback : P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    initialRegularFromList b r fallback ((movingTemplateSlotList 0 (r + r) (b + b)).map y) = y := by
  funext i
  unfold initialRegularFromList
  rw [List.getD_eq_getElem _ _ (by
    simpa only [List.length_map] using ((movingTemplateListEquiv 0 (r + r) (b + b)).symm i).isLt)]
  rw [List.getElem_map]
  change y ((movingTemplateSlotList 0 (r + r) (b + b)).get
    ((movingTemplateListEquiv 0 (r + r) (b + b)).symm i)) = y i
  rw [← movingTemplateListEquiv_apply, Equiv.apply_symm_apply]

theorem initialMovingDataCutoff_zero {P : Type*} (value : P → ℕ) (b d r : ℕ)
    (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P) {n : ℕ} (T : MovingSlotData P n) :
    initialMovingDataCutoff value b d r cb cd sl sr fallback T 0 = 0 := by
  simp only [initialMovingDataCutoff, ↓reduceIte]

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

theorem initialMovingCutoffWeight_bulk_product_lower {P : Type*} (value : P → ℕ)
    (hvalue : ∀ p, 0 < value p) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P)
    (hy : initialMovingCutoffWeight value b d r cb cd sl sr y ≠ 0) :
    Real.exp (2 * cb - 2) < (∏ i : Fin (b + b), (value (y ((), .inr i)) : ℝ)) := by
  have h := (abs_lt.mp (initialMovingCutoffWeight_live_sums value b d r cb cd sl sr y hy).1).1
  have hp : 0 < ∏ i : Fin (b + b), (value (y ((), .inr i)) : ℝ) :=
    Finset.prod_pos (fun i _ => by exact_mod_cast hvalue (y ((), .inr i)))
  apply (Real.lt_log_iff_exp_lt hp).mp
  rw [Real.log_prod (fun i _ => by exact_mod_cast (hvalue (y ((), .inr i))).ne')]
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingTreeWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original half-list weights through the complete moving tree -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialMovingRealWeight_cast {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    (initialMovingRealWeight value b d r cb cd sl sr y : ℂ) =
      initialMovingCutoffWeight value b d r cb cd sl sr y := by
  exact Complex.ofReal_mul _ _

theorem initialMovingDataCutoff_factor {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    {n : ℕ} (T : MovingSlotData P n) (s : ℤ) :
    initialMovingDataCutoff value b d r cb cd sl sr fallback T s =
      (initialMovingRealWeight value b d r cb cd sl sr
        (initialRegularFromList b r fallback T.regularSlots) : ℂ) *
        (if s = 0 then 0 else 1) := by
  rw [initialMovingRealWeight_cast]
  unfold initialMovingDataCutoff
  split_ifs <;> simp only [mul_zero, mul_one]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingBulkLists
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two actual half-bulk cutoffs are independent of restored small slots -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialRegularFromList_bulk {P : Type*} (b r : ℕ) (fallback : P)
    (small : List P) (hsmall : small.length = r + r)
    (bulk : Fin (b + b) → P) (i : Fin (b + b)) :
    initialRegularFromList b r fallback (small ++ List.ofFn bulk) ((), .inr i) = bulk i := by
  let y : MovingRegularSlot 0 (r + r) (b + b) → P :=
    fun j => Sum.elim (fun z => small.get (Fin.cast hsmall.symm z)) bulk j.2
  have hlist : (movingTemplateSlotList 0 (r + r) (b + b)).map y =
      small ++ List.ofFn bulk := by
    simp only [movingTemplateSlotList, movingTemplateSmall, bulkSlotLeaves,
      treeLeafTupleEquiv, Equiv.coe_fn_symm_mk, flattenMovingSlots, List.map_append,
      List.map_ofFn, Function.comp_def, y, movingTemplateBulk, Sum.elim_inl,
      ]
    congr 1
    exact (List.ofFn_congr hsmall small.get).symm.trans (List.ofFn_get small)
  have h := congrFun (initialRegularFromList_mapped b r fallback y) ((), .inr i)
  simpa only [hlist, y, Sum.elim_inr] using h

theorem initialMovingRealWeight_list {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (small : List P) (hsmall : small.length = r + r) (bulk : Fin (b + b) → P) :
    initialMovingRealWeight value b d r cb cd sl sr
      (initialRegularFromList b r fallback (small ++ List.ofFn bulk)) =
      initialHalfBulkWeight value b d cb cd sl sr bulk := by
  unfold initialMovingRealWeight initialHalfBulkWeight
  simp only [initialRegularFromList_bulk b r fallback small hsmall bulk]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingBulkTree
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal two half-bulk weights through every moving branch -/
namespace Ostmann
open scoped Classical BigOperators

theorem moving_append_length_eq {P : Type*} (n : ℕ)
    (x y : TreeLeafTuple (List P) n) (a b : ℕ)
    (hx : MovingLeafLengthEq n x a) (hy : MovingLeafLengthEq n y b) :
    MovingLeafLengthEq n (appendMovingSlotLeaves n x y) (a + b) := by
  induction n with
  | zero => exact (List.length_append).trans (congrArg₂ (· + ·) hx hy)
  | succ n ih => exact ⟨ih x.1 y.1 hx.1 hy.1, ih x.2 y.2 hx.2 hy.2⟩

theorem moving_compensation_length_eq {P : Type*} (n : ℕ)
    (samples : TreeLeafTuple (Fin 4 → P) n) :
    MovingLeafLengthEq n (movingCompensationSlots n samples) 4 := by
  induction n with
  | zero => exact List.length_ofFn
  | succ n ih => exact ⟨ih samples.1, ih samples.2⟩

theorem initialMovingTreeWeight_sample {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (n s : ℕ) (t : FrequencyTree ℤ n) (small : TreeLeafTuple (List P) n)
    (slot : TreeLeafIndex n × Fin (b + b) → P) (a : MovingSampleSlots P n)
    (hsmall : MovingLeafLengthEq n small s) (hlen : s + 4 * n = r + r) :
    initialMovingTreeWeight value b d r cb cd sl sr fallback
      (buildMovingSlotData n t small (bulkSlotLeaves n (b + b) slot) a) =
      initialHalfBulkProduct value b d cb cd sl sr n slot := by
  induction a generalizing s with
  | leaf =>
    change initialMovingRealWeight value b d r cb cd sl sr
      (initialRegularFromList b r fallback ((show List P from small) ++ List.ofFn (fun i => slot ((), i)))) = _
    exact initialMovingRealWeight_list value b d r cb cd sl sr fallback small
      (hsmall.trans (by omega)) _
  | @node n samples left right ihL ihR =>
    have hl : 4 + s + 4 * n = r + r := by omega
    change initialMovingTreeWeight value b d r cb cd sl sr fallback
        (buildMovingSlotData n t.2.1
          (appendMovingSlotLeaves n (movingCompensationSlots n samples) small.1)
          (bulkSlotLeaves n (b + b) (fun j => slot (.inl j.1, j.2))) left) *
      initialMovingTreeWeight value b d r cb cd sl sr fallback
        (buildMovingSlotData n t.2.2
          (appendMovingSlotLeaves n (movingCompensationSlots n samples) small.2)
          (bulkSlotLeaves n (b + b) (fun j => slot (.inr j.1, j.2))) right) = _
    rw [ihL _ _ _ _ (moving_append_length_eq n _ _ 4 s
      (moving_compensation_length_eq n samples) hsmall.1) hl,
      ihR _ _ _ _ (moving_append_length_eq n _ _ 4 s
        (moving_compensation_length_eq n samples) hsmall.2) hl]
    rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialHalfBulkProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lower product bounds for the two genuine half-bulk cutoffs -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialHalfBulkWeight_product_lower {P : Type*} (value : P → ℕ)
    (hvalue : ∀ p, 0 < value p) (b d : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (bulk : Fin (b + b) → P)
    (h : initialHalfBulkWeight value b d cb cd sl sr bulk ≠ 0) :
    Real.exp (2 * cb - 2) ≤ ((∏ i, value (bulk i) : ℕ) : ℝ) := by
  let y : MovingRegularSlot 0 (0 + 0) (b + b) → P :=
    fun j => Sum.elim Fin.elim0 bulk j.2
  have he : (initialHalfBulkWeight value b d cb cd sl sr bulk : ℂ) =
      initialMovingCutoffWeight value b d 0 cb cd sl sr y := by
    exact Complex.ofReal_mul _ _
  have hh : initialMovingCutoffWeight value b d 0 cb cd sl sr y ≠ 0 := by
    rw [← he]
    exact Complex.ofReal_ne_zero.mpr h
  have hl := initialMovingCutoffWeight_bulk_product_lower value hvalue b d 0 cb cd sl sr y hh
  exact le_of_lt (by simpa only [y, Sum.elim_inr, Nat.cast_prod] using hl)

theorem initialHalfBulkProduct_product_lower {P : Type*} (value : P → ℕ)
    (hvalue : ∀ p, 0 < value p) (b d : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (n : ℕ) (slot : TreeLeafIndex n × Fin (b + b) → P)
    (h : initialHalfBulkProduct value b d cb cd sl sr n slot ≠ 0) :
    Real.exp ((2 ^ n : ℕ) * (2 * cb - 2)) ≤ ((∏ j, value (slot j) : ℕ) : ℝ) := by
  induction n with
  | zero =>
    have hl := initialHalfBulkWeight_product_lower value hvalue b d cb cd sl sr
      (fun i => slot ((), i)) h
    have hp := Fintype.prod_prod_type (fun j : Unit × Fin (b + b) => value (slot j))
    simp only [Fintype.prod_unique] at hp
    rw [pow_zero, Nat.cast_one, one_mul]
    change Real.exp (2 * cb - 2) ≤ ↑(∏ j : Unit × Fin (b + b), value (slot j))
    simp only [finite_univ_canonical] at hp hl ⊢
    rw [hp]
    exact hl
  | succ n ih =>
    have hL := ih (fun j => slot (.inl j.1, j.2)) (left_ne_zero_of_mul h)
    have hR := ih (fun j => slot (.inr j.1, j.2)) (right_ne_zero_of_mul h)
    have he : Real.exp ((2 ^ (n + 1) : ℕ) * (2 * cb - 2)) =
        Real.exp ((2 ^ n : ℕ) * (2 * cb - 2)) * Real.exp ((2 ^ n : ℕ) * (2 * cb - 2)) := by
      rw [← Real.exp_add, pow_succ, Nat.cast_mul, Nat.cast_ofNat]
      congr 1
      ring
    rw [he]
    convert mul_le_mul hL hR (Real.exp_nonneg _) (Nat.cast_nonneg _) using 1
    all_goals try with_reducible_and_instances rfl
    rw [← Nat.cast_mul]
    congr 1
    have hp := Fintype.prod_prod_type
      (fun j : (TreeLeafIndex n ⊕ TreeLeafIndex n) × Fin (b + b) => value (slot j))
    have hs := Fintype.prod_sum_type
      (fun j : TreeLeafIndex n ⊕ TreeLeafIndex n => ∏ i : Fin (b + b), value (slot (j, i)))
    have hpL := Fintype.prod_prod_type
      (fun j : TreeLeafIndex n × Fin (b + b) => value (slot (.inl j.1, j.2)))
    have hpR := Fintype.prod_prod_type
      (fun j : TreeLeafIndex n × Fin (b + b) => value (slot (.inr j.1, j.2)))
    simp only [finite_univ_canonical] at hp hs hpL hpR ⊢
    exact hp.trans (hs.trans (congrArg₂ (· * ·) hpL.symm hpR.symm))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingRecursiveWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Factoring terminal bulk weights from the original recursion -/

namespace Ostmann
open scoped Classical ComplexConjugate

/-- The logarithmic bulk cutoffs are independent of every reconstructed
pivot and survive the right-branch conjugations unchanged. -/
theorem movingSlotWeight_initial_halves {σ : Type*} (value : σ → ℕ) (b d r : ℕ) (cb cd : ℝ)
    (sl sr : Fin d → σ) (fallback : σ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (cutoff : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) (t : FrequencyTree ℤ n) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => (initialMovingRealWeight value b d r cb cd sl sr
          (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) * F x s)
        cutoff n ⟨n, T, XL, XR⟩ t =
      (initialMovingTreeWeight value b d r cb cd sl sr fallback T : ℂ) *
        recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
          F cutoff n ⟨n, T, XL, XR⟩ t := by
  induction T generalizing XL XR with
  | leaf => rfl
  | @node n s CL CR U left right ihL ihR =>
    simp only [recursiveTransferWeight]
    split_ifs
    · simp only [movingSlotSystem, MovingSlotState.child, ite_true, if_true,
        Bool.false_eq_true, ite_false, if_false] at ihL ihR ⊢
      rw [ihL, ihR]
      simp only [initialMovingTreeWeight,
        Complex.ofReal_mul, star_mul, Complex.star_def, Complex.conj_ofReal]
      ring
    · exact (mul_zero _).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingCoefficientFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact half-bulk factorization under the unchanged compensation law -/
namespace Ostmann
open scoped Classical BigOperators

theorem movingSupportedSampleTerm_initial_halves {P : Type}
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState P → ℤ → ℂ) (E : MovingSlotState P → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List P) n)
    (XL XR : ℕ) (a : MovingSampleSlots P n) :
    movingSupportedSampleTerm value outside childBound pivotBound
      (fun x s => (initialMovingRealWeight value b d r cb cd sl sr
        (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) * F x s)
      E n t small bulk XL XR a =
    (initialMovingTreeWeight value b d r cb cd sl sr fallback
      (buildMovingSlotData n t small bulk a) : ℂ) *
      movingSupportedSampleTerm value outside childBound pivotBound F E n t small bulk XL XR a := by
  unfold movingSupportedSampleTerm
  rw [movingSlotWeight_initial_halves]
  unfold movingSupportedWeight
  split_ifs
  · rfl
  · exact (mul_zero _).symm

theorem movingSupportedSampledWeight_initial_halves {P : Type} [Fintype P]
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState P → ℤ → ℂ) (E : MovingSlotState P → ℤ → ℤ → ℤ → ℝ)
    (n s : ℕ) (t : FrequencyTree ℤ n) (small : TreeLeafTuple (List P) n)
    (slot : TreeLeafIndex n × Fin (b + b) → P)
    (hsmall : MovingLeafLengthEq n small s) (hlen : s + 4 * n = r + r)
    (XL XR : ℕ) :
    movingSupportedSampledWeight value outside μ childBound pivotBound
      (fun x s => (initialMovingRealWeight value b d r cb cd sl sr
        (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) * F x s)
      E n t small (bulkSlotLeaves n (b + b) slot) XL XR =
    (initialHalfBulkProduct value b d cb cd sl sr n slot : ℂ) *
      movingSupportedSampledWeight value outside μ childBound pivotBound F E n t small
        (bulkSlotLeaves n (b + b) slot) XL XR := by
  rw [movingSupportedSampledWeight_eq, movingSupportedSampledWeight_eq]
  unfold movingCompensatedAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [movingSupportedSampleTerm_initial_halves,
    initialMovingTreeWeight_sample value b d r cb cd sl sr fallback n s t small slot a hsmall hlen]
  ring

theorem movingFrequencyCoefficient_initial_halves {P : Type} [Fintype P]
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState P → ℤ → ℂ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n a : ℕ) (s : ℤ) (small : TreeLeafTuple (List P) n)
    (slot : TreeLeafIndex n × Fin (b + b) → P)
    (hsmall : MovingLeafLengthEq n small a) (hlen : a + 4 * n = r + r)
    (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V
      (fun x s => (initialMovingRealWeight value b d r cb cd sl sr
        (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) * F x s)
      φ G n s small (bulkSlotLeaves n (b + b) slot) XL XR =
    (initialHalfBulkProduct value b d cb cd sl sr n slot : ℂ) *
      movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n s small
        (bulkSlotLeaves n (b + b) slot) XL XR := by
  unfold movingFrequencyCoefficient
  simp only [movingSupportedSampledWeight_initial_halves value b d r cb cd sl sr fallback
    outside μ childBound pivotBound F _ n a _ small slot hsmall hlen XL XR, Finset.mul_sum]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingOriginalFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Factoring the genuine half-list weights in the original Fourier coefficient -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingOriginalLeaf_initial_halves {P I : Type}
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (x : MovingSlotState P) (s : ℤ) :
    movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
      g Dq S ψ X lo hi x s =
    (initialMovingRealWeight value b d r cb cd sl sr
      (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) *
      movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1) g Dq S ψ X lo hi x s := by
  unfold movingOriginalLeaf movingWindowLeaf movingDataLeaf
  dsimp only
  rw [initialMovingDataCutoff_factor]
  split_ifs <;> ring

theorem movingFrequencyCoefficient_original_initial_halves {P I : Type} [Fintype P]
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n a : ℕ) (s : ℤ)
    (small : TreeLeafTuple (List P) n) (slot : TreeLeafIndex n × Fin (b + b) → P)
    (hsmall : MovingLeafLengthEq n small a) (hlen : a + 4 * n = r + r) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G n s small (bulkSlotLeaves n (b + b) slot) XL XR =
    (initialHalfBulkProduct value b d cb cd sl sr n slot : ℂ) *
      movingFrequencyCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1) g Dq S ψ X lo hi)
        φ G n s small (bulkSlotLeaves n (b + b) slot) XL XR := by
  have he : movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
      g Dq S ψ X lo hi = fun x s =>
      (initialMovingRealWeight value b d r cb cd sl sr
        (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) *
      movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1) g Dq S ψ X lo hi x s := by
    funext x s
    exact movingOriginalLeaf_initial_halves value b d r cb cd sl sr fallback q g Dq S ψ X lo hi x s
  rw [he]
  exact movingFrequencyCoefficient_initial_halves value b d r cb cd sl sr fallback outside μ
    childBound pivotBound V _ φ G n a s small slot hsmall hlen XL XR

theorem movingFrequencyCoefficient_original_initial_product_lower {P I : Type} [Fintype P]
    (value : P → ℕ) (hvalue : ∀ p, 0 < value p)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n a : ℕ) (s : ℤ)
    (small : TreeLeafTuple (List P) n) (slot : TreeLeafIndex n × Fin (b + b) → P)
    (hsmall : MovingLeafLengthEq n small a) (hlen : a + 4 * n = r + r) (XL XR : ℕ)
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G n s small (bulkSlotLeaves n (b + b) slot) XL XR ≠ 0) :
    Real.exp ((2 ^ n : ℕ) * (2 * cb - 2)) ≤ ((∏ j, value (slot j) : ℕ) : ℝ) := by
  rw [movingFrequencyCoefficient_original_initial_halves value b d r cb cd sl sr fallback
    q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G n a s small slot hsmall hlen XL XR] at h
  apply initialHalfBulkProduct_product_lower value hvalue b d cb cd sl sr n slot
  exact Complex.ofReal_ne_zero.mp (left_ne_zero_of_mul h)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingTemplateProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic product bounds from the literal two-half initial weights -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingLeafLengthEq_map {P Q : Type*} (f : P → Q) (n : ℕ)
    (x : TreeLeafTuple (List P) n) (a : ℕ) (hx : MovingLeafLengthEq n x a) :
    MovingLeafLengthEq n (treeLeafMap (List.map f) n x) a := by
  induction n with
  | zero => simpa only [MovingLeafLengthEq, treeLeafMap, List.length_map] using hx
  | succ n ih => exact ⟨ih x.1 hx.1, ih x.2 hx.2⟩

theorem bulkSlotLeaves_length_eq {P : Type*} (n m : ℕ)
    (slot : TreeLeafIndex n × Fin m → P) :
    MovingLeafLengthEq n (bulkSlotLeaves n m slot) m := by
  induction n with
  | zero => exact List.length_ofFn
  | succ n ih =>
    change MovingLeafLengthEq n (bulkSlotLeaves n m (fun j => slot (.inl j.1, j.2))) m ∧
      MovingLeafLengthEq n (bulkSlotLeaves n m (fun j => slot (.inr j.1, j.2))) m
    exact ⟨ih _, ih _⟩

theorem movingTemplateCoefficient_original_initial_bulk_lower {P I : Type} [Fintype P]
    (value : P → ℕ) (hvalue : ∀ p, 0 < value p)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n a : ℕ) (s : ℤ)
    (y : MovingRegularSlot n a (b + b) → P) (hlen : a + 4 * n = r + r) (XL XR : ℕ)
    (h : movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G n a (b + b) s y XL XR ≠ 0) :
    Real.exp ((2 ^ n : ℕ) * (2 * cb - 2)) ≤
      ((∏ j : TreeLeafIndex n × Fin (b + b), value (y (j.1, .inr j.2)) : ℕ) : ℝ) := by
  unfold movingTemplateCoefficient at h
  rw [bulkSlotLeaves_map] at h
  exact movingFrequencyCoefficient_original_initial_product_lower value hvalue b d r cb cd sl sr
    fallback q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G n a s _ _
    (movingLeafLengthEq_map y n _ a (bulkSlotLeaves_length_eq n a _)) hlen XL XR h

theorem movingTemplateCoefficient_original_initial_full_lower {P I : Type} [Fintype P]
    (value : P → ℕ) (hvalue : ∀ p, 0 < value p)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n a : ℕ) (s : ℤ)
    (u : TreeLeafIndex n × Fin 4 → P) (y : MovingRegularSlot n a (b + b) → P)
    (hlen : 4 + a + 4 * n = r + r)
    (lower : TreeLeafIndex n × Fin a → ℝ)
    (hlower : ∀ j, Real.exp (lower j) ≤ (value (y (j.1, .inl j.2)) : ℝ)) (XL XR : ℕ)
    (h : movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G n (4 + a) (b + b) s
          (movingRestoreSample n a (b + b) u y) XL XR ≠ 0) :
    Real.exp ((∑ j, lower j) + (2 ^ n : ℕ) * (2 * cb - 2)) ≤
      ((∏ i, value (y i) : ℕ) : ℝ) := by
  have hb := movingTemplateCoefficient_original_initial_bulk_lower value hvalue b d r cb cd sl sr
    fallback q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G n (4 + a) s
    (movingRestoreSample n a (b + b) u y) hlen XL XR h
  have he : (∏ j : TreeLeafIndex n × Fin (b + b),
      value (movingRestoreSample n a (b + b) u y (j.1, .inr j.2))) =
      ∏ j : TreeLeafIndex n × Fin (b + b), value (y (j.1, .inr j.2)) := by
    apply Finset.prod_congr rfl
    intro j _
    change value (movingRestoreSample n a (b + b) u y
      (movingTemplateBulk n (4 + a) (b + b) j)) = _
    rw [movingRestoreSample_bulk]
    rfl
  rw [he] at hb
  have hs := movingTemplate_small_product_lower value n a (b + b) y lower hlower
  rw [Real.exp_add]
  convert mul_le_mul hs hb (Real.exp_nonneg _) (Nat.cast_nonneg _) using 1
  all_goals try with_reducible_and_instances rfl
  rw [← Nat.cast_mul]
  congr 1
  simp only [MovingRegularSlot, Fintype.prod_prod_type, Fintype.prod_sum_type,
    Finset.prod_mul_distrib]

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedCompensationPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual selected compensation cells as one common prime-space prior -/
namespace Ostmann
open scoped Classical BigOperators

/-- This support bound is valid at every index, including unused indices.
It therefore supplies the recursive cap without any tail-of-list premise. -/
theorem selectedCompensationPrior_lower (A B : Set ℕ) (N : ℕ) (X : ℝ)
    (hi : ℕ) (D P : Finset ℕ) (centers : List ℕ) (n : ℕ) (q : P)
    (hq : selectedCompensationPrior A B N X hi D P centers n q ≠ 0) :
    Real.exp (selectedCompensationCenter centers n - 1) ≤ (q : ℝ) := by
  have hp := primeSubsetPrior_support P _ q hq
  have hc := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hp).1).1
  have hb := (mem_primeLogCellSet_iff.mp hc).2.2.1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (mem_primeLogCellSet_iff.mp hc).1.pos
  have he := (Real.lt_log_iff_exp_lt hq0).mp hb
  simpa only [selectedCompensationCenter, add_sub_cancel_right] using he.le

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

theorem scheduledRegularPrior_restore {A : Type} (cell : ℕ → A → ℝ)
    (bulk : A → ℝ) (top c : ℕ) (cs : List ℕ) (n m : ℕ) :
    scheduledRegularPrior cell bulk top (c :: cs) n m =
      movingTemplateRestoredPrior n (scheduledSmallLength cs) m (cell c)
        (scheduledRegularPrior cell bulk top cs n m) := by
  funext i
  rcases i with ⟨j, i | i⟩
  · refine Fin.addCases (fun t => ?_) (fun t => ?_) i
    · simp only [scheduledRegularPrior, scheduledSmallCell, movingTemplateRestoredPrior,
        movingReverseTemplate, Equiv.coe_fn_symm_mk, Sum.elim_inl, Fin.addCases_left]
      exact congrArg cell (Fin.append_left _ _ t)
    · simp only [scheduledRegularPrior, scheduledSmallCell, movingTemplateRestoredPrior,
        movingReverseTemplate, Equiv.coe_fn_symm_mk, Sum.elim_inl, Sum.elim_inr,
        Fin.addCases_right]
      exact congrArg cell (Fin.append_right _ _ t)
  · rfl

theorem drop_eq_headD_cons {A : Type} (cs : List A) (fallback : A) (n : ℕ)
    (hn : n < cs.length) :
    cs.drop n = (cs.drop n).headD fallback :: cs.drop (n + 1) := by
  induction cs generalizing n with
  | nil => simp at hn
  | cons c cs ih =>
    cases n with
    | zero => simp
    | succ n =>
      simpa only [List.drop_succ_cons] using ih n (by simpa using hn)

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

theorem completedCompensationPrior_used (A B : Set ℕ) (N : ℕ) (X : ℝ)
    (hi : ℕ) (D P : Finset ℕ) (top : ℕ) (cs : List ℕ) (n : ℕ) (hn : n < cs.length) :
    completedCompensationPrior A B N X hi D P top cs n =
      selectedCompensationPrior A B N X hi D P cs n := by
  unfold completedCompensationPrior completedCompensationSets selectedCompensationPrior
  rw [completedCompensationCell_used top cs n hn]

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

theorem completedCompensationPrior_lower (A B : Set ℕ) (N : ℕ) (X : ℝ)
    (hi : ℕ) (D P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (top : ℕ) (cs : List ℕ) (n : ℕ) (q : P)
    (hq : completedCompensationPrior A B N X hi D P top cs n q ≠ 0) :
    Real.exp (selectedCompensationCenter cs n - 1) ≤ (q : ℝ) := by
  by_cases hn : n < cs.length
  · rw [completedCompensationPrior_used A B N X hi D P top cs n hn] at hq
    exact selectedCompensationPrior_lower A B N X hi D P cs n q hq
  · have he : selectedCompensationCenter cs n = 1 := by
      simp only [selectedCompensationCenter, List.drop_eq_nil_of_le (Nat.le_of_not_gt hn),
        List.headD_nil, Nat.cast_zero, zero_add]
    rw [he, sub_self, Real.exp_zero]
    exact_mod_cast (hP q q.property).one_le

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual amplitudes along the shrinking compensation list -/
namespace Ostmann
open scoped Classical BigOperators

theorem scheduledCellAmplitude_restore {A : Type} [Fintype A]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState A → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Pg : Finset ℕ) (ρ : Pg → ℝ)
    (cell : ℕ → A → ℝ) (bulk : A → ℝ) (top : ℕ) (cs : List ℕ) (n m : ℕ)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool)
    (hn : n < cs.length) (hμ : μ n = cell ((cs.drop n).headD 0)) :
    let r := scheduledSmallLength (cs.drop (n + 1))
    let ν := scheduledRegularPrior cell bulk top (cs.drop (n + 1)) n m
    scheduledCellAmplitude value outside μ childBound pivotBound V F φ G Pg ρ
      cell bulk top cs n m greg ggiant favorable =
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G n (4 + r) m
      Pg ρ (movingTemplateRestoredPrior n r m (μ n) ν) greg ggiant favorable := by
  intro r ν
  unfold scheduledCellAmplitude
  conv_lhs => rw [drop_eq_headD_cons cs 0 n hn, scheduledRegularPrior_restore]
  rw [hμ]
  rfl

theorem scheduledCellAmplitude_next {A : Type} [Fintype A]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState A → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Pg : Finset ℕ) (ρ : Pg → ℝ)
    (cell : ℕ → A → ℝ) (bulk : A → ℝ) (top : ℕ) (cs : List ℕ) (n m : ℕ)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) :
    let r := scheduledSmallLength (cs.drop (n + 1))
    let ν := scheduledRegularPrior cell bulk top (cs.drop (n + 1)) n m
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G (n + 1) r m
      Pg ρ (movingTemplateDoubledPrior n r m ν) greg ggiant favorable =
    scheduledCellAmplitude value outside μ childBound pivotBound V F φ G Pg ρ
      cell bulk top cs (n + 1) m greg ggiant favorable := rfl

theorem completedCompensationPrior_cell (A B : Set ℕ) (N : ℕ) (X : ℝ)
    (hi : ℕ) (D P : Finset ℕ) (top : ℕ) (cs : List ℕ) (n : ℕ) (hn : n < cs.length) :
    completedCompensationPrior A B N X hi D P top cs n =
      primeSubsetPrior P (selectedTailCellPrimes A B N X hi D ((cs.drop n).headD 0)) := by
  exact completedCompensationPrior_used A B N X hi D P top cs n hn

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedCompensationFrequency
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected compensation list supplies the actual frequency-budget data -/
namespace Ostmann
open scoped Classical BigOperators

private theorem headD_drop_get {α : Type*} (xs : List α) (fallback : α)
    (n : ℕ) (hn : n < xs.length) :
    (xs.drop n).headD fallback = xs.get ⟨n, hn⟩ := by
  induction xs generalizing n with
  | nil => simp at hn
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simpa only [List.drop_succ_cons, List.get_cons_succ] using ih n (by simpa using hn)

theorem selectedCompensation_pivot_error
    {A B : Set ℕ} {N hi : ℕ} {a C L X : ℝ} {D : Finset ℕ}
    {centers : List ℕ} {targets : List ℝ}
    (h : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) centers targets)
    (n : ℕ) (hn : n < targets.length)
    (G : ℝ) :
    |movingCellPivotExponent (fun _ => G) (selectedCompensationCenter centers) n -
      movingTargetPivotExponent G targets n| ≤
        (2 : ℝ) ^ n * (256 * tailDefectBudget a C X + 9) := by
  have hnc : n < centers.length := by rw [h.length_eq]; exact hn
  have hc := h.get hnc hn
  rw [← headD_drop_get centers 0 n hnc, ← headD_drop_get targets 0 n hn] at hc
  have hlo := hc.1
  have hhi := hc.2.1
  have hD : 0 ≤ 64 * tailDefectBudget a C X + 1 := by linarith
  have hr : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hr0 : 0 ≤ (2 : ℝ) ^ n := by positivity
  have hlow := mul_le_mul_of_nonneg_left hlo hr0
  have hupp := mul_le_mul_of_nonneg_left hhi hr0
  have hbudget := mul_le_mul_of_nonneg_left hD hr0
  simp only [movingCellPivotExponent, selectedCompensationCenter, movingTargetPivotExponent,
    add_sub_cancel_right, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  exact abs_le.mpr ⟨by nlinarith only [hlow, hbudget, hr], by nlinarith only [hupp, hr]⟩

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

theorem selected_scheduled_rigidity_margin
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y G cb cd width Dlog Bs BD Bz : ℝ}
    {D : Finset ℕ} {cs : List ℕ} (k n : ℕ) (hn : n < k)
    (hk : 1 ≤ k) (hm : 64 ≤ (spectatorBulkCount k L : ℝ))
    (hD : Dlog ≤ 2 * cd + 2)
    (herror : 256 * tailDefectBudget a C Y + 9 ≤ (spectatorBulkCount k L : ℝ) / 40)
    (hBD : Bs + 1 ≤ BD) (hBz : 8 ≤ Bz)
    (hcs : List.Forall₂
      (fun j t => SelectedSmallTailCell A B N a C L Y hi D (t / 4) j)
      cs (movingCompensationTargets
        (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
        (movingCompensationGaps k BD Bz L))) :
    let m : ℝ := spectatorBulkCount k L
    let T := movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs)
    let W := Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog
    (1 / 20 : ℝ) * (2 : ℝ) ^ n * m ≤
      (movingProductExponent T W n - 2 * T n) -
        movingProductFrequencyExponent T W (Y - Dlog) (m / 4) n := by
  intro m T W
  let J := movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L)
  have htotal := moving_protected_and_compensation_total k BD Bz L Y G cd
    (spectatorBaseGap Bs ((k : ℝ) ^ 4) m)
  have hbase : 2 * G + J +
      (movingCompensationTargets J (movingCompensationGaps k BD Bz L)).sum - (Y - 2 * cd) =
      spectatorBaseGap Bs ((k : ℝ) ^ 4) m := by
    change 2 * G + 2 * cd + J +
      (movingCompensationTargets J (movingCompensationGaps k BD Bz L)).sum = _ at htotal
    linarith only [htotal]
  have herr := (abs_le.mp (selectedCompensation_pivot_error hcs n
    (by simpa only [movingCompensationTargets_length, movingCompensationGaps_length] using hn) G)).2
  have hideal := movingProductFrequency_prescribed_margin G J (Y - 2 * cd) Bs BD Bz L k n hn
    T W (256 * tailDefectBudget a C Y + 9) hbase
    (by dsimp only [T, J]; linarith only [herr]) herror hBD hBz
    (one_le_pow₀ (by exact_mod_cast hk)) hm
  rw [movingProductFrequency_gap] at hideal ⊢
  have hroot := Real.sqrt_le_sqrt (show 4 * (m / 4) ≤ 4 * m by dsimp only [m] at *; linarith only [hm])
  have hr : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hr0 : 0 ≤ (2 : ℝ) ^ n := by positivity
  have hs := mul_le_mul_of_nonneg_left hroot hr0
  have hreserve := mul_le_mul_of_nonneg_left hm hr0
  nlinarith only [hideal, hs, hD, hr, hreserve]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledIntegerRigidity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual product separation on the retained initial-coefficient support -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem scheduledPivotBound_upper (G width : ℝ) (cs : List ℕ) (n : ℕ)
    (hG : 1 ≤ G) (hwidth : 0 ≤ width) :
    (scheduledPivotBound G cs n : ℝ) ≤
      Real.exp (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n +
        scheduledProductRounding width cs n) := by
  let T := movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n
  let Z := G + 1 + (2 : ℝ) ^ n * 4 * (((cs.drop n).headD 0 : ℝ) + 1)
  have hr : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hZ : 0 ≤ Z := by
    dsimp only [Z]
    positivity
  have hceil : (scheduledPivotBound G cs n : ℝ) ≤ 2 * Real.exp Z := by
    have hh := (Nat.ceil_lt_add_one (Real.exp_nonneg Z)).le
    have hz := Real.one_le_exp hZ
    change (⌈Real.exp Z⌉₊ : ℝ) ≤ _
    linarith
  have hlog : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hmargin : Real.log 2 + Z ≤ T + scheduledProductRounding width cs n := by
    dsimp only [T, Z, scheduledProductRounding]
    rw [selected_cell_pivot_exponent]
    have hw := mul_nonneg (show 0 ≤ (2 : ℝ) ^ n by positivity) hwidth
    have hl := mul_nonneg (show 0 ≤ (2 : ℝ) ^ n by positivity)
      (Nat.cast_nonneg cs.length (α := ℝ))
    nlinarith only [hlog, hr, hw, hl]
  apply hceil.trans
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
  exact Real.exp_le_exp.mpr hmargin

theorem scheduled_retained_product_exponent (G Y cb cd width Dlog : ℝ)
    (top : ℕ) (cs : List ℕ) (n : ℕ) :
    movingProductExponent (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
        (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) n -
      movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n -
      (G - 1 + (∑ i, scheduledSmallLower top (cs.drop (n + 1)) n i) +
        (2 : ℝ) ^ n * (2 * cb - 2)) =
      (2 : ℝ) ^ n * (2 * cd - Dlog + width + 10 + 4 * (cs.drop (n + 1)).length) := by
  rw [selectedProductExponent_eq, selected_cell_pivot_exponent, nat_cell_drop_sum cs n,
    scheduledSmallLower_sum]
  have hs := list_sum_sub_one ((cs.drop (n + 1)).map (fun j : ℕ => (j : ℝ)))
  simp only [List.map_map, Function.comp_def, List.length_map] at hs
  rw [hs]
  push_cast
  ring

theorem scheduled_retained_product_rounding (G Y cb cd width Dlog : ℝ)
    (top : ℕ) (cs : List ℕ) (n : ℕ) (hD : 2 * cd - 2 ≤ Dlog) :
    movingProductExponent (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
        (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) n -
      movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n -
      scheduledProductRounding width cs n ≤
      G - 1 + (∑ i, scheduledSmallLower top (cs.drop (n + 1)) n i) +
        (2 : ℝ) ^ n * (2 * cb - 2) := by
  have he := scheduled_retained_product_exponent G Y cb cd width Dlog top cs n
  have hlen : ((cs.drop (n + 1)).length : ℝ) ≤ cs.length := by
    exact_mod_cast (show (cs.drop (n + 1)).length ≤ cs.length by simp only [List.length_drop]; omega)
  have hr : 0 ≤ (2 : ℝ) ^ n := by positivity
  have hh := mul_le_mul_of_nonneg_left (show
    2 * cd - Dlog + width + 10 + 4 * (cs.drop (n + 1)).length ≤ width + 14 + 4 * cs.length by
      linarith only [hD, hlen]) hr
  unfold scheduledProductRounding
  linarith only [he, hh]

theorem scheduled_original_retained_product_lower {A I : Type} [Fintype A]
    (value : A → ℕ) (hvalue : ∀ x, 0 < value x)
    (b d top : ℕ) (cs : List ℕ) (cb cd G Y width Dlog : ℝ)
    (sl sr : Fin d → A) (fallback : A)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → A → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (n : ℕ) (hn : n < cs.length)
    (u : TreeLeafIndex n × Fin 4 → A)
    (right : MovingRegularSlot n (scheduledSmallLength (cs.drop (n + 1))) (b + b) → A)
    (p XR : ℕ) (w : ℤ) (hXR : Real.exp (G - 1) ≤ (XR : ℝ))
    (hD : 2 * cd - 2 ≤ Dlog)
    (hlower : ∀ j, Real.exp (scheduledSmallLower top (cs.drop (n + 1)) n j) ≤
      (value (right (j.1, .inl j.2)) : ℝ))
    (hcoeff : movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q
        (initialMovingDataCutoff value b d (initialSmallCellList top cs).length cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ (fun _ => G) n
      (4 + scheduledSmallLength (cs.drop (n + 1))) (b + b) w
      (movingRestoreSample n (scheduledSmallLength (cs.drop (n + 1))) (b + b) u right) p XR ≠ 0) :
    let T := movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs)
    let W := Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog
    Real.exp (movingProductExponent T W n - T n - scheduledProductRounding width cs n) ≤
      ((XR * ∏ i, value (right i) : ℕ) : ℝ) := by
  intro T W
  have hprod := movingTemplateCoefficient_original_initial_full_lower value hvalue b d
    (initialSmallCellList top cs).length cb cd sl sr fallback q g Dq S ψ X lo hi outside μ
    childBound pivotBound V φ (fun _ => G) n (scheduledSmallLength (cs.drop (n + 1))) w
    u right (scheduled_drop_length_balance top cs n hn) _ hlower p XR hcoeff
  have hround := scheduled_retained_product_rounding G Y cb cd width Dlog top cs n hD
  apply (Real.exp_le_exp.mpr hround).trans
  rw [Real.exp_add, Real.exp_add, Nat.cast_mul]
  push_cast at hprod
  simpa only [Real.exp_add, Nat.cast_prod, mul_assoc] using
    mul_le_mul hXR hprod (Real.exp_nonneg _) (Nat.cast_nonneg XR)

theorem scheduled_integer_rigidity (G Y cb cd width Dlog m : ℝ)
    (top : ℕ) (cs : List ℕ) (n R : ℕ)
    (hG : 1 ≤ G) (hwidth : 0 ≤ width)
    (hbudget : 40 * (width + 14 + 4 * cs.length) + 20 * Real.log 2 < m)
    (hR : Real.exp (
      movingProductExponent (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
        (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) n -
      movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n -
      scheduledProductRounding width cs n) ≤ (R : ℝ))
    (hmargin : (1 / 20 : ℝ) * (2 : ℝ) ^ n * m ≤
      (movingProductExponent (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
          (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) n -
        2 * movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n) -
      movingProductFrequencyExponent
        (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
        (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) (Y - Dlog) (m / 4) n) :
    2 * scheduledPivotBound G cs n *
      movingProductNaturalCutoff
        (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
        (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) (Y - Dlog) (m / 4) n < R := by
  apply movingProductNaturalCutoff_rigidity _ _ _ _ (scheduledProductRounding width cs n)
    n (scheduledPivotBound G cs n) R (scheduledPivotBound_upper G width cs n hG hwidth) hR
  have hr : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hr0 : 0 < (2 : ℝ) ^ n := by positivity
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hh := mul_lt_mul_of_pos_left hbudget hr0
  have hl := mul_le_mul_of_nonneg_right hr hlog
  unfold scheduledProductRounding
  nlinarith only [hh, hl, hmargin]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledCompensationBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integer pivot cap bounds the actual selected compensation product -/
namespace Ostmann
open scoped Classical BigOperators

theorem selected_scheduled_pivot_bound
    {A B : Set ℕ} {N hi top : ℕ} {a C L X G : ℝ} {D P : Finset ℕ}
    {cs : List ℕ} {targets : List ℝ}
    (hcs : List.Forall₂ (fun j t => SelectedSmallTailCell A B N a C L X hi D (t / 4) j)
      cs targets) (n : ℕ) (hn : n < cs.length)
    (u : TreeLeafIndex n × Fin 4 → P)
    (hu : (∏ i, completedCompensationPrior A B N X hi D P top cs n (u i)) ≠ 0)
    (p : ℕ) (hp : p ∈ Finset.Ioc ⌊Real.exp (G - 1)⌋₊ ⌊Real.exp (G + 1)⌋₊) :
    p * (∏ i, (u i : ℕ)) ≤ scheduledPivotBound G cs n := by
  have hc := forall₂_headD_drop hcs n hn
  have hprime (i : TreeLeafIndex n × Fin 4) :
      (u i : ℝ) ≤ Real.exp (((cs.drop n).headD 0 : ℝ) + 1) := by
    have hnz := Finset.prod_ne_zero_iff.mp hu i (Finset.mem_univ i)
    rw [completedCompensationPrior_used A B N X hi D P top cs n hn] at hnz
    have hmem := primeSubsetPrior_support P _ (u i) hnz
    exact (hc.2.2.2.2.2.2 _ hmem).2.2.1
  have hprod := Finset.prod_le_prod (fun i (_ : i ∈ Finset.univ) => by positivity :
      ∀ i ∈ Finset.univ, 0 ≤ (u i : ℝ)) (fun i _ => hprime i)
  have hprod' : ((∏ i, (u i : ℕ) : ℕ) : ℝ) ≤
      Real.exp ((2 : ℝ) ^ n * 4 * (((cs.drop n).headD 0 : ℝ) + 1)) := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_prod, card_treeLeafIndex,
      Fintype.card_fin, ← Real.exp_nat_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_prod] using hprod
  have hpFloor : (p : ℝ) ≤ (⌊Real.exp (G + 1)⌋₊ : ℝ) := by
    exact_mod_cast (Finset.mem_Ioc.mp hp).2
  have hp' : (p : ℝ) ≤ Real.exp (G + 1) :=
    hpFloor.trans (Nat.floor_le (Real.exp_nonneg _))
  have htotal := mul_le_mul hp' hprod' (by positivity) (Real.exp_nonneg _)
  rw [← Real.exp_add, ← Nat.cast_mul] at htotal
  have hfinal : ((p * ∏ i, (u i : ℕ) : ℕ) : ℝ) ≤
      (scheduledPivotBound G cs n : ℝ) := htotal.trans (Nat.le_ceil _)
  exact_mod_cast hfinal

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledCoefficientGap
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The true initial cutoffs supply the coefficient-supported transfer gap -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem selected_scheduled_coefficient_gap
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y G cb cd Dlog Bs BD Bz : ℝ}
    {D P Qb : Finset ℕ} {cs : List ℕ} (k n : ℕ) (hn : n < k)
    (hk : 1 ≤ k) (hm : 64 ≤ (spectatorBulkCount k L : ℝ))
    (hP : ∀ p ∈ P, p.Prime) (hG : 1 ≤ G) (hD : |Dlog - 2 * cd| ≤ 2)
    (herror : 256 * tailDefectBudget a C Y + 9 ≤ (spectatorBulkCount k L : ℝ) / 40)
    (hBD : Bs + 1 ≤ BD) (hBz : 8 ≤ Bz)
    (hbudget : 40 * (2 * ((initialSmallCellList top cs).length + 3) + 14 + 4 * cs.length) +
      20 * Real.log 2 < (spectatorBulkCount k L : ℝ))
    (hcs : List.Forall₂
      (fun j t => SelectedSmallTailCell A B N a C L Y hi D (t / 4) j)
      cs (movingCompensationTargets
        (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
        (movingCompensationGaps k BD Bz L)))
    (b d : ℕ) (sl sr : Fin d → P) (fallback : P)
    {I : Type} (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo upper : ℝ) (φ : ℝ → ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound : ℕ → ℕ)
    (u : TreeLeafIndex n × Fin 4 → P)
    (right : MovingRegularSlot n (scheduledSmallLength (cs.drop (n + 1))) (b + b) → P)
    (hright : ∀ i, (right i : ℕ) ∈ scheduledRegularPrimeSets
      (selectedTailCellPrimes A B N Y hi D) Qb top (cs.drop (n + 1)) n (b + b) i)
    (p XR : ℕ) (w : ℤ) (hXR : Real.exp (G - 1) ≤ (XR : ℝ)) :
    let width : ℝ := 2 * ((initialSmallCellList top cs).length + 3)
    let T := movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs)
    let W := Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog
    let V := movingProductNaturalCutoff T W (Y - Dlog) ((spectatorBulkCount k L : ℝ) / 4)
    pivotBound (n + 1) = scheduledPivotBound G cs n →
    childBound (n + 1) = V n →
    movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V
      (movingOriginalLeaf Subtype.val q
        (initialMovingDataCutoff Subtype.val b d (initialSmallCellList top cs).length cb cd sl sr fallback)
        g Dq S ψ X lo upper) φ (fun _ => G) n
      (4 + scheduledSmallLength (cs.drop (n + 1))) (b + b) w
      (movingRestoreSample n (scheduledSmallLength (cs.drop (n + 1))) (b + b) u right) p XR ≠ 0 →
    2 * pivotBound (n + 1) * childBound (n + 1) < XR * (∏ i, (right i : ℕ)) := by
  intro width T W V hpivot hchild hcoeff
  have hlen : cs.length = k := by
    simpa only [movingCompensationTargets_length, movingCompensationGaps_length] using hcs.length_eq
  have hDl : 2 * cd - 2 ≤ Dlog := by linarith only [(abs_le.mp hD).1]
  have hDu : Dlog ≤ 2 * cd + 2 := by linarith only [(abs_le.mp hD).2]
  have hr := scheduled_original_retained_product_lower Subtype.val
    (fun x => (hP _ x.property).pos) b d top cs cb cd G Y width Dlog sl sr fallback
    q g Dq S ψ X lo upper outside μ childBound pivotBound V φ n (by omega) u right p XR w hXR hDl
    (fun j => scheduledSmallLower_prime_bound A B N hi top Y D Qb (cs.drop (n + 1)) n
      (b + b) j _ (hright _)) hcoeff
  have hg := selected_scheduled_rigidity_margin (top := top) (cb := cb) (width := width)
    k n hn hk hm hDu herror hBD hBz hcs
  have hgap := scheduled_integer_rigidity G Y cb cd width Dlog (spectatorBulkCount k L)
    top cs n (XR * ∏ i, (right i : ℕ)) hG (by dsimp only [width]; positivity) hbudget hr hg
  rwa [hpivot, hchild]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledLiveBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frequency separation of the actual scheduled harmonic laws -/
namespace Ostmann
open scoped Classical BigOperators

theorem scheduledRegularPrior_support (A B : Set ℕ) (N hi : ℕ) (X : ℝ)
    (D P Qb : Finset ℕ) (top : ℕ) (cs : List ℕ) (n m : ℕ)
    (i : MovingRegularSlot n (scheduledSmallLength cs) m) (p : P)
    (hp : scheduledRegularPrior
      (fun c => primeSubsetPrior P (selectedTailCellPrimes A B N X hi D c))
      (primeSubsetPrior P Qb) top cs n m i p ≠ 0) :
    (p : ℕ) ∈ scheduledRegularPrimeSets (selectedTailCellPrimes A B N X hi D)
      Qb top cs n m i := by
  rw [scheduledRegularPrior_prime] at hp
  exact primeSubsetPrior_support P _ p hp

theorem selected_scheduled_regular_large
    {A B : Set ℕ} {N hi top : ℕ} {a C L X target : ℝ} {D P Qb : Finset ℕ}
    {cs : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L X hi D target top)
    (hcs : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) cs targets)
    (hL : 0 ≤ L)
    (hlower : ∀ j ∈ initialSmallCellList top cs, Real.exp ((1 / 100 : ℝ) * L) ≤ (j : ℝ))
    (hbulk : Qb ⊆ initialRegularPrimeRange L)
    (hbulklower : ∀ p ∈ Qb, Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (p : ℝ))
    (n m j V : ℕ) (hV : (V : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)))
    (i : MovingRegularSlot n (scheduledSmallLength (cs.drop j)) m) (p : P)
    (hp : scheduledRegularPrior
      (fun c => primeSubsetPrior P (selectedTailCellPrimes A B N X hi D c))
      (primeSubsetPrior P Qb) top (cs.drop j) n m i p ≠ 0) : V < (p : ℕ) := by
  have hm := scheduledRegularPrior_support A B N hi X D P Qb top (cs.drop j) n m i p hp
  have hr := scheduledRegularPrimeSets_range htop hcs hL hlower hbulk hbulklower n m j i p hm
  exact_mod_cast hV.trans_le hr.2

theorem selected_scheduled_compensation_large
    {A B : Set ℕ} {N hi top : ℕ} {a C L X target : ℝ} {D P : Finset ℕ}
    {cs : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L X hi D target top)
    (hcs : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) cs targets)
    (hL : 0 ≤ L)
    (hlower : ∀ j ∈ initialSmallCellList top cs, Real.exp ((1 / 100 : ℝ) * L) ≤ (j : ℝ))
    (n V : ℕ) (hV : (V : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)))
    (p : P) (hp : completedCompensationPrior A B N X hi D P top cs n p ≠ 0) : V < (p : ℕ) := by
  have hm := primeSubsetPrior_support P _ p hp
  have hr := (completedCompensationSets_range htop hcs hlower n p hm).2
  have hb : Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤
      Real.exp (Real.exp ((1 / 100 : ℝ) * L)) := by
    apply Real.exp_le_exp.mpr
    apply Real.exp_le_exp.mpr
    nlinarith only [hL]
  exact_mod_cast (hV.trans_le hb).trans_le hr

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantLiveSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing zero-weight giant labels preserves the full original law -/
namespace Ostmann
open scoped Classical BigOperators

theorem smoothGiantPrior_live_nonzero (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (p : smoothGiantLivePrimes P φ G) :
    smoothGiantPrior (smoothGiantLivePrimes P φ G) φ G p ≠ 0 := by
  apply div_ne_zero
  · exact mul_ne_zero (Real.exp_ne_zero _) (Finset.mem_filter.mp p.property).2
  · exact_mod_cast (hP _ (smoothGiantLivePrimes_subset P φ G p.property)).ne_zero

theorem smoothGiantLivePrimes_bounds (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (p : smoothGiantLivePrimes P φ G) :
    Real.exp (G - 1) < (p : ℝ) ∧ (p : ℝ) < Real.exp (G + 1) :=
  smoothGiantPrior_active_bounds _ (fun q hq => hP q (smoothGiantLivePrimes_subset P φ G hq))
    φ G hout p (smoothGiantPrior_live_nonzero P hP φ G p)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedScheduledTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual selected cells satisfy the original finite transfer step -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap ComplexConjugate

theorem selected_scheduled_amplitude_step
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
    {N hi top : ℕ} {a C L Y G cb cd Dlog Bs BD Bz : ℝ}
    {D P Qb : Finset ℕ} {cs : List ℕ} (k n : ℕ) (hn : n < k) (hk : 1 ≤ k)
    (hP : ∀ p ∈ P, p.Prime) (hambient : initialRegularPrimeRange L ⊆ P)
    (hL : 1 ≤ L) (hY : 0 < Y) (hYupper : Y ≤ Real.exp L)
    (hcell : 1024 * tailCellLinearRate a C + 52 ≤ (k : ℝ) ^ 4)
    (hcount : (8 + 4 * cs.length : ℕ) ≤ L)
    (hm : 256 ≤ (spectatorBulkCount k L : ℝ))
    (hG : 1 ≤ G) (hcb : 0 ≤ cb) (hD : |Dlog - 2 * cd| ≤ 2)
    (hBs : 0 ≤ Bs) (hBD : Bs + 1 ≤ BD) (hBz : 8 ≤ Bz)
    (herror : 256 * tailDefectBudget a C Y + 9 ≤ (spectatorBulkCount k L : ℝ) / 40)
    (hbudget : 40 * (2 * ((initialSmallCellList top cs).length + 3) + 14 + 4 * cs.length) +
      20 * Real.log 2 < (spectatorBulkCount k L : ℝ))
    (htop : SelectedSmallTailCell A B N a C L Y hi D
      ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top)
    (hcs : List.Forall₂
      (fun j t => SelectedSmallTailCell A B N a C L Y hi D (t / 4) j)
      cs (movingCompensationTargets
        (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
        (movingCompensationGaps k BD Bz L)))
    (hlower : ∀ j ∈ initialSmallCellList top cs, Real.exp ((1 / 100 : ℝ) * L) ≤ (j : ℝ))
    (hbulk : Qb ⊆ initialRegularPrimeRange L)
    (hbulklower : ∀ p ∈ Qb, Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (p : ℝ))
    (hdis : ∀ p ∈ P, Disjoint (tailResidues A N p) (negTailResidues B N p))
    (b d : ℕ)
    (sl sr : Fin d → P) (fallback : P)
    {J : Type} (q : J → ℕ) [∀ i, Fact (q i).Prime]
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J)
    (ψ : 𝓢(ℝ, ℂ)) (X lo upper : ℝ) (hX : 0 < X)
    (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (hpos : 0 < smoothGiantMass (smoothGiantPrimeRange G) φ G)
    (outside : List ℕ) (favorable : ℕ → Bool) :
    let width : ℝ := 2 * ((initialSmallCellList top cs).length + 3)
    let T := movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs)
    let W := Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog
    let V := movingProductNaturalCutoff T W (Y - Dlog) ((spectatorBulkCount k L : ℝ) / 4)
    let μ := completedCompensationPrior A B N Y hi D P top cs
    let cell := fun c => primeSubsetPrior P (selectedTailCellPrimes A B N Y hi D c)
    let F := movingOriginalLeaf Subtype.val q
      (initialMovingDataCutoff Subtype.val b d (initialSmallCellList top cs).length cb cd sl sr fallback)
      g Dq S ψ X lo upper
    let ν := scheduledRegularPrior cell (primeSubsetPrior P Qb) top (cs.drop (n + 1)) n (b + b)
    let I := Finset.Ioc ⌊Real.exp (G - 1)⌋₊ ⌊Real.exp (G + 1)⌋₊
    let ρ := smoothGiantPrior (smoothGiantPrimeRange G) φ G
    let greg := normalizedResidueFamily (tailDensityMask A N)
    X * upper ≤ Real.exp W →
    (V (n + 1) : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
    (V (n + 1) : ℝ) < Real.exp (G - 1) →
    Real.exp (-smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G) *
      ‖scheduledCellAmplitude Subtype.val outside μ (scheduledChildBound V)
        (scheduledPivotCaps G cs) V F φ (fun _ => G) (smoothGiantPrimeRange G) ρ
        cell (primeSubsetPrior P Qb) top cs n (b + b) greg greg favorable‖ ^ 2 ≤
      movingAmplitudeDiagonal Subtype.val outside μ (scheduledChildBound V)
        (scheduledPivotCaps G cs) V F φ (fun _ => G) n
        (scheduledSmallLength (cs.drop (n + 1))) (b + b) (smoothGiantPrimeRange G) I
        ρ ν greg greg favorable +
      ‖scheduledCellAmplitude Subtype.val outside μ (scheduledChildBound V)
        (scheduledPivotCaps G cs) V F φ (fun _ => G) (smoothGiantPrimeRange G) ρ
        cell (primeSubsetPrior P Qb) top cs (n + 1) (b + b) greg greg favorable‖ := by
  intro width T W V μ cell F ν I ρ greg hwindow hfreq hgiantfreq
  have hlen : cs.length = k := by
    simpa only [movingCompensationTargets_length, movingCompensationGaps_length] using hcs.length_eq
  have hncs : n < cs.length := by omega
  have hμcell : μ n = cell ((cs.drop n).headD 0) :=
    completedCompensationPrior_cell A B N Y hi D P top cs n hncs
  rw [scheduledCellAmplitude_restore (cs := cs) (n := n) (hn := hncs) (hμ := hμcell),
    ← scheduledCellAmplitude_next]
  have hproduct := selectedProductExponent_budget_of_cells (G := G) (Y := Y) (cd := cd)
    (Dlog := Dlog) (width := width) (BD := BD) (Bz := Bz) k hk
    hL hY hYupper hcell hcount hcb (by linarith only [(abs_le.mp hD).2])
    (show 0 ≤ width by dsimp only [width]; positivity) (by linarith) (by linarith) htop hcs
  change ∀ j, 2 * T j ≤ movingProductExponent T W j at hproduct
  have hpositive : 0 ≤ movingProductExponent T W n - T n := by
    have ht := selected_cell_pivot_nonneg G hG cs n
    change 0 ≤ T n at ht
    linarith [hproduct n]
  have hcenter : 0 ≤ selectedInitialLogCenter G Y cb cd top cs := by
    apply le_trans _ (selected_initial_center_bounds k htop hcs).1
    unfold spectatorBaseGap
    have hz : 0 ≤ Real.log ((k : ℝ) ^ 4) :=
      Real.log_nonneg (one_le_pow₀ (by exact_mod_cast hk))
    positivity
  have hYreg : Y - Dlog ≤ W := by
    have hw : 0 ≤ width := by dsimp only [width]; positivity
    dsimp only [W]
    linarith
  have hμdata := completedCompensationPrior_data htop hcs P hambient n
  have hIlower (p : ℕ) (hp : p ∈ I) : Real.exp (G - 1) ≤ (p : ℝ) :=
    ((Nat.floor_lt (Real.exp_nonneg _)).mp (Finset.mem_Ioc.mp hp).1).le
  have hIpos (p : ℕ) (hp : p ∈ I) : 0 < p := by
    have hh := (Real.exp_pos (G - 1)).trans_le (hIlower p hp)
    exact_mod_cast hh
  have hPglive (p : smoothGiantLivePrimes (smoothGiantPrimeRange G) φ G) :
      (p : ℕ).Prime := smoothGiantPrimeRange_prime G p
        (smoothGiantLivePrimes_subset _ _ _ p.property)
  have hPglarge (p : smoothGiantLivePrimes (smoothGiantPrimeRange G) φ G) :
      V (n + 1) < (p : ℕ) := by
    have hh := smoothGiantLivePrimes_bounds _ (smoothGiantPrimeRange_prime G) φ G hout p
    exact_mod_cast hgiantfreq.trans hh.1
  have hνlarge (i : MovingRegularSlot n (scheduledSmallLength (cs.drop (n + 1))) (b + b))
      (p : P) (hp : ν i p ≠ 0) : V (n + 1) < (p : ℕ) :=
    selected_scheduled_regular_large htop hcs (by linarith) hlower hbulk hbulklower
      n (b + b) (n + 1) (V (n + 1)) hfreq i p hp
  have hμlarge (p : P) (hp : μ n p ≠ 0) : V (n + 1) < (p : ℕ) :=
    selected_scheduled_compensation_large htop hcs (by linarith) hlower n (V (n + 1)) hfreq p hp
  apply movingTemplatePrimeAmplitude_step_full_coefficients Subtype.val
    (fun p => hP p p.property) outside μ (scheduledChildBound V) (scheduledPivotCaps G cs) V
    q (initialMovingDataCutoff Subtype.val b d (initialSmallCellList top cs).length cb cd sl sr fallback)
    (initialMovingDataCutoff_zero _ _ _ _ _ _ _ _ _) g Dq S ψ X lo upper W hX hwindow
    φ (fun _ => G) (selectedCompensationCenter cs) hout
    (completedCompensationPrior_lower A B N Y hi D P hP top cs)
    n (scheduledSmallLength (cs.drop (n + 1))) (b + b) (Y - Dlog)
    ((spectatorBulkCount k L : ℝ) / 4) (by linarith) hYreg rfl hproduct hpositive
    (smoothGiantPrimeRange G) I (smoothGiantPrimeRange_prime G)
    (fun p hp => smoothGiant_nonzero_in_log_cell φ G hout p
      (smoothGiantPrimeRange_prime G p (smoothGiantLivePrimes_subset _ _ _ hp)).pos
      (Finset.mem_filter.mp hp).2)
    hIpos hφ hpos (fun p => (hμdata.2.2.2 p).1) hμdata.2.2.1 ν (tailDensityMask A N)
    (fun p => tailDensityMask_nonempty hA N p (hP p p.property).pos)
    (fun p => by
      let : NeZero (p : ℕ) := ⟨(hP p p.property).ne_zero⟩
      exact tailDensityMask_card_lt hB N p (hP p p.property).pos (hdis p p.property))
    greg favorable
    (fun p x => by
      let : Fact (p : ℕ).Prime := ⟨hPglive p⟩
      dsimp only [greg]
      rw [normalizedResidueFamily_eq]
      exact normalizedResidueTransform_neg (tailDensityMask A N p) x)
    ⌈Real.exp (movingProductExponent T W n - T n)⌉₊ rfl hIlower
    (fun p y hy ℓ hℓ hd => live_giant_product_divisor_large Subtype.val
      (fun p => hP p p.property) ν (V (n + 1)) p (hPglive p) (hPglarge p)
      hνlarge y hy ℓ hℓ hd) hPglarge
    (smoothGiant_nonzero_in_log_cell φ G hout) (by rfl)
  · intro XR right hright u _ p w hcoeff
    exact selected_scheduled_coefficient_gap k n hn hk (by linarith) hP hG hD
      herror hBD hBz hbudget hcs b d sl sr fallback q g Dq S ψ X lo upper φ outside μ
      (scheduledChildBound V) (scheduledPivotCaps G cs) u right
      (fun i => scheduledRegularPrior_support A B N hi Y D P Qb top (cs.drop (n + 1))
        n (b + b) i (right i) (Finset.prod_ne_zero_iff.mp hright i (Finset.mem_univ _)))
      p XR w (smoothGiantLivePrimes_bounds _ (smoothGiantPrimeRange_prime G) φ G hout XR).1.le
      rfl rfl hcoeff
  · intro u hu
    refine ⟨fun p hp => ?_, fun ℓ hℓ hd => ?_⟩
    · exact selected_scheduled_pivot_bound hcs n hncs u hu p hp
    · have hh := live_prime_product_divisor_large Subtype.val (fun p => hP p p.property)
        (fun _ x => μ n x) (V (n + 1)) (fun _ => hμlarge) u hu ℓ hℓ hd
      exact lt_of_le_of_lt (movingProductNaturalCutoff_monotone T W (Y - Dlog)
        ((spectatorBulkCount k L : ℝ) / 4) hproduct (Nat.le_succ n)) hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferIteration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reserved exponential lower bound through the transfers -/

namespace Ostmann

private theorem half_exponential_square (c q : ℝ) :
    Real.exp (-c) / 2 * Real.exp (-q) ^ 2 =
      Real.exp (-2 * q - c - Real.log 2) := by
  calc
    _ = (Real.exp (-c) * Real.exp (2 * -q)) / 2 := by
      rw [show Real.exp (2 * -q) = Real.exp (-q) ^ 2 by
        simpa only [Nat.cast_ofNat] using Real.exp_nat_mul (-q) 2]
      ring
    _ = Real.exp (-c + 2 * -q) / 2 := by rw [Real.exp_add]
    _ = Real.exp ((-c + 2 * -q) - Real.log 2) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ = _ := by congr 1; ring

theorem transfer_half_lower (x y D B t c : ℝ) (ht : 0 ≤ t)
    (hbudget : c + Real.log 2 ≤ t)
    (hx : Real.exp (-B * t) ≤ x)
    (hD : D ≤ Real.exp (-(2 * B + 3) * t))
    (htransfer : Real.exp (-c) * x ^ 2 ≤ D + y) :
    Real.exp (-c) / 2 * x ^ 2 ≤ y := by
  have hsmall : Real.exp (-(2 * B + 3) * t) ≤
      Real.exp (-c) / 2 * Real.exp (-B * t) ^ 2 := by
    calc
      _ ≤ Real.exp (-2 * (B * t) - c - Real.log 2) :=
        Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := by
        simpa only [neg_mul] using (half_exponential_square c (B * t)).symm
  have hxx : Real.exp (-B * t) ^ 2 ≤ x ^ 2 := by
    have hx0 := (Real.exp_pos (-B * t)).le
    nlinarith
  have hDx := hD.trans (hsmall.trans
    (mul_le_mul_of_nonneg_left hxx (by positivity)))
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_VariableTransferIteration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The amplitude reserve with the actual, varying transfer losses -/

namespace Ostmann

open scoped BigOperators

private theorem half_sq_exp (d q : ℝ) :
    Real.exp (-d) / 2 * Real.exp (-q) ^ 2 =
      Real.exp (-d + 2 * -q - Real.log 2) := by
  rw [← Real.exp_nat_mul, div_mul_eq_mul_div, ← Real.exp_add,
    Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- Summing the actual losses before using the geometric reserve avoids a
uniform per-step loss assumption. The endpoint is finite, as in the paper. -/
theorem variable_transfer_iteration (k : ℕ) (η : ℕ → ℂ) (diag d : ℕ → ℝ)
    (B₀ m : ℝ) (hm : 0 ≤ m) (hd : ∀ j < k, 0 ≤ d j)
    (hbudget : ∑ j ∈ Finset.range k, (d j + Real.log 2) ≤ m)
    (hzero : Real.exp (-B₀ * m) ≤ ‖η 0‖)
    (hdiag : ∀ j < k, diag j ≤ Real.exp (-(2 * (B₀ + 1) + 3) * (2 : ℝ) ^ j * m))
    (htransfer : ∀ j < k, Real.exp (-d j) * ‖η j‖ ^ 2 ≤ diag j + ‖η (j + 1)‖) :
    ∀ j ≤ k, Real.exp (-(B₀ + 1) * (2 : ℝ) ^ j * m) ≤ ‖η j‖ := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsum (j : ℕ) (hj : j ≤ k) :
      ∑ h ∈ Finset.range j, (d h + Real.log 2) ≤ m := by
    apply le_trans _ hbudget
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj)
      (fun i hi _ => add_nonneg (hd i (Finset.mem_range.mp hi)) hlog)
  have hfine : ∀ j ≤ k,
      Real.exp (-((2 : ℝ) ^ j * (B₀ * m + ∑ h ∈ Finset.range j, (d h + Real.log 2)))) ≤ ‖η j‖ := by
    intro j
    induction j with
    | zero => intro _; simpa using hzero
    | succ j ih =>
      intro hj
      have hjk : j < k := by omega
      have hjle : j ≤ k := by omega
      have hprev := ih hjle
      have hcoarse : Real.exp (-(B₀ + 1) * ((2 : ℝ) ^ j * m)) ≤ ‖η j‖ := by
        apply le_trans (Real.exp_le_exp.mpr ?_) hprev
        have hs := mul_le_mul_of_nonneg_left (hsum j hjle) (show 0 ≤ (2 : ℝ) ^ j by positivity)
        nlinarith
      have hloss : d j + Real.log 2 ≤ m := by
        apply le_trans _ (hsum (j + 1) hj)
        have hnonneg : 0 ≤ ∑ h ∈ Finset.range j, (d h + Real.log 2) :=
          Finset.sum_nonneg fun h hh => add_nonneg (hd h (lt_of_lt_of_le (Finset.mem_range.mp hh) hjle)) hlog
        rw [Finset.sum_range_succ]
        linarith
      have ht : 0 ≤ (2 : ℝ) ^ j * m := by positivity
      have htbig : m ≤ (2 : ℝ) ^ j * m := le_mul_of_one_le_left hm (one_le_pow₀ (by norm_num))
      have hhalf := transfer_half_lower ‖η j‖ ‖η (j + 1)‖ (diag j) (B₀ + 1)
        ((2 : ℝ) ^ j * m) (d j) ht (hloss.trans htbig) hcoarse
        (by simpa only [mul_assoc] using hdiag j hjk) (htransfer j hjk)
      have hpow := pow_le_pow_left₀ (Real.exp_nonneg _) hprev 2
      apply le_trans _ hhalf
      apply le_trans _ (mul_le_mul_of_nonneg_left hpow (by positivity))
      rw [half_sq_exp]
      apply Real.exp_le_exp.mpr
      rw [Finset.sum_range_succ, pow_succ]
      have hscale : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      have hl0 : 0 ≤ d j + Real.log 2 := add_nonneg (hd j hjk) hlog
      nlinarith
  intro j hj
  apply le_trans (Real.exp_le_exp.mpr ?_) (hfine j hj)
  have hs := mul_le_mul_of_nonneg_left (hsum j hj) (show 0 ≤ (2 : ℝ) ^ j by positivity)
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedScheduledIteration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Iteration supplied by the actual selected priors and coefficient gaps -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem selected_scheduled_iteration_oai
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
    {N hi top : ℕ} {a C L Y G cb cd Dlog Bs BD Bz : ℝ}
    {D P Qb : Finset ℕ} {cs : List ℕ} (k : ℕ) (hk : 2 ≤ k)
    (hP : ∀ p ∈ P, p.Prime) (hambient : initialRegularPrimeRange L ⊆ P)
    (hL : 1 ≤ L) (hY : 0 < Y) (hYupper : Y ≤ Real.exp L)
    (hcell : 1024 * tailCellLinearRate a C + 52 ≤ (k : ℝ) ^ 4)
    (hcount : (8 + 4 * cs.length : ℕ) ≤ L)
    (hm : 256 ≤ (spectatorBulkCount k L : ℝ))
    (hG : 1 ≤ G) (hcb : 0 ≤ cb) (hD : |Dlog - 2 * cd| ≤ 2)
    (hBs : 0 ≤ Bs) (hBD : Bs + 1 ≤ BD) (hBz : 8 ≤ Bz)
    (herror : 256 * tailDefectBudget a C Y + 9 ≤ (spectatorBulkCount k L : ℝ) / 40)
    (hbudget : 40 * (2 * ((initialSmallCellList top cs).length + 3) + 14 + 4 * cs.length) +
      20 * Real.log 2 < (spectatorBulkCount k L : ℝ))
    (htop : SelectedSmallTailCell A B N a C L Y hi D
      ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top)
    (hcs : List.Forall₂
      (fun j t => SelectedSmallTailCell A B N a C L Y hi D (t / 4) j)
      cs (movingCompensationTargets
        (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
        (movingCompensationGaps k BD Bz L)))
    (hlower : ∀ j ∈ initialSmallCellList top cs, Real.exp ((1 / 100 : ℝ) * L) ≤ (j : ℝ))
    (hbulk : Qb ⊆ initialRegularPrimeRange L)
    (hbulklower : ∀ p ∈ Qb, Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (p : ℝ))
    (hdis : ∀ p ∈ P, Disjoint (tailResidues A N p) (negTailResidues B N p))
    (b d : ℕ)
    (sl sr : Fin d → P) (fallback : P)
    {J : Type} (q : J → ℕ) [∀ i, Fact (q i).Prime]
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J)
    (ψ : 𝓢(ℝ, ℂ)) (X lo upper : ℝ) (hX : 0 < X)
    (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (hpos : 0 < smoothGiantMass (smoothGiantPrimeRange G) φ G)
    (outside : List ℕ) (favorable : ℕ → Bool) (B₀ : ℝ) :
    let width : ℝ := 2 * ((initialSmallCellList top cs).length + 3)
    let T := movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs)
    let W := Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog
    let V := movingProductNaturalCutoff T W (Y - Dlog) ((spectatorBulkCount k L : ℝ) / 4)
    let μ := completedCompensationPrior A B N Y hi D P top cs
    let cell := fun c => primeSubsetPrior P (selectedTailCellPrimes A B N Y hi D c)
    let F := movingOriginalLeaf Subtype.val q
      (initialMovingDataCutoff Subtype.val b d (initialSmallCellList top cs).length cb cd sl sr fallback)
      g Dq S ψ X lo upper
    let I := Finset.Ioc ⌊Real.exp (G - 1)⌋₊ ⌊Real.exp (G + 1)⌋₊
    let ρ := smoothGiantPrior (smoothGiantPrimeRange G) φ G
    let greg := normalizedResidueFamily (tailDensityMask A N)
    let η := fun n => scheduledCellAmplitude Subtype.val outside μ (scheduledChildBound V)
      (scheduledPivotCaps G cs) V F φ (fun _ => G) (smoothGiantPrimeRange G) ρ
      cell (primeSubsetPrior P Qb) top cs n (b + b) greg greg favorable
    let diag := fun n => scheduledCellDiagonal Subtype.val outside μ (scheduledChildBound V)
      (scheduledPivotCaps G cs) V F φ (fun _ => G) (smoothGiantPrimeRange G) I ρ
      cell (primeSubsetPrior P Qb) top cs n (b + b) greg greg favorable
    X * upper ≤ Real.exp W →
    (∀ n ≤ k, (V n : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L))) →
    (∀ n ≤ k, (V n : ℝ) < Real.exp (G - 1)) →
    smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G ≤ L →
    Real.exp (-B₀ * (spectatorBulkCount k L : ℝ)) ≤ ‖η 0‖ →
    (∀ n < k, diag n ≤ Real.exp (-(2 * (B₀ + 1) + 3) * (2 : ℝ) ^ n * spectatorBulkCount k L)) →
    ∀ n ≤ k, Real.exp (-(B₀ + 1) * (2 : ℝ) ^ n * spectatorBulkCount k L) ≤ ‖η n‖ := by
  intro width T W V μ cell F I ρ greg η diag hwindow hfreq hgiantfreq hcg hinit hdiag
  have hscale : 4 ≤ (k : ℝ) ^ 4 * L :=
    (show (4 : ℝ) ≤ spectatorBulkCount k L by linarith).trans
      (spectatorBulkCount_upper k L (by linarith))
  refine variable_transfer_iteration k η diag
    (fun _ => max 0 (smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G))
    B₀ (spectatorBulkCount k L) (Nat.cast_nonneg _)
    (fun _ _ => le_max_left _ _) ?_ hinit hdiag ?_
  · exact spectatorBulkCount_iteration_budget k hk L hL hscale
      (fun _ => max 0 (smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G))
      (fun _ _ => max_le (by linarith) hcg)
  · intro j hj
    apply le_trans _ (show Real.exp (-smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G) *
      ‖η j‖ ^ 2 ≤ diag j + ‖η (j + 1)‖ from ?_)
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact Real.exp_le_exp.mpr (neg_le_neg (le_max_right _ _))
    · simpa only [η, diag, scheduledCellDiagonal] using selected_scheduled_amplitude_step hA hB
        k j hj (by omega) hP hambient hL hY hYupper hcell hcount hm hG hcb hD hBs hBD hBz
        herror hbudget htop hcs hlower hbulk hbulklower hdis b d sl sr fallback
        q g Dq S ψ X lo upper hX φ hφ hout hpos outside favorable hwindow
        (hfreq (j + 1) (by omega)) (hgiantfreq (j + 1) (by omega))

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.selected_scheduled_iteration_oai := @OAI.Ostmann.selected_scheduled_iteration_oai
