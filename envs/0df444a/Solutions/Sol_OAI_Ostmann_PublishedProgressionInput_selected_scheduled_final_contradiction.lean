-- Prove2me | solution 1 for OAI.Ostmann.PublishedProgressionInput.selected_scheduled_final_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:33:55.418851+00:00
-- url     : https://prove2.me/submissions/e02dbc5e-9097-4138-9d0e-21f7b0956fb6

import Mathlib
import Definitions.Def_OAIQ095D008
import Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_moving_selected_initial_symmetrized_energy

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

theorem reciprocalPrimeInterval_nonneg (q a : ℕ) (u v : ℝ) :
    0 ≤ reciprocalPrimeInterval q a u v := by
  apply Finset.sum_nonneg
  intro p _
  split <;> positivity

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
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_TransferCauchy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite Cauchy--Schwarz step in the history transfer -/

namespace Ostmann

open scoped BigOperators

theorem complex_pairing_sq_le {A : Type*} [Fintype A] (F G : A → ℂ) :
    ‖∑ a, F a * G a‖ ^ 2 ≤ (∑ a, ‖F a‖ ^ 2) * ∑ a, ‖G a‖ ^ 2 := by
  have hnorm : ‖∑ a, F a * G a‖ ≤ ∑ a, ‖F a‖ * ‖G a‖ := by
    simpa only [norm_mul] using norm_sum_le (Finset.univ : Finset A) (fun a => F a * G a)
  have hnonneg : 0 ≤ ∑ a, ‖F a‖ * ‖G a‖ :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset A)
    (fun a => ‖F a‖) (fun a => ‖G a‖)
  nlinarith [norm_nonneg (∑ a, F a * G a)]

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
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ComplexPrimeWeights
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complex smooth weights on actual prime intervals -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

theorem complexPrimeInterval_add (q a : ℕ) (u v t : ℝ) (w : ℝ → ℂ)
    (huv : u ≤ v) (hvt : v ≤ t) :
    complexPrimeInterval q a u v w + complexPrimeInterval q a v t w =
      complexPrimeInterval q a u t w :=
  Finset.sum_Ioc_consecutive _ (Nat.floor_le_floor (Real.exp_le_exp.mpr huv))
    (Nat.floor_le_floor (Real.exp_le_exp.mpr hvt))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_IntegerIntervalVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Abel variation for the original external integer measure -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

theorem complexIntegerInterval_add (q a : ℕ) (u v t G : ℝ) (w : ℝ → ℂ)
    (huv : u ≤ v) (hvt : v ≤ t) :
    complexIntegerInterval q a u v G w + complexIntegerInterval q a v t G w =
      complexIntegerInterval q a u t G w :=
  Finset.sum_Ioc_consecutive _ (Nat.floor_le_floor (Real.exp_le_exp.mpr huv))
    (Nat.floor_le_floor (Real.exp_le_exp.mpr hvt))

theorem integerResidueAtom_nonneg (q a : ℕ) (G : ℝ) (n : ℕ) :
    0 ≤ integerResidueAtom q a G n := by
  unfold integerResidueAtom
  split_ifs <;> positivity

theorem integerLogCellMass_nonneg (q a : ℕ) (u v G : ℝ) :
    0 ≤ integerLogCellMass q a u v G :=
  Finset.sum_nonneg (fun _ _ => integerResidueAtom_nonneg _ _ _ _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOccurrenceUnits
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unit coefficients for the actual sampled occurrence paths -/

namespace Ostmann
open scoped Classical

theorem MovingSlotData.Frequencies.root {σ : Type*} {P : ℤ → Prop} {n : ℕ}
    {T : MovingSlotData σ n} (h : T.Frequencies P) : P T.frequency := by
  cases T with
  | leaf => exact h
  | node => exact h.1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleValues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The labelled sampler evaluates to the actual natural prime sampler -/

namespace Ostmann
open scoped BigOperators

theorem movingNaturalProduct_append {σ : Type*} (value : σ → ℕ) (x y : List σ) :
    MovingSlotReversal.naturalProduct value (x ++ y) =
      MovingSlotReversal.naturalProduct value x * MovingSlotReversal.naturalProduct value y := by
  simp only [MovingSlotReversal.naturalProduct, List.map_append, List.prod_append]

theorem movingSlotValues_flatten {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (x : TreeLeafTuple (List σ) n) :
    MovingSlotReversal.naturalProduct value (flattenMovingSlots n x) =
      treeLeafProduct n (movingSlotValues value n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [flattenMovingSlots, MovingSlotReversal.naturalProduct, List.map_append,
      List.prod_append, movingSlotValues, treeLeafProduct]
    exact congrArg₂ (· * ·) (ih x.1) (ih x.2)

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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRegularSlots
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.movingSampleSlotsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original regular slot lists in every moving child -/

namespace Ostmann
open scoped Classical

theorem buildMovingSlotData_regular_perm {σ : Type*} (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List σ) n) (samples : MovingSampleSlots σ n) :
    (buildMovingSlotData n t small bulk samples).regularSlots.Perm
      (flattenMovingSlots n small ++ flattenMovingSlots n bulk) := by
  cases samples with
  | leaf => exact List.Perm.refl _
  | @node n samples left right =>
    apply List.perm_iff_count.mpr
    intro a
    simp only [buildMovingSlotData, MovingSlotData.regularSlots, flattenMovingSlots,
      List.count_append]
    omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSignedUnits
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The giant unit tests on signed residue representatives -/

namespace Ostmann
open scoped Classical

theorem MovingSlotData.frequencies_isCoprime {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) (x : ℤ) :
    T.Frequencies (fun s => IsCoprime x s) ↔ IsCoprime x T.frequencyProduct := by
  induction T with
  | leaf => rfl
  | node s CL CR U left right ihL ihR =>
    simp only [Frequencies, frequencyProduct, IsCoprime.mul_right_iff, ihL, ihR, and_assoc]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_ReciprocalPolynomialFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized counterpart ratio is an admissible smooth factor -/

namespace Ostmann

open scoped BigOperators

theorem reciprocalPolynomialFactor_original (P : Polynomial ℝ) (hi : ℝ)
    (hhi : 1 ≤ hi) (x X M : ℝ) (hX : X ≠ 0) (hM : M ≠ 0)
    (hP : P.eval x = M / X) (hrange : M / X ∈ Set.Icc (1 : ℝ) hi) :
    (reciprocalPolynomialFactor P hi hhi).value x = Complex.ofReal (X / M) := by
  rw [ClippedPolynomialFactor.value_of_mem _ x (by
    change P.eval x ∈ Set.Icc (1 : ℝ) hi
    rw [hP]
    exact hrange)]
  change Complex.ofReal ((P.eval x)⁻¹) = _
  rw [hP]
  congr 1
  field_simp

theorem reciprocalPolynomialFactor_budget (P : Polynomial ℝ) (hi : ℝ) (hhi : 1 ≤ hi) :
    2 * (reciprocalPolynomialFactor P hi hhi).bound +
      (reciprocalPolynomialFactor P hi hhi).lip *
        ((reciprocalPolynomialFactor P hi hhi).hi - (reciprocalPolynomialFactor P hi hhi).lo) =
      hi + 1 := by
  dsimp only [reciprocalPolynomialFactor]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantReciprocalFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized reciprocal giant factor in the diagonal multiplier -/

namespace Ostmann

theorem giantReciprocalFactor_budget (P : Polynomial ℝ) (G : ℝ) :
    2 * (giantReciprocalFactor P G).bound + (giantReciprocalFactor P G).lip *
      ((giantReciprocalFactor P G).hi - (giantReciprocalFactor P G).lo) = 1 + Real.exp 2 := by
  rw [giantReciprocalFactor, reciprocalPolynomialFactor_budget, add_comm]

theorem giantReciprocalFactor_value (P : Polynomial ℝ) (G x : ℝ)
    (hx : P.eval x ∈ Set.Icc (Real.exp (G - 1)) (Real.exp (G + 1))) :
    (Real.exp 1 : ℂ) * (giantReciprocalFactor P G).value x = (Real.exp G / P.eval x : ℝ) := by
  have hlo : 0 < Real.exp (G - 1) := Real.exp_pos _
  have hp : 0 < P.eval x := hlo.trans_le hx.1
  have hrange : P.eval x / Real.exp (G - 1) ∈ Set.Icc (1 : ℝ) (Real.exp 2) := by
    refine ⟨(one_le_div hlo).mpr hx.1, ?_⟩
    calc
      _ ≤ Real.exp (G + 1) / Real.exp (G - 1) := div_le_div_of_nonneg_right hx.2 hlo.le
      _ = _ := by rw [← Real.exp_sub]; congr 1; ring
  rw [giantReciprocalFactor, reciprocalPolynomialFactor_original _ _ _ x
    (Real.exp (G - 1)) (P.eval x) hlo.ne' hp.ne'
    (by simp only [Polynomial.eval_mul, Polynomial.eval_C, div_eq_mul_inv, mul_comm]) hrange,
    ← Complex.ofReal_mul]
  apply congrArg (fun a : ℝ => (a : ℂ))
  rw [← mul_div_assoc, ← Real.exp_add, show 1 + (G - 1) = G by ring]

/-- Multiplication by the actual giant cutoff makes the clipped reciprocal
identical to the manuscript's reciprocal everywhere, including zero terms. -/
theorem giantReciprocalFactor_cutoff (P : Polynomial ℝ) (φ : ℝ → ℝ)
    (G B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (x : ℝ) :
    (logCutoffPolynomialFactor P φ G B D hB hD hφ hlip).value x *
      ((Real.exp 1 : ℂ) * (giantReciprocalFactor P G).value x) =
        (positiveLogCutoff φ G (P.eval x) : ℂ) * (Real.exp G / P.eval x : ℝ) := by
  rw [logCutoffPolynomialFactor_value P φ G B D hB hD hφ hlip hout x]
  by_cases hz : positiveLogCutoff φ G (P.eval x) = 0
  · simp only [hz, Complex.ofReal_zero, zero_mul]
  · have hx : 0 < P.eval x := by
      by_contra hn
      exact hz (by simp only [positiveLogCutoff, ite_eq_right hn])
    have hn : φ (Real.log (P.eval x) - G) ≠ 0 := by
      simpa only [positiveLogCutoff, ite_eq_left hx] using hz
    have hr : |Real.log (P.eval x) - G| < 1 := lt_of_not_ge (fun h => hn (hout _ h))
    have hbounds : P.eval x ∈ Set.Icc (Real.exp (G - 1)) (Real.exp (G + 1)) := by
      have h := abs_lt.mp hr
      constructor
      · rw [← Real.exp_log hx]
        exact Real.exp_le_exp.mpr (by linarith)
      · rw [← Real.exp_log hx]
        exact Real.exp_le_exp.mpr (by linarith)
    rw [giantReciprocalFactor_value P G x hbounds]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantOuterFactors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal two outer cutoff priors and the diagonal reciprocal factor -/

namespace Ostmann
open scoped BigOperators Classical

/-- Both actual cutoff priors are retained. In the diagonal environment the
remaining factor is precisely exp(G_R)/R, including all off-support zeros. -/
theorem giantOuterFactors_value (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (x : ℝ) :
    (giantOuterScalar diagonal : ℂ) *
      smoothPolynomialWeight (giantOuterFactors L R φ Jleft Jright B D hB hD hφ hlip diagonal) x =
        (positiveLogCutoff φ Jleft (L.eval x) : ℂ) * (positiveLogCutoff φ Jright (R.eval x) : ℂ) *
          (if diagonal then ((Real.exp Jright / R.eval x : ℝ) : ℂ) else 1) := by
  have hL := logCutoffPolynomialFactor_value L φ Jleft B D hB hD hφ hlip hout x
  have hR := logCutoffPolynomialFactor_value R φ Jright B D hB hD hφ hlip hout x
  have hone : onePolynomialFactor.value x = 1 := rfl
  have hrec := giantReciprocalFactor_cutoff R φ Jright B D hB hD hφ hlip hout x
  cases diagonal
  · simp only [giantOuterScalar, Bool.false_eq_true, ite_false, if_false, Complex.ofReal_one,
      giantOuterFactors, smoothPolynomialWeight, Fin.prod_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Fin.prod_univ_zero, mul_one, one_mul, hL, hR, hone]
  · simp only [giantOuterScalar, ite_true, if_true, giantOuterFactors, smoothPolynomialWeight,
      Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Fin.prod_univ_zero, mul_one]
    calc
      _ = (logCutoffPolynomialFactor L φ Jleft B D hB hD hφ hlip).value x *
          ((logCutoffPolynomialFactor R φ Jright B D hB hD hφ hlip).value x *
            ((Real.exp 1 : ℂ) * (giantReciprocalFactor R Jright).value x)) := by ring
      _ = _ := by rw [hL, hrec]; ring

theorem giantOuterFactors_budget (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (diagonal : Bool) :
    smoothPolynomialBudget (giantOuterFactors L R φ Jleft Jright B D hB hD hφ hlip diagonal) =
      (2 * B + D * (Real.exp 2 - 1)) ^ 2 * (if diagonal then 1 + Real.exp 2 else 2) := by
  have hL := logCutoffPolynomialFactor_budget L φ Jleft B D hB hD hφ hlip
  have hR := logCutoffPolynomialFactor_budget R φ Jright B D hB hD hφ hlip
  cases diagonal
  · simp only [giantOuterFactors, Bool.false_eq_true, ite_false, if_false, smoothPolynomialBudget,
      Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Fin.prod_univ_zero, mul_one, onePolynomialFactor]
    rw [hL, hR]
    ring
  · simp only [giantOuterFactors, ite_true, if_true, smoothPolynomialBudget,
      Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Fin.prod_univ_zero, mul_one]
    rw [hL, hR, giantReciprocalFactor_budget]
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOuterKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two-history kernel with its original outer priors and diagonal ratio -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators Classical ComplexConjugate SchwartzMap

theorem giantOuterWeight_polynomial (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (x : ℝ) :
    giantOuterWeight φ Jleft Jright diagonal (L.eval x) (R.eval x) =
      (giantOuterScalar diagonal : ℂ) *
        smoothPolynomialWeight (giantOuterFactors L R φ Jleft Jright B D hB hD hφ hlip diagonal) x :=
  (giantOuterFactors_value L R φ Jleft Jright B D hB hD hφ hlip hout diagonal x).symm

theorem giantOuterWeight_norm (φ : ℝ → ℝ) (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (L R : ℝ) :
    ‖giantOuterWeight φ Jleft Jright diagonal L R‖ ≤
      giantOuterScalar diagonal * (2 * B + D * (Real.exp 2 - 1)) ^ 2 *
        (if diagonal then 1 + Real.exp 2 else 2) := by
  have hs : 0 ≤ giantOuterScalar diagonal := by cases diagonal <;> simp [giantOuterScalar, (Real.exp_pos _).le]
  have hv := giantOuterWeight_polynomial (Polynomial.C L) (Polynomial.C R) φ Jleft Jright B D
    hB hD hφ hlip hout diagonal 0
  simp only [Polynomial.eval_C] at hv
  rw [hv, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
  have h := mul_le_mul_of_nonneg_left (smoothPolynomialWeight_norm
    (giantOuterFactors (Polynomial.C L) (Polynomial.C R) φ Jleft Jright B D hB hD hφ hlip diagonal) 0) hs
  rw [giantOuterFactors_budget] at h
  simpa only [mul_assoc] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ResidueIntervals
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact residue decompositions of the original giant sums -/

namespace Ostmann
open scoped BigOperators Classical

theorem reciprocalPrimeInterval_le_exp (q a : ℕ) (u v : ℝ) :
    reciprocalPrimeInterval q a (Real.exp u) (Real.exp v) ≤ Real.exp (v - u) := by
  calc
    _ ≤ ∑ _p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊, Real.exp (-u) := by
      apply Finset.sum_le_sum
      intro p hp
      split_ifs
      · have hp0 : (0 : ℝ) < p := (Real.exp_pos u).trans (Nat.lt_of_floor_lt (Finset.mem_Ioc.mp hp).1)
        have hlog : Real.exp (-Real.log (p : ℝ)) = (p : ℝ)⁻¹ := by
          rw [Real.exp_neg, Real.exp_log hp0]
        rw [← hlog]
        exact Real.exp_le_exp.mpr (neg_le_neg (log_mem_of_mem_exp_interval hp).1.le)
      · exact (Real.exp_pos _).le
    _ = ((⌊Real.exp v⌋₊ - ⌊Real.exp u⌋₊ : ℕ) : ℝ) * Real.exp (-u) := by simp
    _ ≤ Real.exp v * Real.exp (-u) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact (Nat.cast_le.mpr (Nat.sub_le _ _)).trans (Nat.floor_le (Real.exp_pos _).le)
    _ = _ := by rw [← Real.exp_add, sub_eq_add_neg]

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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkSlotFieldBridge
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original labelled bulk slots produce the quartet leaf arrays -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem movingSlotValues_indexed {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (s : TreeLeafTuple (List σ) n) (j : TreeLeafIndex n) :
    treeLeafTupleEquiv ℕ n (movingSlotValues value n s) j =
      MovingSlotReversal.naturalProduct value (treeLeafTupleEquiv (List σ) n s j) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases j with
    | inl j => exact ih s.1 j
    | inr j => exact ih s.2 j

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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSamplePrimeExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact sample expansion inside the actual giant-prime averages -/

namespace Ostmann
open scoped Classical BigOperators

theorem complexPrimeInterval_const_mul (q a : ℕ) (u v : ℝ) (c : ℂ) (F : ℝ → ℂ) :
    complexPrimeInterval q a u v (fun x => c * F x) =
      c * complexPrimeInterval q a u v F := by
  unfold complexPrimeInterval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp only [mul_assoc, mul_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRootedSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact grouping of the two independent child frequency sums -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingRootedFrequencyTree_root (V : ℕ → ℕ) (n : ℕ) (s : ℤ)
    (a : MovingDescendantFrequencyIndex V n) :
    frequencyRoot n (movingRootedFrequencyTree V n s a) = s := by
  cases n <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCoefficientSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Current support inherited from the original summed coefficient -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingFullSupport_local {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ)
    (h : movingFullSupport value outside T XL XR) :
    movingLocalSupport value outside ⟨n, T, XL, XR⟩ := by
  cases T with
  | leaf => exact h
  | node => exact ⟨h.1.1, h.2.1⟩

/-- A nonzero finite average contains a supported original sample. No
positivity, normalization, or conditioning of the prime prior is needed. -/
theorem movingSupportedSampledWeight_nonzero_support {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ)
    (h : movingSupportedSampledWeight value outside μ childBound pivotBound F E
      n t small bulk XL XR ≠ 0) :
    ∃ a : MovingSampleSlots σ n,
      movingFullSupport value outside (buildMovingSlotData n t small bulk a) XL XR := by
  rw [movingSupportedSampledWeight_eq, movingCompensatedAverage] at h
  obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have ht : movingSupportedSampleTerm value outside childBound pivotBound F E
      n t small bulk XL XR a ≠ 0 := by
    intro hz
    exact ha (by rw [hz, mul_zero])
  unfold movingSupportedSampleTerm movingSupportedWeight at ht
  refine ⟨a, ?_⟩
  by_contra hs
  exact ht (ite_eq_right hs)

/-- The root sum still has the actual current pairwise support and both
root-frequency units. These are the only support facts needed to attach the
original coefficient to the full Fourier transfer. -/
theorem movingFrequencyCoefficient_nonzero_support {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ)
    (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ)
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G
      n s small bulk XL XR ≠ 0) :
    (XL :: XR :: ((flattenMovingSlots n small ++ flattenMovingSlots n bulk).map value ++ outside)).Pairwise Nat.Coprime ∧
      IsCoprime (XL : ℤ) s ∧ IsCoprime (XR : ℤ) s := by
  rw [movingFrequencyCoefficient] at h
  obtain ⟨t, _, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨a, ha⟩ := movingSupportedSampledWeight_nonzero_support value outside μ childBound
    pivotBound F (movingOriginalNode value childBound pivotBound φ G) n
    (movingRootedFrequencyTree V n s t) small bulk XL XR ht
  let T := buildMovingSlotData n (movingRootedFrequencyTree V n s t) small bulk a
  have hlocal := movingFullSupport_local value outside T XL XR ha
  have hreg := buildMovingSlotData_regular_perm n (movingRootedFrequencyTree V n s t) small bulk a
  have hp : (T.currentSlots value XL XR ++ outside).Perm
      (XL :: XR :: ((flattenMovingSlots n small ++ flattenMovingSlots n bulk).map value ++ outside)) := by
    simpa only [MovingSlotData.currentSlots, List.cons_append] using
      (((hreg.map value).cons XR).cons XL).append_right outside
  have hpair := (hp.pairwise_iff (fun h => h.symm)).mp hlocal.1
  have hfreq : T.frequency = s := by
    rw [(buildMovingSlotData_follows n _ small bulk a).root, movingRootedFrequencyTree_root]
  have hL := ((T.frequencies_isCoprime (XL : ℤ)).mpr hlocal.2.1).root
  have hR := ((T.frequencies_isCoprime (XR : ℤ)).mpr hlocal.2.2.1).root
  exact ⟨hpair, hfreq ▸ hL, hfreq ▸ hR⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFinalGap
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The polynomial bulk scale leaves a strict final overlap margin -/

namespace Ostmann
open Filter Asymptotics

/-- At the manuscript's scale `z = k^4`, every fixed logarithmic cost is
smaller than any fixed positive multiple of `log (2^k)`. -/
theorem eventually_polynomial_scale_log_margin (B C δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop,
      B + C * Real.log ((k : ℝ) ^ 4) < δ * Real.log ((2 : ℝ) ^ k) := by
  have hlog := (((Real.isLittleO_log_id_atTop.const_mul_left (4 * C)).add
    (isLittleO_const_id_atTop B)).bound
    (by positivity : 0 < δ * Real.log 2 / 2))
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually hlog,
    eventually_ge_atTop (1 : ℕ)] with k hk hk1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  simp only [Real.norm_eq_abs, id_eq, abs_of_pos hk0] at hk
  rw [Real.log_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  have h := (le_abs_self _).trans hk
  have hpos : 0 < δ * Real.log 2 * (k : ℝ) := by positivity
  nlinarith

/-- The `3/4` bad-arrangement saving dominates the `2/5` cutoff exponent,
with the full base-gap and fixed logarithmic costs of (9.8). -/
theorem eventually_moving_final_gap (Bs BD Bz C B : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      BD + 2 * Bs + (Bz + 16) * Real.log ((k : ℝ) ^ 4) + C + 2 * B + 2 <
        (7 / 20 : ℝ) * Real.log ((2 : ℝ) ^ k) := by
  filter_upwards [eventually_polynomial_scale_log_margin (BD + 2 * Bs + C + 2 * B + 2)
    (Bz + 16) (7 / 20) (by norm_num)] with k hk
  linarith

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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingDiagonalOuterWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining the inactive regular density under the bulk prime average -/

namespace Ostmann
open scoped Classical BigOperators

theorem diagonalOuterMajorant_pos (B D : ℝ) (diagonal : Bool) :
    0 < diagonalOuterMajorant B D diagonal := by
  unfold diagonalOuterMajorant
  have hs : 0 ≤ giantOuterScalar diagonal := by
    cases diagonal <;> simp [giantOuterScalar, (Real.exp_pos _).le]
  have hh : 0 ≤ (if diagonal then 1 + Real.exp 2 else (2 : ℝ)) := by
    cases diagonal <;> positivity
  positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingStatisticDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential decay of the full selected-statistic bound at fixed depth -/

namespace Ostmann
open Filter

/-- Fixed constants are absorbed by a strict linear-exponent margin. -/
theorem eventually_bulk_exp_margin (k : ℕ) (hk : 0 < k) (K a b : ℝ)
    (hK : 0 ≤ K) (hab : a < b) :
    ∀ᶠ L : ℝ in atTop, K * Real.exp (a * spectatorBulkCount k L) ≤
      Real.exp (b * spectatorBulkCount k L) := by
  filter_upwards [(spectatorBulkCount_tendsto k hk).eventually
    (eventually_ge_atTop (Real.log (K + 1) / (b - a)))] with L hL
  have hmargin := (div_le_iff₀ (sub_pos.mpr hab)).mp hL
  calc
    _ ≤ (K + 1) * Real.exp (a * spectatorBulkCount k L) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ = Real.exp (Real.log (K + 1) + a * spectatorBulkCount k L) := by
      rw [Real.exp_add, Real.exp_log (by linarith)]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

/-- The retained arithmetic error beats every fixed exponential in the bulk size. -/
theorem eventually_bulk_arithmetic_error (k : ℕ) (T : ℝ) :
    ∀ᶠ L : ℝ in atTop, Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) ≤
      Real.exp (-T * spectatorBulkCount k L) := by
  let C := max T 0 * (k : ℝ) ^ 4
  have hC : 0 ≤ C := mul_nonneg (le_max_right _ _) (by positivity)
  filter_upwards [arithmetic_exponent_absorption 0 (12 / 10000) 0 C 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (0 : ℝ)] with L hL hL0
  have hm : T * spectatorBulkCount k L ≤ C * L := by
    apply (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)).trans
    exact (mul_le_mul_of_nonneg_left (spectatorBulkCount_upper k L hL0)
      (le_max_right _ _)).trans_eq (by dsimp only [C]; ring)
  simp only [pow_one, zero_mul, Real.exp_zero, mul_one, one_mul] at hL
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hC hL0]

theorem eventually_scaled_bulk_arithmetic_error (k : ℕ) (hk : 0 < k)
    (K a T : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop,
      K * Real.exp (a * spectatorBulkCount k L) *
        Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) ≤
      Real.exp (-T * spectatorBulkCount k L) := by
  filter_upwards [eventually_bulk_arithmetic_error k (a + T + 1),
    eventually_bulk_exp_margin k hk K (-(T + 1)) (-T) hK (by linarith)] with L herror hmargin
  apply le_trans (mul_le_mul_of_nonneg_left herror
    (mul_nonneg hK (Real.exp_pos _).le))
  have heq : K * Real.exp (a * spectatorBulkCount k L) *
      Real.exp (-(a + T + 1) * spectatorBulkCount k L) =
      K * Real.exp (-(T + 1) * spectatorBulkCount k L) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rwa [heq]

/-- This is the numerical bound occurring in the selected-prior theorem,
including the root-frequency mass and all five arithmetic errors. -/
theorem eventually_moving_statistic_decay (k : ℕ) (hk : 0 < k)
    (C K A badRate diagRate gain T : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hbad : A + badRate + diagRate < -T) (hgood : A - gain < -T) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ V : ℕ, (V : ℝ) ≤ Real.exp (A * m) → ∀ η : ℂ,
      ‖η‖ ^ 2 ≤ C * (2 * V + 1 : ℕ) * Real.exp 2 *
        (K * Real.exp (badRate * m) *
          (Real.exp (diagRate * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) +
          Real.exp (-gain * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) →
      ‖η‖ ^ 2 ≤ Real.exp (-T * m) := by
  let K₀ := 3 * C * Real.exp 2
  have hK₀ : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  filter_upwards [eventually_bulk_exp_margin k hk (4 * K₀ * K)
      (A + badRate + diagRate) (-T) (by positivity) hbad,
    eventually_bulk_exp_margin k hk (4 * K₀) (A - gain) (-T) (by positivity) hgood,
    eventually_scaled_bulk_arithmetic_error k hk (4 * (5 * K₀ * K)) (A + badRate) T (by positivity),
    eventually_scaled_bulk_arithmetic_error k hk (4 * (5 * K₀)) A T (by positivity)]
    with L h₁ h₃ h₂ h₄
  dsimp only
  intro V hV η hη
  let m := spectatorBulkCount k L
  have hmass : ((2 * V + 1 : ℕ) : ℝ) ≤ 3 * Real.exp (A * m) := by
    have he : 1 ≤ Real.exp (A * m) := Real.one_le_exp (mul_nonneg hA (Nat.cast_nonneg _))
    push_cast
    dsimp only [m] at he ⊢
    linarith
  have hupper := hη.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass hC) (Real.exp_pos _).le)
    (by positivity))
  have heq : C * (3 * Real.exp (A * m)) * Real.exp 2 *
        (K * Real.exp (badRate * m) *
          (Real.exp (diagRate * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) +
          Real.exp (-gain * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) =
      K₀ * K * Real.exp ((A + badRate + diagRate) * m) +
      5 * K₀ * K * Real.exp ((A + badRate) * m) * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) +
      K₀ * Real.exp ((A - gain) * m) +
      5 * K₀ * Real.exp (A * m) * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
    dsimp only [K₀]
    simp only [add_mul, sub_mul, Real.exp_add, Real.exp_sub, Real.exp_neg, neg_mul]
    ring
  change ‖η‖ ^ 2 ≤ C * (3 * Real.exp (A * m)) * Real.exp 2 * _ at hupper
  rw [heq] at hupper
  dsimp only [m] at hupper
  nlinarith only [hupper, h₁, h₂, h₃, h₄]

/-- Substitute the original bottom gap before applying the exponential margin. -/
theorem eventually_moving_statistic_decay_with_base (k : ℕ) (hk : 0 < k)
    (r C K A badRate D ε gain T : ℝ)
    (hr : 0 ≤ r) (hC : 0 ≤ C) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hbad : A + r * badRate + (r * D + (Real.log 12 + 1) * r + ε) < -T)
    (hgood : A - gain < -T) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ V : ℕ, (V : ℝ) ≤ Real.exp (A * m) → ∀ Δ : ℝ, Δ ≤ D * m → ∀ η : ℂ,
      ‖η‖ ^ 2 ≤ C * (2 * V + 1 : ℕ) * Real.exp 2 *
        (K * Real.exp (r * m * badRate) *
          (Real.exp (r * Δ + (Real.log 12 + 1) * r * m + ε * m) +
            5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) +
          Real.exp (-gain * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) →
      ‖η‖ ^ 2 ≤ Real.exp (-T * m) := by
  filter_upwards [eventually_moving_statistic_decay k hk C K A (r * badRate)
    (r * D + (Real.log 12 + 1) * r + ε) gain T hC hK hA hbad hgood] with L hd
  dsimp only at hd ⊢
  rw [show (r * badRate) * (spectatorBulkCount k L : ℝ) =
    r * spectatorBulkCount k L * badRate by ring] at hd
  intro V hV Δ hΔ η hη
  have hb : Real.exp (r * Δ + (Real.log 12 + 1) * r * spectatorBulkCount k L +
      ε * spectatorBulkCount k L) ≤
      Real.exp ((r * D + (Real.log 12 + 1) * r + ε) * spectatorBulkCount k L) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left hΔ hr]
  let err := 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))
  have hi := mul_le_mul_of_nonneg_left (add_le_add hb (le_refl err))
    (mul_nonneg hK (Real.exp_pos (r * spectatorBulkCount k L * badRate)).le)
  have hi' := add_le_add
    (add_le_add hi (le_refl (Real.exp (-gain * spectatorBulkCount k L)))) (le_refl err)
  exact hd V hV η (hη.trans (mul_le_mul_of_nonneg_left hi'
    (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) (Real.exp_pos 2).le)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFinalRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Specializing the final decay to the actual frequency rate -/

namespace Ostmann
open Filter

theorem eventually_moving_frequency_rate_margin (Bs BD Bz B : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      movingFrequencyRate Bs BD Bz ((k : ℝ) ^ 4) k +
        (2 : ℝ) ^ k * (-(3 / 4 : ℝ) * Real.log ((2 : ℝ) ^ k) + 5 / 4) +
        ((2 : ℝ) ^ k * (Bs + 8 * Real.log ((k : ℝ) ^ 4)) +
          (Real.log 12 + 1) * (2 : ℝ) ^ k + 1) <
        -((2 * B + 1) * (2 : ℝ) ^ k) := by
  filter_upwards [eventually_moving_final_gap Bs BD Bz (Real.log 12 + 21 / 4) B] with k hk
  have hr : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hh := mul_lt_mul_of_pos_left hk (show 0 < (2 : ℝ) ^ k by positivity)
  unfold movingFrequencyRate
  nlinarith only [hh, hr]

theorem bulk_exponential_lower_contradicts_decay (B r m : ℝ) (hm : 0 < m) (hr : 0 < r)
    (η : ℂ) (hlower : Real.exp (-B * r * m) ≤ ‖η‖)
    (hupper : ‖η‖ ^ 2 ≤ Real.exp (-((2 * B + 1) * r) * m)) : False := by
  have hs := pow_le_pow_left₀ (Real.exp_pos (-B * r * m)).le hlower 2
  have heq : Real.exp (-B * r * m) ^ 2 = Real.exp (-(2 * B * r) * m) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at hs
  have hlt : Real.exp (-((2 * B + 1) * r) * m) < Real.exp (-(2 * B * r) * m) :=
    Real.exp_lt_exp.mpr (by nlinarith [mul_pos hr hm])
  exact (not_lt_of_ge (hs.trans hupper)) hlt

/-- The precise numerical upper bound already proved for the selected-prior
statistic contradicts the lower bound preserved by the transfer iteration. -/
theorem eventually_moving_numeric_contradiction (Bs BD Bz B C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ k : ℕ in atTop, ∀ᶠ L : ℝ in atTop,
      let m := spectatorBulkCount k L
      let r : ℝ := (2 : ℝ) ^ k
      let z : ℝ := (k : ℝ) ^ 4
      let A := movingFrequencyRate Bs BD Bz z k
      let D := Bs + 8 * Real.log z
      ∀ V : ℕ, (V : ℝ) ≤ Real.exp (A * m) → 0 ≤ A →
      ∀ Δ : ℝ, Δ ≤ D * m → ∀ η : ℂ,
      Real.exp (-B * r * m) ≤ ‖η‖ →
      ‖η‖ ^ 2 ≤ C * (2 * V + 1 : ℕ) * Real.exp 2 *
        (((((2 ^ k + 1) * (2 ^ k) ^ (2 * 2 ^ k) : ℕ) : ℝ)) *
          Real.exp (r * m * (-(3 / 4 : ℝ) * Real.log ((2 : ℝ) ^ k) + 5 / 4)) *
            (Real.exp (r * Δ + (Real.log 12 + 1) * r * m + m) +
              5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) +
          Real.exp (-(A + (2 * B + 1) * r + 1) * m) +
            5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) → False := by
  filter_upwards [eventually_moving_frequency_rate_margin Bs BD Bz B,
    eventually_ge_atTop (1 : ℕ)] with k hmargin hk
  let A := movingFrequencyRate Bs BD Bz ((k : ℝ) ^ 4) k
  by_cases hA : 0 ≤ A
  · have hd := eventually_moving_statistic_decay_with_base k hk ((2 : ℝ) ^ k) C
      (((2 ^ k + 1) * (2 ^ k) ^ (2 * 2 ^ k) : ℕ) : ℝ) A
      (-(3 / 4 : ℝ) * Real.log ((2 : ℝ) ^ k) + 5 / 4)
      (Bs + 8 * Real.log ((k : ℝ) ^ 4)) 1 (A + (2 * B + 1) * (2 : ℝ) ^ k + 1)
      ((2 * B + 1) * (2 : ℝ) ^ k) (by positivity) hC (by positivity) hA hmargin (by dsimp only [A]; linarith)
    filter_upwards [hd, (spectatorBulkCount_tendsto k hk).eventually (eventually_gt_atTop (0 : ℝ))]
      with L hd hm
    dsimp only
    intro V hV _ Δ hΔ η hlower hupper
    apply bulk_exponential_lower_contradicts_decay B ((2 : ℝ) ^ k)
      (spectatorBulkCount k L) hm (by positivity) η hlower
    apply hd V hV Δ hΔ η
    simpa only [one_mul] using hupper
  · exact Filter.Eventually.of_forall (fun L V _ hA' => (hA hA').elim)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeProductMatching
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equal distinct-prime products give the unique actual slot matching -/

namespace Ostmann

open scoped BigOperators Classical

theorem prime_dvd_prime_product {I : Type*} [Fintype I]
    (p : I → ℕ) (hp : ∀ i, (p i).Prime) (q : ℕ) (hq : q.Prime)
    (hd : q ∣ ∏ i, p i) : ∃ i, q = p i := by
  obtain ⟨i, _, hi⟩ := (hq.prime.dvd_finsetProd_iff p).mp hd
  exact ⟨i, ((Nat.dvd_prime (hp i)).mp hi).resolve_left hq.ne_one⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRegularDiagonal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The common Fourier multiplier on equal-product diagonal fibres -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem primeTuple_image_factors {J : Type*} [Fintype J]
    (p : J → ℕ) (hp : ∀ j, (p j).Prime) :
    Finset.univ.image p = (∏ j, p j).primeFactors := by
  ext q
  rw [Nat.mem_primeFactors]
  constructor
  · intro hq
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨hp j, Finset.dvd_prod_of_mem p (Finset.mem_univ j),
      (Finset.prod_pos (fun j _ => (hp j).pos)).ne'⟩
  · rintro ⟨hq, hd, _⟩
    obtain ⟨j, rfl⟩ := prime_dvd_prime_product p hp q hq hd
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩

/-- Every distinct-prime arrangement has exactly the same transform on a
fixed product/frequency fibre. This justifies extracting it before taking
the squared modulus of the sum over arrangements. -/
theorem movingRegularTransform_eq_primeProduct {J : Type*} [Fintype J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime] (hinj : Function.Injective p)
    (g : ∀ q : ℕ, ZMod q → ℂ) (D : ℕ) (s : ℤ) :
    movingRegularTransform p (fun j => g (p j)) D s =
      primeProductTransform g D (∏ j, p j) s := by
  have hc (j : J) : tupleCofactor p j = (∏ i, p i) / p j := by
    rw [← tupleCofactor_mul p j]
    exact (Nat.mul_div_cancel_left _ (Fact.out : (p j).Prime).pos).symm
  unfold movingRegularTransform primeProductTransform
  rw [← primeTuple_image_factors p (fun j => Fact.out), Finset.prod_image]
  · exact Finset.prod_congr rfl (fun j _ => by rw [hc j])
  · intro i _ j _ hij
    exact hinj hij

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRegularMultiplierIdentity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal diagonal multiplier is the squared regular Fourier product -/

namespace Ostmann
open scoped Classical BigOperators

theorem naturalRegularMultiplier_eq_transform_norm {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (active : I → Bool) (s : ℤ)
    (D : ℕ) (g : ∀ i, ZMod (p i) → ℂ) (XL XR : ℕ) :
    naturalRegularMultiplier p active s
      (fun i => ((D * tupleCofactor p i : ℕ) : ZMod (p i))) g XL XR =
      ‖movingRegularTransform p (fun i x => if active i then g i x else 1)
        (D * XL * XR) s‖ ^ 2 := by
  rw [movingRegularTransform, norm_prod, ← Finset.prod_pow]
  unfold naturalRegularMultiplier
  apply Finset.prod_congr rfl
  intro i _
  cases ha : active i
  · simp only [Bool.false_eq_true, ite_false, if_false, norm_one, one_pow]
  · simp only [ite_true, if_true]
    congr 2
    simp only [div_eq_mul_inv, Nat.cast_mul]
    congr 2
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternPermutedProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The common regular product under an arbitrary bulk matching -/

namespace Ostmann
open scoped Classical

theorem bulkSlotLeaves_perm_matching {σ : Type*} (n m : ℕ)
    (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) :
    (flattenMovingSlots n (bulkSlotLeaves n m (slot ∘ perm.symm))).Perm
      (flattenMovingSlots n (bulkSlotLeaves n m slot)) := by
  apply (List.perm_ext_iff_of_nodup
    (bulkSlotLeaves_nodup n m _ (slot.injective.comp perm.symm.injective))
    (bulkSlotLeaves_nodup n m slot slot.injective)).mpr
  intro i
  rw [mem_flatten_bulkSlotLeaves, mem_flatten_bulkSlotLeaves]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨perm.symm j, hj⟩
  · rintro ⟨j, hj⟩
    refine ⟨perm j, ?_⟩
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hj

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedBulkPermutation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Permuting only the selected bulk coordinates in the original law -/

namespace Ostmann
open scoped Classical BigOperators

/-- Only the selected coordinates need identical distributions. -/
theorem selectedBulkSample_prior {B J A : Type*} [Fintype B]
    (slot : J ↪ B) (e : Equiv.Perm J) (ν : B → A → ℝ)
    (hν : ∀ j k, ν (slot j) = ν (slot k)) (y : B → A) :
    (∏ i, ν i (selectedBulkSample slot e y i)) = ∏ i, ν i (y i) := by
  have hpres (i : B) : ν i = ν ((selectedBulkPerm slot e).symm i) := by
    obtain ⟨j, rfl⟩ := (selectedIndexEquiv slot).surjective i
    cases j with
    | inl j => simpa using hν j (e.symm j)
    | inr i => simp [i.property]
  calc
    _ = ∏ i, ν ((selectedBulkPerm slot e).symm i)
        (y ((selectedBulkPerm slot e).symm i)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [hpres i]
      rfl
    _ = _ := (selectedBulkPerm slot e).symm.prod_comp (fun i => ν i (y i))

theorem selectedBulkSample_sum {B J A : Type*} [Fintype B] [Fintype A]
    (slot : J ↪ B) (e : Equiv.Perm J) (ν : B → A → ℝ)
    (hν : ∀ j k, ν (slot j) = ν (slot k)) (F : (B → A) → ℂ) :
    (∑ y, ((∏ i, ν i (y i) : ℝ) : ℂ) * F (selectedBulkSample slot e y)) =
      ∑ y, ((∏ i, ν i (y i) : ℝ) : ℂ) * F y := by
  have h := (bulkArrayEquiv (A := A) (selectedBulkPerm slot e)).sum_comp
    (fun y => ((∏ i, ν i (y i) : ℝ) : ℂ) * F y)
  change (∑ y, ((∏ i, ν i (selectedBulkSample slot e y i) : ℝ) : ℂ) *
    F (selectedBulkSample slot e y)) = _ at h
  simpa only [selectedBulkSample_prior slot e ν hν] using h

theorem selectedBulkSample_bulk_leaves {B A : Type*} (n m : ℕ)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (e : Equiv.Perm (TreeLeafIndex n × Fin m)) (y : B → A) :
    treeLeafMap (List.map (selectedBulkSample slot e y)) n (bulkSlotLeaves n m slot) =
      treeLeafMap (List.map y) n (bulkSlotLeaves n m (slot ∘ e.symm)) := by
  simp only [bulkSlotLeaves_map]
  congr 1
  funext j
  exact selectedBulkSample_bulk slot e y j

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedExternalAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original root, prime and integer average as one finite positive law -/

namespace Ostmann
open scoped Classical BigOperators

theorem mixedExternalPrior_nonneg {B A : Type*} [Fintype B]
    (ν : B → A → ℝ) (hν : ∀ b a, 0 ≤ ν b a)
    (N : ℕ) (u v r w center : ℝ) (x : MixedExternalPoint B A N u v r w) :
    0 ≤ mixedExternalPrior ν N u v r w center x := by
  unfold mixedExternalPrior
  apply mul_nonneg
  · exact mul_nonneg (Finset.prod_nonneg fun b _ => hν b _) (by split_ifs <;> positivity)
  · exact integerResidueAtom_nonneg 1 0 center _

theorem mixedExternalAverage_finite {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) :
    mixedExternalAverage ν N u v r w center F =
      ∑ x : MixedExternalPoint B A N u v r w,
        (mixedExternalPrior ν N u v r w center x : ℂ) *
          F x.1.val x.2.1 (Real.log x.2.2.2.val) (Real.log x.2.2.1.val) := by
  have hp (F : ℝ → ℂ) : complexPrimeInterval 1 0 r w F =
      ∑ p : Finset.Ioc ⌊Real.exp r⌋₊ ⌊Real.exp w⌋₊,
        if (p.val).Prime then F (Real.log p.val) * ((p.val : ℝ)⁻¹ : ℂ) else 0 := by
    rw [Finset.sum_coe_sort _ (fun p : ℕ =>
      if p.Prime then F (Real.log p) * ((p : ℝ)⁻¹ : ℂ) else 0)]
    simp only [complexPrimeInterval, Nat.modEq_one, and_true]
  have hi (F : ℝ → ℂ) : complexIntegerInterval 1 0 u v center F =
      ∑ q : Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊,
        F (Real.log q.val) * (integerResidueAtom 1 0 center q.val : ℂ) := by
    rw [Finset.sum_coe_sort _ (fun q : ℕ =>
      F (Real.log q) * (integerResidueAtom 1 0 center q : ℂ))]
    rfl
  simp only [mixedExternalAverage, hp, hi, MixedExternalPoint,
    Fintype.sum_prod_type, mixedExternalPrior]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hprime : (p.val).Prime
  · simp only [hprime, ite_true, if_true, Complex.ofReal_mul]
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    push_cast
    ring
  · simp only [hprime, ite_false, if_false, mul_zero, zero_mul, Complex.ofReal_zero,
      Finset.sum_const_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOriginalBulkAction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original coefficient and common transform under bulk reassignment -/

namespace Ostmann
open scoped Classical BigOperators

theorem MovingSlotReversal.naturalProduct_selected_bulk {B A : Type*}
    (value : A → ℕ) (n m : ℕ) (small : TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (e : Equiv.Perm (TreeLeafIndex n × Fin m)) (y : B → A)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot) :
    naturalProduct (value ∘ selectedBulkSample slot e y)
      (flattenMovingSlots n small ++ flattenMovingSlots n (bulkSlotLeaves n m slot)) =
    naturalProduct (value ∘ y)
      (flattenMovingSlots n small ++ flattenMovingSlots n (bulkSlotLeaves n m slot)) := by
  have hs : (flattenMovingSlots n small).map (selectedBulkSample slot e y) =
      (flattenMovingSlots n small).map y :=
    List.map_congr_left (fun i hi => selectedBulkSample_nonbulk slot e y i (hsmall i hi))
  have hb : (flattenMovingSlots n (bulkSlotLeaves n m slot)).map (selectedBulkSample slot e y) =
      (flattenMovingSlots n (bulkSlotLeaves n m (slot ∘ e.symm))).map y := by
    rw [← flattenMovingSlots_map, selectedBulkSample_bulk_leaves, flattenMovingSlots_map]
  unfold naturalProduct
  simp only [← List.map_map, List.map_append, List.prod_append]
  rw [hs, hb]
  exact congrArg (_ * ·) (((bulkSlotLeaves_perm_matching n m slot e).map y).map value).prod_eq

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedExternalPermutation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing the original mixed external law by its selected bulk coordinates -/

namespace Ostmann
open scoped Classical BigOperators

theorem mixedExternalAverage_selectedBulkSample {B J A : Type*}
    [Fintype B] [Fintype A]
    (slot : J ↪ B) (e : Equiv.Perm J) (ν : B → A → ℝ)
    (hν : ∀ j k, ν (slot j) = ν (slot k))
    (N : ℕ) (u v r w center : ℝ) (F : ℤ → (B → A) → ℝ → ℝ → ℂ) :
    mixedExternalAverage ν N u v r w center
      (fun s y x z => F s (selectedBulkSample slot e y) x z) =
    mixedExternalAverage ν N u v r w center F := by
  unfold mixedExternalAverage
  apply Finset.sum_congr rfl
  intro s _
  exact selectedBulkSample_sum slot e ν hν
    (fun y => complexPrimeInterval 1 0 r w (fun z =>
      complexIntegerInterval 1 0 u v center (fun x => F s.val y x z)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedExternalStatistic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original statistic is unchanged by bulk symmetrization -/

namespace Ostmann
open scoped Classical BigOperators

theorem mixedExternalAverage_sum {B A J : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r w center : ℝ)
    (T : Finset J) (F : J → ℤ → (B → A) → ℝ → ℝ → ℂ) :
    mixedExternalAverage ν N u v r w center (fun s y x z => ∑ j ∈ T, F j s y x z) =
      ∑ j ∈ T, mixedExternalAverage ν N u v r w center (F j) := by
  simp only [mixedExternalAverage_finite, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem mixedExternalAverage_const_mul {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r w center : ℝ)
    (c : ℂ) (F : ℤ → (B → A) → ℝ → ℝ → ℂ) :
    mixedExternalAverage ν N u v r w center (fun s y x z => c * F s y x z) =
      c * mixedExternalAverage ν N u v r w center F := by
  simp only [mixedExternalAverage_finite, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem mixedBulkSymmetrize_statistic {B A : Type*} [Fintype B] [Fintype A]
    (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (ν : B → A → ℝ) (hν : ∀ j k, ν (slot j) = ν (slot k))
    (N : ℕ) (u v r w center : ℝ)
    (F H : ℤ → (B → A) → ℝ → ℝ → ℂ)
    (hH : ∀ e s y x z, H s (selectedBulkSample slot e y) x z = H s y x z) :
    mixedExternalAverage ν N u v r w center
      (fun s y x z => H s y x z * mixedBulkSymmetrize n m slot F s y x z) =
    mixedExternalAverage ν N u v r w center (fun s y x z => H s y x z * F s y x z) := by
  let J := Equiv.Perm (TreeLeafIndex n × Fin m)
  have hc : (Fintype.card J : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := J)
  have he (e : J) : mixedExternalAverage ν N u v r w center
      (fun s y x z => H s y x z * F s (selectedBulkSample slot e⁻¹ y) x z) =
      mixedExternalAverage ν N u v r w center (fun s y x z => H s y x z * F s y x z) := by
    have h := mixedExternalAverage_selectedBulkSample slot e⁻¹ ν hν N u v r w center
      (fun s y x z => H s y x z * F s y x z)
    simpa only [hH] using h
  have hpoint : (fun s y x z => H s y x z * mixedBulkSymmetrize n m slot F s y x z) =
      (fun s y x z => (Fintype.card J : ℂ)⁻¹ * ∑ e : J,
        H s y x z * F s (selectedBulkSample slot e⁻¹ y) x z) := by
    funext s y x z
    simp only [mixedBulkSymmetrize, finiteFamilyAverage, ← Finset.mul_sum]
    ring
  rw [hpoint, mixedExternalAverage_const_mul, mixedExternalAverage_sum]
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem mixedExternalAverage_weighted_cauchy {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (hν : ∀ b a, 0 ≤ ν b a)
    (N : ℕ) (u v r w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (W : ℤ → (B → A) → ℝ → ℝ → ℝ)
    (hW : ∀ s y x z, 0 ≤ W s y x z) :
    ‖mixedExternalAverage ν N u v r w center (fun s y x z => F s y x z * W s y x z)‖ ^ 2 ≤
      (mixedExternalAverage ν N u v r w center (fun s y x z => (W s y x z : ℂ))).re *
      (mixedExternalAverage ν N u v r w center
        (fun s y x z => (‖F s y x z‖ ^ 2 : ℂ) * W s y x z)).re := by
  let ρ := fun x : MixedExternalPoint B A N u v r w =>
    mixedExternalPrior ν N u v r w center x *
      W x.1.val x.2.1 (Real.log x.2.2.2.val) (Real.log x.2.2.1.val)
  let f := fun x : MixedExternalPoint B A N u v r w =>
    F x.1.val x.2.1 (Real.log x.2.2.2.val) (Real.log x.2.2.1.val)
  have hρ (x) : 0 ≤ ρ x := mul_nonneg
    (mixedExternalPrior_nonneg ν hν N u v r w center x) (hW _ _ _ _)
  have he (x) : Real.sqrt (ρ x) ^ 2 = ρ x := Real.sq_sqrt (hρ x)
  have hprod (x) : (Real.sqrt (ρ x) : ℂ) * ((Real.sqrt (ρ x) : ℂ) * f x) =
      (ρ x : ℂ) * f x := by
    rw [← mul_assoc, ← pow_two, ← Complex.ofReal_pow, he]
  have hc := complex_pairing_sq_le (fun x => (Real.sqrt (ρ x) : ℂ))
    (fun x => (Real.sqrt (ρ x) : ℂ) * f x)
  simp only [hprod, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, he] at hc
  simp only [mixedExternalAverage_finite, Complex.re_sum, Complex.mul_re,
    ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
    sub_zero]
  convert hc using 1
  · congr 2
    apply Finset.sum_congr rfl
    intro x _
    dsimp [ρ, f]
    push_cast
    ring
  · apply congrArg₂ (· * ·)
    · rfl
    · apply Finset.sum_congr rfl
      intro x _
      dsimp [ρ, f]
      ring

theorem mixedBulkSymmetrize_statistic_cauchy {B A : Type*} [Fintype B] [Fintype A]
    (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (ν : B → A → ℝ) (hν : ∀ b a, 0 ≤ ν b a)
    (hidentical : ∀ j k, ν (slot j) = ν (slot k))
    (N : ℕ) (u v r w center : ℝ)
    (F H : ℤ → (B → A) → ℝ → ℝ → ℂ)
    (hH : ∀ e s y x z, H s (selectedBulkSample slot e y) x z = H s y x z)
    (W : ℝ → ℝ → ℝ) (hW : ∀ x z, 0 ≤ W x z) :
    ‖mixedExternalAverage ν N u v r w center
      (fun s y x z => (H s y x z * F s y x z) * W x z)‖ ^ 2 ≤
    (mixedExternalAverage ν N u v r w center (fun _ _ x z => (W x z : ℂ))).re *
    (mixedExternalAverage ν N u v r w center (fun s y x z =>
      (‖mixedBulkSymmetrize n m slot F s y x z‖ ^ 2 : ℂ) *
        ((W x z : ℂ) * (‖H s y x z‖ ^ 2 : ℝ)))).re := by
  have hs := mixedBulkSymmetrize_statistic n m slot ν hidentical N u v r w center
    F (fun s y x z => H s y x z * W x z) (fun e s y x z => by rw [hH])
  have hm : mixedExternalAverage ν N u v r w center
      (fun s y x z => (H s y x z * F s y x z) * W x z) =
    mixedExternalAverage ν N u v r w center (fun s y x z =>
      (H s y x z * mixedBulkSymmetrize n m slot F s y x z) * W x z) := by
    calc
      _ = mixedExternalAverage ν N u v r w center
          (fun s y x z => (H s y x z * W x z) * F s y x z) := by
        congr 1; funext s y x z; ring
      _ = _ := by
        rw [← hs]
        congr 1; funext s y x z; ring
  rw [hm]
  have hc := mixedExternalAverage_weighted_cauchy ν hν N u v r w center
    (fun s y x z => H s y x z * mixedBulkSymmetrize n m slot F s y x z)
    (fun _ _ x z => W x z) (fun _ _ x z => hW x z)
  have heq : (fun s y x z =>
      (‖mixedBulkSymmetrize n m slot F s y x z‖ ^ 2 : ℂ) *
        ((W x z : ℂ) * (‖H s y x z‖ ^ 2 : ℝ))) =
      (fun s y x z => (‖H s y x z * mixedBulkSymmetrize n m slot F s y x z‖ ^ 2 : ℂ) * W x z) := by
    funext s y x z
    simp only [norm_mul, mul_pow, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  rw [heq]
  exact hc

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOriginalStatistic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original mixed arithmetic statistic and its symmetrized upper bound -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem giantOuterWeight_positive (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (Jleft Jright : ℝ) (diagonal : Bool) (L R : ℝ) :
    ∃ a : ℝ, 0 ≤ a ∧ giantOuterWeight φ Jleft Jright diagonal L R = a := by
  have hc (x J : ℝ) : 0 ≤ positiveLogCutoff φ J x := by
    unfold positiveLogCutoff
    split_ifs
    · exact hφ _
    · exact le_rfl
  refine ⟨positiveLogCutoff φ Jleft L * positiveLogCutoff φ Jright R *
    (if diagonal then Real.exp Jright / R else 1), ?_, ?_⟩
  · have hratio : 0 ≤ (if diagonal then Real.exp Jright / R else 1) ∨ R ≤ 0 := by
      by_cases hR : 0 ≤ R
      · left; split_ifs <;> positivity
      · exact Or.inr (le_of_not_ge hR)
    rcases hratio with hratio | hR
    · exact mul_nonneg (mul_nonneg (hc _ _) (hc _ _)) hratio
    · simp only [positiveLogCutoff, not_lt.mpr hR, ite_false, if_false, mul_zero, zero_mul]
      exact le_rfl
  · unfold giantOuterWeight
    cases diagonal <;> simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true] <;> push_cast <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PhaseGiantTest
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Fourier-phase giant and its real physical inverse -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem complexUnitPhase_norm_le (z : ℂ) : ‖complexUnitPhase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · simp only [complexUnitPhase, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    rw [div_self (norm_ne_zero_iff.mpr hz)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGiantPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two original giant Fourier phases on a fixed product fibre -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingGiantPhase_norm_le {σ B : Type*} {n : ℕ}
    (value : σ → ℕ) (outside : List ℕ) (small bulk : TreeLeafTuple (List B) n)
    (g : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (s : ℤ) (y : B → σ) (x z : ℝ) :
    ‖movingGiantPhase value outside small bulk g favorable s y x z‖ ≤ 1 := by
  unfold movingGiantPhase giantPairPhase
  rw [norm_mul]
  apply (mul_le_mul _ _ (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  all_goals split_ifs <;> first | exact complexUnitPhase_norm_le _ | simp

theorem movingGiantPhase_selectedBulkSample {σ B : Type*} [Fintype B]
    (value : σ → ℕ) (outside : List ℕ) (n m : ℕ)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (e : Equiv.Perm (TreeLeafIndex n × Fin m)) (y : B → σ)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot)
    (g : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (s : ℤ) (x z : ℝ) :
    movingGiantPhase value outside small (bulkSlotLeaves n m slot) g favorable s
      (selectedBulkSample slot e y) x z =
    movingGiantPhase value outside small (bulkSlotLeaves n m slot) g favorable s y x z := by
  unfold movingGiantPhase
  rw [MovingSlotReversal.naturalProduct_selected_bulk value n m small slot e y hsmall]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingNormalizedFinalRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The final numerical contradiction retains both giant normalizers -/
namespace Ostmann
open Filter

theorem moving_normalized_amplitude_lower (B r m cg : ℝ) (η statistic : ℂ)
    (hloss : 2 * cg ≤ r * m)
    (hid : η = (Real.exp (2 * cg) : ℂ) * statistic)
    (hlower : Real.exp (-B * r * m) ≤ ‖η‖) :
    Real.exp (-(B + 1) * r * m) ≤ ‖statistic‖ := by
  rw [hid, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)] at hlower
  have h := mul_le_mul_of_nonneg_left hlower (Real.exp_nonneg (-2 * cg))
  have hinv : Real.exp (-2 * cg) * Real.exp (2 * cg) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  have hs : Real.exp (-2 * cg + -B * r * m) ≤ ‖statistic‖ := by
    calc
      _ = Real.exp (-2 * cg) * Real.exp (-B * r * m) := Real.exp_add _ _
      _ ≤ Real.exp (-2 * cg) * (Real.exp (2 * cg) * ‖statistic‖) := h
      _ = _ := by rw [← mul_assoc, hinv, one_mul]
  exact (Real.exp_le_exp.mpr (by nlinarith only [hloss])).trans hs

theorem eventually_moving_normalized_numeric_contradiction (Bs BD Bz B C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ k : ℕ in atTop, ∀ᶠ L : ℝ in atTop,
      let m := spectatorBulkCount k L
      let r : ℝ := (2 : ℝ) ^ k
      let A := movingFrequencyRate Bs BD Bz ((k : ℝ) ^ 4) k
      let D := Bs + 8 * Real.log ((k : ℝ) ^ 4)
      ∀ V : ℕ, (V : ℝ) ≤ Real.exp (A * m) → 0 ≤ A →
      ∀ Δ cg : ℝ, Δ ≤ D * m → cg ≤ L → ∀ η statistic : ℂ,
      η = (Real.exp (2 * cg) : ℂ) * statistic →
      Real.exp (-B * r * m) ≤ ‖η‖ →
      ‖statistic‖ ^ 2 ≤ C * (2 * V + 1 : ℕ) * Real.exp 5 *
        (4 * ((((2 ^ k + 1) * (2 ^ k) ^ (2 * 2 ^ k) : ℕ) : ℝ) *
          Real.exp (r * m * (-(3 / 4 : ℝ) * Real.log ((2 : ℝ) ^ k) + 5 / 4)) *
            (Real.exp (r * Δ + (Real.log 12 + 1) * r * m + m) +
              5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) +
          Real.exp (-(A + (2 * (B + 1) + 1) * r + 1) * m) +
            5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)))) → False := by
  filter_upwards [eventually_moving_numeric_contradiction Bs BD Bz (B + 1)
    (4 * C * Real.exp 3) (by positivity), eventually_ge_atTop (2 : ℕ)] with k hk hk2
  filter_upwards [hk, eventually_ge_atTop (1 : ℝ)] with L hfinal hL
  dsimp only at hfinal ⊢
  intro V hV hA Δ cg hΔ hcg η statistic hid hlower hupper
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hk4 : (16 : ℝ) ≤ (k : ℝ) ^ 4 := by
    convert pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hkR 4 using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have hm := spectatorBulkCount_lower k L
  have hr : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hloss : 2 * cg ≤ (2 : ℝ) ^ k * spectatorBulkCount k L := by
    have hm2 : 2 * L ≤ (spectatorBulkCount k L : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_right hk4 (show 0 ≤ L by linarith)]
    have hrm := mul_le_mul_of_nonneg_right hr (show 0 ≤ (spectatorBulkCount k L : ℝ) by positivity)
    nlinarith
  apply hfinal V hV hA Δ hΔ statistic
    (moving_normalized_amplitude_lower B (2 ^ k) (spectatorBulkCount k L) cg η statistic hloss hid hlower)
  have hexp : Real.exp 5 = Real.exp 3 * Real.exp 2 := by
    rw [← Real.exp_add]
    norm_num
  convert hupper using 1
  all_goals try with_reducible_and_instances rfl
  rw [hexp]
  ring

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

theorem movingTemplateSmall_not_bulk (n r m : ℕ) :
    ∀ i ∈ flattenMovingSlots n (movingTemplateSmall n r m), i ∉ Set.range (movingTemplateBulk n r m) := by
  intro i hi hbulk
  obtain ⟨j, rfl⟩ := (mem_flatten_bulkSlotLeaves n r _ i).mp hi
  obtain ⟨k, hk⟩ := hbulk
  have hs : (Sum.inr k.2 : Fin r ⊕ Fin m) = .inl j.2 :=
    congrArg (fun z : MovingRegularSlot n r m => z.2) hk
  cases hs

theorem movingRegularSlot_card (n r m : ℕ) :
    Fintype.card (MovingRegularSlot n r m) = 2 ^ n * (r + m) := by
  simp only [MovingRegularSlot, Fintype.card_prod, card_treeLeafIndex, Fintype.card_sum,
    Fintype.card_fin]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedExternalMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary total-mass bounds for the original mixed external law -/

namespace Ostmann
open scoped Classical BigOperators

theorem complexIntegerInterval_const (u v center : ℝ) (c : ℂ) :
    complexIntegerInterval 1 0 u v center (fun _ => c) =
      (integerLogCellMass 1 0 u v center : ℂ) * c := by
  simp only [complexIntegerInterval, integerLogCellMass, Complex.ofReal_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem complexPrimeInterval_const (r w : ℝ) (c : ℂ) :
    complexPrimeInterval 1 0 r w (fun _ => c) =
      (reciprocalPrimeInterval 1 0 (Real.exp r) (Real.exp w) : ℂ) * c := by
  simp only [complexPrimeInterval, reciprocalPrimeInterval, Complex.ofReal_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp_all [mul_comm]

theorem mixedExternalAverage_const {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (hmass : ∀ b, ∑ a, ν b a = 1)
    (N : ℕ) (u v r w center : ℝ) (c : ℂ) :
    mixedExternalAverage ν N u v r w center (fun _ _ _ _ => c) =
      (((2 * N + 1 : ℕ) : ℝ) * reciprocalPrimeInterval 1 0 (Real.exp r) (Real.exp w) *
        integerLogCellMass 1 0 u v center : ℝ) * c := by
  simp only [mixedExternalAverage, complexIntegerInterval_const, complexPrimeInterval_const]
  have hν : ∑ y : B → A, (∏ b, ν b (y b) : ℝ) = 1 := by
    rw [← Fintype.prod_sum]
    simp only [hmass, Finset.prod_const_one]
  simp only [← Finset.sum_mul, ← Complex.ofReal_sum, hν, Complex.ofReal_one, one_mul]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, card_transferFrequencyRange,
    nsmul_eq_mul, Complex.ofReal_mul, Complex.ofReal_natCast]
  ring

theorem integerLogCellMass_le_exp (u v center : ℝ) :
    integerLogCellMass 1 0 u v center ≤ Real.exp (v - center) := by
  simp only [integerLogCellMass, integerResidueAtom, Nat.modEq_one, ite_true, if_true,
    Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
  calc
    _ ≤ Real.exp v * Real.exp (-center) :=
      mul_le_mul_of_nonneg_right
        ((Nat.cast_le.mpr (Nat.sub_le _ _)).trans (Nat.floor_le (Real.exp_pos _).le))
        (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, sub_eq_add_neg]

theorem mixedExternalAverage_mass_bound {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (hν : ∀ b a, 0 ≤ ν b a) (hmass : ∀ b, ∑ a, ν b a = 1)
    (N : ℕ) (u v r w center C : ℝ) (hC : 0 ≤ C)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (hF : ∀ s y x z, (F s y x z).re ≤ C) :
    (mixedExternalAverage ν N u v r w center F).re ≤
      C * (2 * N + 1 : ℕ) * Real.exp ((w - r) + (v - center)) := by
  have hunit : (mixedExternalAverage ν N u v r w center (fun _ _ _ _ => (1 : ℂ))).re =
      ((2 * N + 1 : ℕ) : ℝ) * reciprocalPrimeInterval 1 0 (Real.exp r) (Real.exp w) *
        integerLogCellMass 1 0 u v center := by
    rw [mixedExternalAverage_const ν hmass]
    simp
  have hbound : (mixedExternalAverage ν N u v r w center F).re ≤
      C * (mixedExternalAverage ν N u v r w center (fun _ _ _ _ => (1 : ℂ))).re := by
    simp only [mixedExternalAverage_finite, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_one, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    exact (mul_le_mul_of_nonneg_left (hF _ _ _ _)
      (mixedExternalPrior_nonneg ν hν N u v r w center x)).trans_eq (by ring)
  rw [hunit] at hbound
  apply hbound.trans
  rw [Real.exp_add]
  have hp := reciprocalPrimeInterval_le_exp 1 0 r w
  have hi := integerLogCellMass_le_exp u v center
  have hp0 := reciprocalPrimeInterval_nonneg 1 0 (Real.exp r) (Real.exp w)
  have hi0 := integerLogCellMass_nonneg 1 0 u v center
  nlinarith [mul_le_mul hp hi hi0 (Real.exp_pos _).le,
    mul_nonneg hC (Nat.cast_nonneg (2 * N + 1))]

theorem mixedExternalAverage_re_nonneg {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (hν : ∀ b a, 0 ≤ ν b a)
    (N : ℕ) (u v r w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (hF : ∀ s y x z, 0 ≤ (F s y x z).re) :
    0 ≤ (mixedExternalAverage ν N u v r w center F).re := by
  simp only [mixedExternalAverage_finite, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact Finset.sum_nonneg (fun x _ => mul_nonneg
    (mixedExternalPrior_nonneg ν hν N u v r w center x) (hF _ _ _ _))

theorem mixedExternalAverage_re_mono {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (hν : ∀ b a, 0 ≤ ν b a)
    (N : ℕ) (u v r w center : ℝ)
    (F H : ℤ → (B → A) → ℝ → ℝ → ℂ)
    (hFH : ∀ s y x z, (F s y x z).re ≤ (H s y x z).re) :
    (mixedExternalAverage ν N u v r w center F).re ≤
      (mixedExternalAverage ν N u v r w center H).re := by
  simp only [mixedExternalAverage_finite, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
    (hFH _ _ _ _) (mixedExternalPrior_nonneg ν hν N u v r w center x))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedBoundedPhaseStatistic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded invariant giant factors do not enlarge the symmetrized energy -/

namespace Ostmann
open scoped Classical BigOperators

theorem mixedBulkSymmetrize_bounded_statistic_cauchy {B A : Type*} [Fintype B] [Fintype A]
    (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (ν : B → A → ℝ) (hν : ∀ b a, 0 ≤ ν b a)
    (hidentical : ∀ j k, ν (slot j) = ν (slot k))
    (N : ℕ) (u v r w center : ℝ)
    (F H P : ℤ → (B → A) → ℝ → ℝ → ℂ)
    (hH : ∀ e s y x z, H s (selectedBulkSample slot e y) x z = H s y x z)
    (hP : ∀ e s y x z, P s (selectedBulkSample slot e y) x z = P s y x z)
    (hPnorm : ∀ s y x z, ‖P s y x z‖ ≤ 1)
    (W : ℝ → ℝ → ℝ) (hW : ∀ x z, 0 ≤ W x z) :
    ‖mixedExternalAverage ν N u v r w center
      (fun s y x z => ((P s y x z * H s y x z) * F s y x z) * W x z)‖ ^ 2 ≤
    (mixedExternalAverage ν N u v r w center (fun _ _ x z => (W x z : ℂ))).re *
    (mixedExternalAverage ν N u v r w center (fun s y x z =>
      (‖mixedBulkSymmetrize n m slot F s y x z‖ ^ 2 : ℂ) *
        ((W x z : ℂ) * (‖H s y x z‖ ^ 2 : ℝ)))).re := by
  have hc := mixedBulkSymmetrize_statistic_cauchy n m slot ν hν hidentical N
    u v r w center F (fun s y x z => P s y x z * H s y x z)
    (fun e s y x z => by rw [hP, hH]) W hW
  apply hc.trans
  apply mul_le_mul_of_nonneg_left
  · apply mixedExternalAverage_re_mono ν hν N u v r w center
    intro s y x z
    simp only [norm_mul, mul_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    have hp : ‖P s y x z‖ ^ 2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (hPnorm s y x z) 2
    have hscale : 0 ≤ ‖mixedBulkSymmetrize n m slot F s y x z‖ ^ 2 * W x z := by
      exact mul_nonneg (sq_nonneg _) (hW x z)
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hp (sq_nonneg ‖H s y x z‖)) hscale
    nlinarith
  · exact mixedExternalAverage_re_nonneg ν hν N u v r w center _
      (fun _ _ x z => by simpa only [Complex.ofReal_re] using hW x z)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeExternalAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing from the integer/prime comparison law to two prime giants -/

namespace Ostmann
open scoped Classical BigOperators

theorem leftPrimeDensity_nonneg (u x : ℝ) : 0 ≤ leftPrimeDensity u x := by
  unfold leftPrimeDensity
  split_ifs <;> positivity

theorem leftPrimeDensity_le_one (u x : ℝ) : leftPrimeDensity u x ≤ 1 := by
  unfold leftPrimeDensity
  split_ifs with h
  · exact (div_le_one (Nat.cast_pos.mpr h.1.pos)).mpr h.2
  · exact zero_le_one

theorem leftPrimeDensity_norm_le_one (u x : ℝ) : ‖(leftPrimeDensity u x : ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real, Real.norm_of_nonneg (leftPrimeDensity_nonneg u x)] using
    leftPrimeDensity_le_one u x

theorem complexPrimeInterval_as_integer (u v center : ℝ) (F : ℝ → ℂ) :
    complexPrimeInterval 1 0 u v F = (Real.exp (center - u) : ℂ) *
      complexIntegerInterval 1 0 u v center (fun x => (leftPrimeDensity u x : ℂ) * F x) := by
  unfold complexPrimeInterval complexIntegerInterval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.zero_le _).trans_lt (Finset.mem_Ioc.mp hp).1
  have hlow : Real.exp u ≤ (p : ℝ) := by
    exact (Nat.lt_of_floor_lt (Finset.mem_Ioc.mp hp).1).le
  simp only [leftPrimeDensity, Real.exp_log hp0, Nat.floor_natCast,
    integerResidueAtom, Nat.modEq_one, ite_true, if_true, and_true]
  by_cases hprime : p.Prime
  · simp only [hprime, hlow, and_self, ite_true, if_true, Complex.ofReal_div]
    have he : Real.exp (center - u) * Real.exp u * Real.exp (-center) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    have heC : (Real.exp (center - u) : ℂ) * (Real.exp u : ℂ) * (Real.exp (-center) : ℂ) = 1 := by
      exact_mod_cast he
    calc
      _ = ((Real.exp (center - u) : ℂ) * (Real.exp u : ℂ) * (Real.exp (-center) : ℂ)) *
          (F (Real.log p) * ((p : ℝ) : ℂ)⁻¹) := by rw [heC]; ring
      _ = _ := by ring
  · simp only [hprime, false_and, ite_false, if_false, Complex.ofReal_zero, zero_mul, mul_zero]

theorem primeExternalAverage_as_mixed {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) :
    primeExternalAverage ν N u v r w F = (Real.exp (center - u) : ℂ) *
      mixedExternalAverage ν N u v r w center
        (fun s y x z => (leftPrimeDensity u x : ℂ) * F s y x z) := by
  simp only [primeExternalAverage, mixedExternalAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro y _
  rw [show (fun z => complexPrimeInterval 1 0 u v (fun x => F s.val y x z)) =
      (fun z => (Real.exp (center - u) : ℂ) * complexIntegerInterval 1 0 u v center
        (fun x => (leftPrimeDensity u x : ℂ) * F s.val y x z)) from
      funext (fun z => complexPrimeInterval_as_integer u v center _)]
  simp only [complexPrimeInterval, mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> ring

/-- The same bulk symmetrization applies to two genuine prime giants. Only
one explicit scalar is lost when passing to the integer comparison law. -/
theorem primeExternalAverage_bounded_statistic_cauchy {B A : Type*} [Fintype B] [Fintype A]
    (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (ν : B → A → ℝ) (hν : ∀ b a, 0 ≤ ν b a)
    (hidentical : ∀ j k, ν (slot j) = ν (slot k))
    (N : ℕ) (u v r w center : ℝ)
    (F H P : ℤ → (B → A) → ℝ → ℝ → ℂ)
    (hH : ∀ e s y x z, H s (selectedBulkSample slot e y) x z = H s y x z)
    (hP : ∀ e s y x z, P s (selectedBulkSample slot e y) x z = P s y x z)
    (hPnorm : ∀ s y x z, ‖P s y x z‖ ≤ 1)
    (W : ℝ → ℝ → ℝ) (hW : ∀ x z, 0 ≤ W x z) :
    ‖primeExternalAverage ν N u v r w
      (fun s y x z => ((P s y x z * H s y x z) * F s y x z) * W x z)‖ ^ 2 ≤
    Real.exp (center - u) ^ 2 *
    (mixedExternalAverage ν N u v r w center (fun _ _ x z => (W x z : ℂ))).re *
    (mixedExternalAverage ν N u v r w center (fun s y x z =>
      (‖mixedBulkSymmetrize n m slot F s y x z‖ ^ 2 : ℂ) *
        ((W x z : ℂ) * (‖H s y x z‖ ^ 2 : ℝ)))).re := by
  let Q := fun s y x z => (leftPrimeDensity u x : ℂ) * P s y x z
  have hQ (e s y x z) : Q s (selectedBulkSample slot e y) x z = Q s y x z := by
    dsimp only [Q]
    rw [hP]
  have hQnorm (s y x z) : ‖Q s y x z‖ ≤ 1 := by
    dsimp only [Q]
    rw [norm_mul]
    exact (mul_le_mul (leftPrimeDensity_norm_le_one u x) (hPnorm s y x z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hc := mixedBulkSymmetrize_bounded_statistic_cauchy n m slot ν hν hidentical N
    u v r w center F H Q hH hQ hQnorm W hW
  have heq : (fun s y x z => (leftPrimeDensity u x : ℂ) *
      (((P s y x z * H s y x z) * F s y x z) * W x z)) =
      (fun s y x z => ((Q s y x z * H s y x z) * F s y x z) * W x z) := by
    funext s y x z
    dsimp only [Q]
    ring
  rw [primeExternalAverage_as_mixed ν N u v r w center, heq, norm_mul, mul_pow]
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact (mul_le_mul_of_nonneg_left hc (sq_nonneg _)).trans_eq (by ring)

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

/-- The finite support may include extra endpoints, but those have zero
smooth weight; every contributing prime lies in the complete cell. -/
theorem smoothGiant_unnormalized_interval (φ : ℝ → ℝ) (G : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (F : ℕ → ℂ) :
    (∑ p ∈ smoothGiantPrimeRange G,
      (φ (Real.log p - G) : ℂ) * F p * ((p : ℝ)⁻¹ : ℂ)) =
    complexPrimeInterval 1 0 (G - 1) (G + 1)
      (fun x => (φ (x - G) : ℂ) * F ⌊Real.exp x⌋₊) := by
  let Q := (Finset.Ioc ⌊Real.exp (G - 1)⌋₊ ⌊Real.exp (G + 1)⌋₊).filter Nat.Prime
  have hQP : Q ⊆ smoothGiantPrimeRange G := by
    intro p hp
    obtain ⟨hpI, hprime⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hprime.pos, ?_⟩, hprime⟩
    have hu : (p : ℝ) ≤ Real.exp (G + 1) :=
      (Nat.cast_le.mpr (Finset.mem_Ioc.mp hpI).2).trans (Nat.floor_le (Real.exp_nonneg _))
    exact_mod_cast hu.trans (Nat.le_ceil (Real.exp (G + 1)))
  have hs := Finset.sum_subset (f := fun (p : ℕ) =>
    (φ (Real.log p - G) : ℂ) * F p * ((p : ℝ)⁻¹ : ℂ)) hQP (fun p hp hn => by
    have hz : φ (Real.log p - G) = 0 := by
      by_contra hz
      apply hn
      exact Finset.mem_filter.mpr ⟨smoothGiant_nonzero_in_log_cell φ G hout p
        (smoothGiantPrimeRange_prime G p hp).pos hz, smoothGiantPrimeRange_prime G p hp⟩
    simp only [hz, Complex.ofReal_zero, zero_mul])
  rw [← hs]
  dsimp only [Q]
  rw [Finset.sum_filter]
  unfold complexPrimeInterval
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : (0 : ℝ) < p := by
    exact_mod_cast (Nat.zero_le _).trans_lt (Finset.mem_Ioc.mp hp).1
  simp only [Nat.modEq_one, and_true, Real.exp_log hp', Nat.floor_natCast]

/-- The normalizer is retained explicitly when the original giant law is
written as a prime logarithmic integral. -/
theorem smoothGiantPrior_interval (φ : ℝ → ℝ) (G : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (F : ℕ → ℂ) :
    (∑ p : smoothGiantPrimeRange G,
      (smoothGiantPrior (smoothGiantPrimeRange G) φ G p : ℂ) * F p) =
    (Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G) : ℂ) *
      complexPrimeInterval 1 0 (G - 1) (G + 1)
        (fun x => (φ (x - G) : ℂ) * F ⌊Real.exp x⌋₊) := by
  rw [← smoothGiant_unnormalized_interval φ G hout F, Finset.mul_sum]
  have he := Finset.sum_coe_sort (smoothGiantPrimeRange G) (fun p =>
    ((Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G) : ℂ) *
      ((φ (Real.log p - G) : ℂ) * F p * ((p : ℝ)⁻¹ : ℂ))))
  rw [← he]
  apply Finset.sum_congr rfl
  intro p _
  simp only [smoothGiantPrior, Complex.ofReal_div, Complex.ofReal_mul]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantExternalAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two original normalized giant priors in the exterior average -/

namespace Ostmann
open scoped Classical BigOperators

theorem smoothGiantPrior_pair_interval (φ : ℝ → ℝ) (G H : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (F : ℕ → ℕ → ℂ) :
    (∑ q : smoothGiantPrimeRange H,
      (smoothGiantPrior (smoothGiantPrimeRange H) φ H q : ℂ) *
        ∑ p : smoothGiantPrimeRange G,
          (smoothGiantPrior (smoothGiantPrimeRange G) φ G p : ℂ) * F p q) =
    (Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G +
      smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H) : ℂ) *
      complexPrimeInterval 1 0 (H - 1) (H + 1) (fun y =>
        complexPrimeInterval 1 0 (G - 1) (G + 1) (fun x =>
          (φ (x - G) : ℂ) * (φ (y - H) : ℂ) * F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) := by
  rw [smoothGiantPrior_interval φ H hout (fun q : ℕ =>
    ∑ p : smoothGiantPrimeRange G,
      (smoothGiantPrior (smoothGiantPrimeRange G) φ G p : ℂ) * F p q)]
  have hG (q : ℕ) := smoothGiantPrior_interval φ G hout (fun p => F p q)
  simp_rw [hG]
  have hf : (fun y => (φ (y - H) : ℂ) *
      ((Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G) : ℂ) *
        complexPrimeInterval 1 0 (G - 1) (G + 1)
          (fun x => (φ (x - G) : ℂ) * F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊))) =
    (fun y => (Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G) : ℂ) *
      complexPrimeInterval 1 0 (G - 1) (G + 1)
        (fun x => (φ (x - G) : ℂ) * (φ (y - H) : ℂ) * F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) := by
    funext y
    rw [show (fun x => (φ (x - G) : ℂ) * (φ (y - H) : ℂ) * F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊) =
      (fun x => (φ (y - H) : ℂ) * ((φ (x - G) : ℂ) * F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) from
      funext (fun _ => by ring), complexPrimeInterval_const_mul]
    ring
  rw [hf, complexPrimeInterval_const_mul, Real.exp_add, Complex.ofReal_mul]
  ring

theorem smoothGiantExternalAverage_eq {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (φ : ℝ → ℝ) (G H : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (F : ℤ → (B → A) → ℕ → ℕ → ℂ) :
    smoothGiantExternalAverage ν N φ G H F =
      (Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G +
        smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H) : ℂ) *
      primeExternalAverage ν N (G - 1) (G + 1) (H - 1) (H + 1)
        (fun s y x z => (φ (x - G) : ℂ) * (φ (z - H) : ℂ) * F s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊) := by
  unfold smoothGiantExternalAverage primeExternalAverage
  have hp (s : ℤ) (y : B → A) := smoothGiantPrior_pair_interval φ G H hout (F s y)
  simp_rw [hp]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro y _
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeExternalLogCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact positive-log cutoffs at the prime points of the exterior law -/

namespace Ostmann
open scoped Classical BigOperators

theorem primeExternalAverage_congr_primes {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r w : ℝ)
    (F H : ℤ → (B → A) → ℝ → ℝ → ℂ)
    (h : ∀ s y (p q : ℕ), p.Prime → q.Prime →
      F s y (Real.log p) (Real.log q) = H s y (Real.log p) (Real.log q)) :
    primeExternalAverage ν N u v r w F = primeExternalAverage ν N u v r w H := by
  unfold primeExternalAverage
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro y _
  apply congrArg (fun z : ℂ => ((∏ i, ν i (y i) : ℝ) : ℂ) * z)
  unfold complexPrimeInterval
  apply Finset.sum_congr rfl
  intro q _
  simp only [Nat.modEq_one, and_true]
  by_cases hq : q.Prime
  · rw [ite_eq_left hq, ite_eq_left hq]
    apply congrArg (fun z : ℂ => z * ((q : ℝ)⁻¹ : ℂ))
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.Prime
    · rw [ite_eq_left hp, ite_eq_left hp, h s.val y p q hp hq]
    · rw [ite_eq_right hp, ite_eq_right hp]
  · rw [ite_eq_right hq, ite_eq_right hq]

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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_NodeBulkProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preorder child products of the selected original prime leaves -/

namespace Ostmann
open scoped BigOperators

theorem treeLeafProduct_indexed {G : Type*} [CommMonoid G]
    (n : ℕ) (x : TreeLeafIndex n → G) :
    treeLeafProduct n ((treeLeafTupleEquiv G n).symm x) = ∏ i, x i := by
  induction n with
  | zero =>
    change Unit → G at x
    change x () = ∏ i : Unit, x i
    exact (Fintype.prod_subsingleton x ()).symm
  | succ n ih =>
    change (TreeLeafIndex n ⊕ TreeLeafIndex n) → G at x
    change treeLeafProduct n ((treeLeafTupleEquiv G n).symm (fun i => x (.inl i))) *
      treeLeafProduct n ((treeLeafTupleEquiv G n).symm (fun i => x (.inr i))) = _
    rw [ih, ih]
    change _ = ∏ i : TreeLeafIndex n ⊕ TreeLeafIndex n, x i
    exact (Fintype.prod_sum_type x).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact moduli of the regular-slot templates -/

namespace Ostmann
open scoped Classical BigOperators

theorem naturalProduct_bulkSlotLeaves {A : Type*} (value : A → ℕ) (n m : ℕ)
    (slot : TreeLeafIndex n × Fin m → A) :
    MovingSlotReversal.naturalProduct value (flattenMovingSlots n (bulkSlotLeaves n m slot)) =
      ∏ i, value (slot i) := by
  rw [movingSlotValues_flatten]
  have h : movingSlotValues value n (bulkSlotLeaves n m slot) =
      (treeLeafTupleEquiv ℕ n).symm (fun j => ∏ i : Fin m, value (slot (j, i))) := by
    apply (treeLeafTupleEquiv ℕ n).injective
    funext j
    rw [movingSlotValues_indexed, Equiv.apply_symm_apply]
    simp only [bulkSlotLeaves, Equiv.apply_symm_apply, MovingSlotReversal.naturalProduct,
      List.map_ofFn, List.prod_ofFn]
    rfl
  rw [h, treeLeafProduct_indexed, Fintype.prod_prod_type]

/-- Every regular coordinate occurs once in the small/bulk leaf lists. -/
theorem movingTemplate_product {A : Type*} (value : A → ℕ) (n r m : ℕ)
    (y : MovingRegularSlot n r m → A) :
    MovingSlotReversal.naturalProduct (value ∘ y)
      (flattenMovingSlots n (movingTemplateSmall n r m) ++
        flattenMovingSlots n (bulkSlotLeaves n m (movingTemplateBulk n r m))) =
      ∏ i, value (y i) := by
  rw [movingNaturalProduct_append]
  unfold movingTemplateSmall
  rw [naturalProduct_bulkSlotLeaves, naturalProduct_bulkSlotLeaves]
  simp only [MovingRegularSlot, Fintype.prod_prod_type, Fintype.prod_sum_type,
    Function.comp_apply, movingTemplateBulk]
  rw [Finset.prod_mul_distrib]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantTransformProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recombining the two giant phases with the common regular transform -/

namespace Ostmann
open scoped Classical BigOperators

private theorem bool_tupleCofactor (q : Bool → ℕ) [∀ b, Fact (q b).Prime] (b : Bool) :
    tupleCofactor q b = q (!b) := by
  have hp : 0 < q b := (Fact.out : (q b).Prime).pos
  have hh := tupleCofactor_mul q b
  rw [Fintype.prod_bool] at hh
  cases b <;> simp only [Bool.not_true, Bool.not_false] <;> nlinarith

attribute [local instance] OAI.Ostmann.giantProductSum_neZero
/-- The cofactor formula in the two-prime statistic is exactly the full
Fourier transform of the original ordered regular-prime tuple. -/
theorem movingRegularTransform_two_giant_phases {I : Type*} [Fintype I]
    (q : Bool → ℕ) (p : I → ℕ) [∀ b, Fact (q b).Prime] [∀ i, Fact (p i).Prime]
    (hp : Function.Injective p) (greg ggiant : ∀ r : ℕ, ZMod r → ℂ)
    (favorable : ℕ → Bool) (D : ℕ) (s : ℤ) :
    movingRegularTransform (Sum.elim q p)
      (fun i => match i with
        | .inl b => fun t => if favorable (q b) then complexUnitPhase (ggiant (q b) t) else 0
        | .inr j => greg (p j)) D s =
    ((if favorable (q true) then complexUnitPhase
      (ggiant (q true) ((s : ZMod (q true)) *
        ((D * q false * (∏ i, p i) : ℕ) : ZMod (q true))⁻¹)) else 0) *
      (if favorable (q false) then complexUnitPhase
      (ggiant (q false) ((s : ZMod (q false)) *
        ((D * q true * (∏ i, p i) : ℕ) : ZMod (q false))⁻¹)) else 0)) *
      primeProductTransform greg (D * q true * q false) (∏ i, p i) s := by
  have hs := moving_regular_transform_split q p
    (fun b t => if favorable (q b) then complexUnitPhase (ggiant (q b) t) else 0)
    (fun i => greg (p i)) D s
  have hfinal :
      movingRegularTransform q
        (fun b t => if favorable (q b) then complexUnitPhase (ggiant (q b) t) else 0)
        (D * ∏ i, p i) s *
      movingRegularTransform p (fun i => greg (p i)) (D * ∏ b, q b) s =
    ((if favorable (q true) then complexUnitPhase
      (ggiant (q true) ((s : ZMod (q true)) *
        ((D * q false * (∏ i, p i) : ℕ) : ZMod (q true))⁻¹)) else 0) *
      (if favorable (q false) then complexUnitPhase
      (ggiant (q false) ((s : ZMod (q false)) *
        ((D * q true * (∏ i, p i) : ℕ) : ZMod (q false))⁻¹)) else 0)) *
      primeProductTransform greg (D * q true * q false) (∏ i, p i) s := by
    rw [movingRegularTransform_eq_primeProduct p hp]
    simp only [Fintype.prod_bool]
    rw [show D * (q true * q false) = D * q true * q false by ring]
    congr 1
    simp only [movingRegularTransform, Fintype.prod_bool, bool_tupleCofactor,
      Bool.not_true, Bool.not_false]
    simp only [show ∀ a b c : ℕ, (a * b) * c = (a * c) * b by intros; ring]
  convert hs.trans hfinal using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext i
  cases i with
  | inl b =>
    funext t
    dsimp only
  | inr j => rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal regular template and its full Fourier factor -/

namespace Ostmann
open scoped Classical BigOperators

private theorem prime_pairwise_list_nodup (L : List ℕ) (hp : ∀ p ∈ L, p.Prime)
    (h : L.Pairwise Nat.Coprime) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons p L ih =>
    obtain ⟨hh, ht⟩ := List.pairwise_cons.mp h
    refine List.nodup_cons.mpr ⟨?_, ih (fun q hq => hp q (List.mem_cons_of_mem p hq)) ht⟩
    intro hmem
    have h1 : p = 1 := by simpa only [Nat.coprime_self] using hh p hmem
    exact (hp p List.mem_cons_self).ne_one h1

/-- The support of the actual coefficient forces every prime in the full
regular template to be distinct. -/
theorem movingTemplateCoefficient_nonzero_injective {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (y : MovingRegularSlot n r m → σ) (XL XR : ℕ)
    (hprime : ∀ i, (value (y i)).Prime)
    (h : movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n r m s y XL XR ≠ 0) :
    Function.Injective (value ∘ y) := by
  have hs := (movingFrequencyCoefficient_nonzero_support value outside μ childBound pivotBound V
    F φ G n s _ _ XL XR h).1
  have hr : ((movingTemplateSlotList n r m).map (value ∘ y) ++ outside).Pairwise Nat.Coprime := by
    simpa only [flattenMovingSlots_map, List.map_append, List.map_map, Function.comp_def,
      movingTemplateSlotList, List.tail_cons] using hs.tail.tail
  have hnd : ((movingTemplateSlotList n r m).map (value ∘ y)).Nodup := by
    apply prime_pairwise_list_nodup _ _ (List.pairwise_append.mp hr).1
    intro p hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    exact hprime i
  intro i j hij
  exact List.inj_on_of_nodup_map hnd (mem_movingTemplateSlotList n r m i)
    (mem_movingTemplateSlotList n r m j) hij

attribute [local instance] OAI.Ostmann.templateSum_neZero
/-- The two phase factors and the regular product transform combine into
exactly the full indexed Fourier transform wherever the coefficient contributes. -/
theorem movingTemplateCoefficient_full_transform {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (y : MovingRegularSlot n r m → σ) (q : Bool → ℕ) [∀ b, Fact (q b).Prime]
    (hprime : ∀ i, (value (y i)).Prime)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) :
    let _ : ∀ i, Fact ((value ∘ y) i).Prime := fun i => ⟨hprime i⟩
    movingRegularTransform (Sum.elim q (value ∘ y))
      (fun i => match i with
        | .inl b => fun t => if favorable (q b) then complexUnitPhase (ggiant (q b) t) else 0
        | .inr j => greg (value (y j))) outside.prod s *
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n r m s y (q true) (q false) =
    (giantPairPhase ggiant favorable outside.prod (∏ i, value (y i)) (q true) (q false) s *
      primeProductTransform greg (outside.prod * q true * q false) (∏ i, value (y i)) s) *
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n r m s y (q true) (q false) := by
  let : ∀ i, Fact ((value ∘ y) i).Prime := fun i => ⟨hprime i⟩
  dsimp only
  by_cases h : movingTemplateCoefficient value outside μ childBound pivotBound V F φ G
      n r m s y (q true) (q false) = 0
  · simp only [h, mul_zero]
  · have he := movingRegularTransform_two_giant_phases q (value ∘ y)
      (movingTemplateCoefficient_nonzero_injective value outside μ childBound pivotBound V F
        φ G n r m s y (q true) (q false) hprime h) greg ggiant favorable outside.prod s
    have hh := congrArg (fun z : ℂ => z * movingTemplateCoefficient value outside μ childBound pivotBound V
      F φ G n r m s y (q true) (q false)) he
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
    apply congrArg (fun z : ℂ => z * movingTemplateCoefficient value outside μ childBound pivotBound V
      F φ G n r m s y (q true) (q false))
    unfold movingRegularTransform
    apply Finset.prod_congr rfl
    intro i _
    cases i <;> rfl

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

theorem movingTemplatePrimeAmplitude_regular_congr {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (Pg : Finset ℕ) (ρ : Pg → ℝ)
    (ν : MovingRegularSlot n r m → σ → ℝ)
    (greg hreg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (hregEq : ∀ a, greg (value a) = hreg (value a)) :
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G n r m
      Pg ρ ν greg ggiant favorable =
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G n r m
      Pg ρ ν hreg ggiant favorable := by
  unfold movingTemplatePrimeAmplitude
  have ht (p : Bool → ℕ) (y : MovingRegularSlot n r m → σ) (D : ℕ) (s : ℤ) :
      movingTaggedTransform (Sum.elim p (value ∘ y))
        (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable D s =
      movingTaggedTransform (Sum.elim p (value ∘ y))
        (Sum.elim (fun _ => true) (fun _ => false)) hreg ggiant favorable D s :=
    movingTaggedTransform_regular_congr p (value ∘ y) greg hreg ggiant favorable D s
      (fun i => hregEq _)
  simp_rw [ht]

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedBulkSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonzero bulk averages inherit the original support of one assignment -/

namespace Ostmann
open scoped Classical BigOperators

theorem mixedBulkSymmetrize_ne_zero {B A : Type*} (n m : ℕ)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (s : ℤ) (y : B → A) (x z : ℝ)
    (h : mixedBulkSymmetrize n m slot F s y x z ≠ 0) :
    ∃ e : Equiv.Perm (TreeLeafIndex n × Fin m), F s (selectedBulkSample slot e y) x z ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  simp only [mixedBulkSymmetrize, finiteFamilyAverage, hn, Finset.sum_const_zero, mul_zero]

theorem selectedBulkSample_injective_iff {B J A C : Type*} (slot : J ↪ B)
    (e : Equiv.Perm J) (value : A → C) (y : B → A) :
    Function.Injective (value ∘ selectedBulkSample slot e y) ↔ Function.Injective (value ∘ y) := by
  let E := selectedBulkPerm slot e
  constructor
  · intro h i j hij
    apply E.injective
    apply h
    simpa only [Function.comp_apply, selectedBulkSample, E, Equiv.symm_apply_apply] using hij
  · intro h i j hij
    exact E.symm.injective (h hij)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSymmetrizedMaskedKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The restored multiplier of the actual bulk-averaged coefficient -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingBulkAveragedTemplateCoefficient_nonzero_injective {A : Type} [Fintype A]
    (value : A → ℕ) (hprime : ∀ a, (value a).Prime)
    (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState A → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (x : MovingRegularSlot n r m → A) (XL XR : ℕ)
    (h : movingBulkAveragedTemplateCoefficient value outside μ childBound pivotBound V F φ G
      n r m s x XL XR ≠ 0) : Function.Injective (value ∘ x) := by
  obtain ⟨e, he⟩ := mixedBulkSymmetrize_ne_zero n m (movingTemplateBulk n r m) _ 0 x 0 0 h
  have hi := movingTemplateCoefficient_nonzero_injective value outside μ childBound pivotBound V
    F φ G n r m s (selectedBulkSample (movingTemplateBulk n r m) e x) XL XR
    (fun i => hprime _) he
  exact (selectedBulkSample_injective_iff (movingTemplateBulk n r m) e value x).mp hi

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
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedExternalPartition
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining both complete smooth cells in the mixed external average -/

namespace Ostmann
open scoped Classical BigOperators

private theorem primeInterval_function_add (u v : ℝ) (F H : ℝ → ℂ) :
    complexPrimeInterval 1 0 u v (fun x => F x + H x) =
      complexPrimeInterval 1 0 u v F + complexPrimeInterval 1 0 u v H := by
  unfold complexPrimeInterval
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> ring

theorem mixedExternalAverage_left_add {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v t r w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (huv : u ≤ v) (hvt : v ≤ t) :
    mixedExternalAverage ν N u v r w center F + mixedExternalAverage ν N v t r w center F =
      mixedExternalAverage ν N u t r w center F := by
  unfold mixedExternalAverage
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  rw [← mul_add, ← primeInterval_function_add]
  congr 1
  apply congrArg (complexPrimeInterval 1 0 r w)
  funext z
  exact complexIntegerInterval_add 1 0 u v t center _ huv hvt

theorem mixedExternalAverage_right_add {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r t w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (hrt : r ≤ t) (htw : t ≤ w) :
    mixedExternalAverage ν N u v r t center F + mixedExternalAverage ν N u v t w center F =
      mixedExternalAverage ν N u v r w center F := by
  unfold mixedExternalAverage
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  rw [← mul_add, complexPrimeInterval_add 1 0 r t w _ hrt htw]

theorem mixedExternalAverage_four_cells {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (G H center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) :
    mixedExternalAverage ν N (G - 1) (G + 1) (H - 1) (H + 1) center F =
      (mixedExternalAverage ν N (G - 1) G (H - 1) H center F +
        mixedExternalAverage ν N G (G + 1) (H - 1) H center F) +
      (mixedExternalAverage ν N (G - 1) G H (H + 1) center F +
        mixedExternalAverage ν N G (G + 1) H (H + 1) center F) := by
  rw [mixedExternalAverage_left_add ν N (G - 1) G (G + 1) (H - 1) H center F
      (by linarith) (by linarith),
    mixedExternalAverage_left_add ν N (G - 1) G (G + 1) H (H + 1) center F
      (by linarith) (by linarith),
    mixedExternalAverage_right_add ν N (G - 1) (G + 1) (H - 1) H (H + 1) center F
      (by linarith) (by linarith)]

theorem mixedExternalAverage_full_cell_bound {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (G H center E : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ)
    (h : ∀ i j : Bool, ‖mixedExternalAverage ν N
      (if i then G else G - 1) ((if i then G else G - 1) + 1)
      (if j then H else H - 1) ((if j then H else H - 1) + 1) center F‖ ≤ E) :
    ‖mixedExternalAverage ν N (G - 1) (G + 1) (H - 1) (H + 1) center F‖ ≤ 4 * E := by
  rw [mixedExternalAverage_four_cells]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) (norm_add_le _ _)).trans
  have h00 := h false false
  have h10 := h true false
  have h01 := h false true
  have h11 := h true true
  simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true, sub_add_cancel] at h00 h10 h01 h11
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSymmetrizedFullCell
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full smooth cell for the original symmetrized coefficient -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingTemplateMaskedSymmetrizedEnergy_full_cell_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (ν : MovingRegularSlot n r m → P → ℝ) (active : MovingRegularSlot n r m → Bool)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (Jleft Jright : ℝ) (diagonal : Bool)
    (H K center E : ℝ)
    (h : ∀ i j : Bool, ‖movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G
      n r m ν active greg Jleft Jright diagonal
      (if i then H else H - 1) ((if i then H else H - 1) + 1)
      (if j then K else K - 1) ((if j then K else K - 1) + 1) center‖ ≤ E) :
    ‖movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G
      n r m ν active greg Jleft Jright diagonal (H - 1) (H + 1) (K - 1) (K + 1) center‖ ≤ 4 * E := by
  exact mixedExternalAverage_full_cell_bound ν (V n) H K center E _ h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSelectedInitialFullEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full bulk symmetrization under the actual selected harmonic priors -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_initial_full_energy
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ) (hk : 0 < k) (hn : n + 2 ≤ k)
    (A Wwin Bφ Dφ c K εdiag gain : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hεdiag : 0 < εdiag)
    (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
    ∀ᶠ L : ℝ in atTop, ∀ b : ℕ, spectatorBulkCount k L = b + b →
      let m := b + b
      let Cprior := K + 1
      ∀ (tierB : MovingRegularSlot (n + 2) r₀ m → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (d r : ℕ) (sl sr : Fin d → primes) (fallback : primes)
        (childBound pivotBound V : ℕ → ℕ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ)
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (active : MovingRegularSlot (n + 2) r₀ m → Bool)
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot (n + 2) r₀ m → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (H cb cd : ℝ),
      let slot := movingTemplateBulk (n + 2) r₀ m
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let ν := fun j => primeSubsetPrior primes (Qν j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V (n + 2))).erase 0
      r₀ + 4 * (n + 2) = r + r →
      Monotone V →
      (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
      (V (n + 2) : ℝ) ≤ Real.exp (A * m) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      0 ≤ Δ → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
      1 ≤ H - 1 →
      (∀ i, (n + 2) ≤ tierB i) →
      1 ≤ m → (∀ i, primeCutoff ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      (∀ x, 0 ≤ φ x) → (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) → S ⊆ primes →
      ((global.card + (Fintype.card (MovingRegularSlot (n + 2) r₀ m) + 4 * (n + 2) * 2 ^ (n + 2)) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
      (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j, active (slot j) = true) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ H - 1 →
      (∀ j, j < n + 2 → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
      V (n + 2) ≤ primeLo → V (n + 2) < cutoff → cutoff ≤ primeLo →
      (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qμ j) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
      (∀ z, selectedPageZero P (bulkProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      ‖movingTemplateMaskedSymmetrizedEnergy primes _hprimes outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val p
          (initialMovingDataCutoff Subtype.val b d r cb cd sl sr fallback)
          (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
        φ G (n + 2) r₀ m ν active (normalizedResidueFamily setsReg)
        H H false (H - 1) (H + 1) (H - 1) (H + 1) H‖ ≤
      4 * ((((2 ^ (n + 2) + 1) * (2 ^ (n + 2)) ^ (2 * 2 ^ (n + 2)) : ℕ) : ℝ) *
        Real.exp ((2 ^ (n + 2) : ℝ) * m *
          (-(3 / 4 : ℝ) * Real.log (2 ^ (n + 2) : ℕ) + 5 / 4)) *
        (Real.exp ((2 ^ (n + 2) : ℕ) * Δ +
          (Real.log 12 + 1) * (2 ^ (n + 2) : ℕ) * m + εdiag * m) +
            5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) +
        Real.exp (-gain * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) := by
  obtain ⟨ε, hε, hε1, primeCutoff, hpc, hunit⟩ :=
    P.moving_selected_initial_symmetrized_energy C hM ψ n r₀ k hk hn
      A Wwin Bφ Dφ c K εdiag gain hA hWwin hBφ hDφ hc hK hεdiag hdepth Dlog hDlog hloglip
  refine ⟨ε, hε, hε1, primeCutoff, hpc, ?_⟩
  filter_upwards [hunit] with L hunit
  intro b hsize
  have hunit := hunit b hsize
  dsimp only at hunit ⊢
  intro tierB primes hprimes _ d r sl sr fallback childBound pivotBound V outside p _ Dq sets β
    primeLo cutoff tier X Δ hi φ G active global Qμ Qν setsReg H cb cd
    hlen hV hcard hVn hV0 hΔ hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange hactive houtcover hinjp hHbig hμtier hνtier hNlo hNcut hcutlo hloReal
    hupper hpband hdeleteμ hdeletep hdeleteν hdeletebulk hsetsReg
  apply movingTemplateMaskedSymmetrizedEnergy_full_cell_bound primes hprimes outside
    (fun j => primeSubsetPrior primes (Qμ j)) childBound pivotBound V
    (movingOriginalLeaf Subtype.val p
      (initialMovingDataCutoff Subtype.val b d r cb cd sl sr fallback)
      (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
    φ G (n + 2) r₀ (b + b)
    (fun j => primeSubsetPrior primes (Qν j)) active (normalizedResidueFamily setsReg)
    H H false H H H _
  intro i j
  have hu : H - 1 ≤ (if i then H else H - 1) := by split <;> linarith
  have hr : H - 1 ≤ (if j then H else H - 1) := by split <;> linarith
  have hv : (if i then H else H - 1) ≤ H := by split <;> linarith
  exact hunit tierB primes hprimes d r sl sr fallback childBound pivotBound V outside p Dq sets β
    primeLo cutoff tier X Δ hi φ G active global Qμ Qν setsReg H H false
    (if i then H else H - 1) ((if i then H else H - 1) + 1)
    (if j then H else H - 1) ((if j then H else H - 1) + 1) H cb cd
    hlen hV hcard hVn hV0 hΔ hhi hwindow (hH.trans hu) (hH.trans hr)
    (by linarith) (by linarith) le_rfl le_rfl (by linarith) hB
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange hactive houtcover hinjp (hHbig.trans (by linarith)) (hHbig.trans hr)
    hμtier hνtier hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep hdeleteν hdeletebulk hsetsReg

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplatePrimeStatistic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prime statistic for the actual data-dependent template leaf -/
namespace Ostmann
open scoped Classical BigOperators

/-- The exterior factor agrees with the literal template multiplier wherever
its bulk-symmetrized coefficient is nonzero. -/
theorem movingTemplatePrimeStatistic_energy_integrand
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (H : ℝ) (s : ℤ)
    (y : MovingRegularSlot n r m → P) (x z : ℝ) :
    (‖movingBulkAveragedTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
      n r m s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊‖ ^ 2 : ℂ) *
      ((giantOuterWeight φ H H false ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊) *
        (‖movingExternalRegularFactor Subtype.val outside (movingTemplateSmall n r m)
          (bulkSlotLeaves n m (movingTemplateBulk n r m)) greg s y x z‖ ^ 2 : ℝ)) =
    (‖movingBulkAveragedTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
      n r m s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊‖ ^ 2 : ℂ) *
      movingTemplateExternalMultiplier P hP n r m (fun _ => true) outside greg s φ H H false y x z := by
  by_cases hc : movingBulkAveragedTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
      n r m s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ = 0
  · simp only [hc, norm_zero, zero_pow (by norm_num : 2 ≠ 0), Complex.ofReal_zero, zero_mul]
  have hi := movingBulkAveragedTemplateCoefficient_nonzero_injective Subtype.val
    (fun q : P => hP _ q.property) outside μ childBound pivotBound V F φ G n r m s y
    ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ hc
  let q := fun i => (y i : ℕ)
  let _ : ∀ i, Fact (q i).Prime := fun i => ⟨hP _ (y i).property⟩
  have hprod := movingTemplate_product Subtype.val n r m y
  unfold movingTemplateExternalMultiplier
  dsimp only
  rw [naturalRegularMultiplier_eq_transform_norm]
  simp only [ite_true, if_true]
  change _ = _ * (giantOuterWeight _ _ _ _ _ _ *
    (‖movingRegularTransform q (fun i => greg (q i))
      (outside.prod * ⌊Real.exp x⌋₊ * ⌊Real.exp z⌋₊) s‖ ^ 2 : ℝ))
  rw [movingRegularTransform_eq_primeProduct q hi]
  unfold movingExternalRegularFactor
  rw [hprod]

theorem movingTemplatePrimeStatistic_cauchy
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x) (G : ℕ → ℝ) (n r m : ℕ)
    (ν : MovingRegularSlot n r m → P → ℝ)
    (hν : ∀ i q, 0 ≤ ν i q)
    (hidentical : ∀ j k, ν (movingTemplateBulk n r m j) = ν (movingTemplateBulk n r m k))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (H u v a b center : ℝ) :
    ‖movingTemplatePrimeStatistic P outside μ childBound pivotBound V F φ G n r m ν
      greg ggiant favorable H u v a b‖ ^ 2 ≤
    Real.exp (center - u) ^ 2 *
      (mixedExternalAverage ν (V n) u v a b center (fun _ _ x z =>
        giantOuterWeight φ H H false ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)).re *
      (movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G
        n r m ν (fun _ => true) greg H H false u v a b center).re := by
  let C := fun s y x z => movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
    n r m s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
  let R := movingExternalRegularFactor (Subtype.val : P → ℕ) outside (movingTemplateSmall n r m)
    (bulkSlotLeaves n m (movingTemplateBulk n r m)) greg
  let Q := movingGiantPhase (Subtype.val : P → ℕ) outside (movingTemplateSmall n r m)
    (bulkSlotLeaves n m (movingTemplateBulk n r m)) ggiant favorable
  let W := fun x z => giantOuterWeight φ H H false ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
  have hsmall : ∀ i ∈ flattenMovingSlots n (movingTemplateSmall n r m),
      i ∉ Set.range (movingTemplateBulk n r m) := movingTemplateSmall_not_bulk n r m
  have hR (e s y x z) : R s (selectedBulkSample (movingTemplateBulk n r m) e y) x z = R s y x z := by
    dsimp only [R, movingExternalRegularFactor]
    rw [MovingSlotReversal.naturalProduct_selected_bulk Subtype.val n m
      (movingTemplateSmall n r m) (movingTemplateBulk n r m) e y hsmall]
  have hQ (e s y x z) : Q s (selectedBulkSample (movingTemplateBulk n r m) e y) x z = Q s y x z :=
    movingGiantPhase_selectedBulkSample Subtype.val outside n m (movingTemplateSmall n r m)
      (movingTemplateBulk n r m) e y hsmall ggiant favorable s x z
  have hQnorm (s y x z) : ‖Q s y x z‖ ≤ 1 :=
    movingGiantPhase_norm_le Subtype.val outside (movingTemplateSmall n r m)
      (bulkSlotLeaves n m (movingTemplateBulk n r m)) ggiant favorable s y x z
  have hW (x z : ℝ) : 0 ≤ (W x z).re ∧ ((W x z).re : ℂ) = W x z := by
    obtain ⟨c, hc, he⟩ := giantOuterWeight_positive φ hφ H H false ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
    change W x z = (c : ℂ) at he
    rw [he]
    exact ⟨hc, rfl⟩
  have hc := primeExternalAverage_bounded_statistic_cauchy n m (movingTemplateBulk n r m)
    ν hν hidentical (V n) u v a b center C R Q hR hQ hQnorm
    (fun x z => (W x z).re) (fun x z => (hW x z).1)
  simp only [(hW _ _).2] at hc
  have he : (mixedExternalAverage ν (V n) u v a b center (fun s y x z =>
      (‖mixedBulkSymmetrize n m (movingTemplateBulk n r m) C s y x z‖ ^ 2 : ℂ) *
        (W x z * (‖R s y x z‖ ^ 2 : ℝ)))) =
      movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G
        n r m ν (fun _ => true) greg H H false u v a b center := by
    unfold movingTemplateMaskedSymmetrizedEnergy
    congr 1
    funext s y x z
    exact movingTemplatePrimeStatistic_energy_integrand P hP outside μ childBound pivotBound V F
      φ G n r m greg H s y x z
  rw [he] at hc
  exact hc

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplatePrimeStatisticBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The final full-cell statistic is controlled by its literal masked energy -/
namespace Ostmann
open scoped Classical BigOperators

theorem movingTemplatePrimeStatistic_full_cell_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hφnorm : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (G : ℕ → ℝ) (n r m : ℕ)
    (ν : MovingRegularSlot n r m → P → ℝ)
    (hν : ∀ i q, 0 ≤ ν i q) (hmass : ∀ i, ∑ q, ν i q = 1)
    (hidentical : ∀ j k, ν (movingTemplateBulk n r m j) = ν (movingTemplateBulk n r m k))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (H : ℝ) :
    ‖movingTemplatePrimeStatistic P outside μ childBound pivotBound V F φ G n r m ν
      greg ggiant favorable H (H - 1) (H + 1) (H - 1) (H + 1)‖ ^ 2 ≤
    diagonalOuterMajorant Bφ Dφ false * (2 * V n + 1 : ℕ) * Real.exp 5 *
      ‖movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G
        n r m ν (fun _ => true) greg H H false (H - 1) (H + 1) (H - 1) (H + 1) H‖ := by
  let W := fun (_ : ℤ) (_ : MovingRegularSlot n r m → P) (x z : ℝ) =>
    giantOuterWeight φ H H false ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
  have hC := (diagonalOuterMajorant_pos Bφ Dφ false).le
  have hW (s y x z) : 0 ≤ (W s y x z).re := by
    obtain ⟨a, ha, he⟩ := giantOuterWeight_positive φ hφ H H false ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
    change W s y x z = (a : ℂ) at he
    rw [he]
    exact ha
  have hWu (s y x z) : (W s y x z).re ≤ diagonalOuterMajorant Bφ Dφ false := by
    apply (Complex.re_le_norm _).trans
    exact (giantOuterWeight_norm φ H H Bφ Dφ hBφ hDφ hφnorm hlip hout false _ _).trans
      (by unfold diagonalOuterMajorant; linarith)
  have hm0 := mixedExternalAverage_re_nonneg ν hν (V n)
    (H - 1) (H + 1) (H - 1) (H + 1) H W hW
  have hmb := mixedExternalAverage_mass_bound ν hν hmass (V n)
    (H - 1) (H + 1) (H - 1) (H + 1) H (diagonalOuterMajorant Bφ Dφ false) hC W hWu
  have hmupper : (mixedExternalAverage ν (V n)
      (H - 1) (H + 1) (H - 1) (H + 1) H W).re ≤
      diagonalOuterMajorant Bφ Dφ false * (2 * V n + 1 : ℕ) * Real.exp 3 := by
    simpa only [show H + 1 - (H - 1) + (H + 1 - H) = 3 by ring] using hmb
  have hc := movingTemplatePrimeStatistic_cauchy P hP outside μ childBound pivotBound V F
    φ hφ G n r m ν hν hidentical greg ggiant favorable H
    (H - 1) (H + 1) (H - 1) (H + 1) H
  have he := Complex.re_le_norm (movingTemplateMaskedSymmetrizedEnergy P hP outside μ
    childBound pivotBound V F φ G n r m ν (fun _ => true) greg H H false
    (H - 1) (H + 1) (H - 1) (H + 1) H)
  have hstep := mul_le_mul_of_nonneg_left he (mul_nonneg (sq_nonneg (Real.exp (H - (H - 1)))) hm0)
  have hnext := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmupper (sq_nonneg (Real.exp (H - (H - 1)))))
    (norm_nonneg (movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F
      φ G n r m ν (fun _ => true) greg H H false (H - 1) (H + 1) (H - 1) (H + 1) H))
  apply hc.trans ((hstep.trans hnext).trans_eq ?_)
  rw [show H - (H - 1) = 1 by ring]
  have hExp : Real.exp 1 ^ 2 * Real.exp 3 = Real.exp 5 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    norm_num
  calc
    _ = (diagonalOuterMajorant Bφ Dφ false * (2 * V n + 1 : ℕ)) *
      (Real.exp 1 ^ 2 * Real.exp 3) *
      ‖movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G
        n r m ν (fun _ => true) greg H H false (H - 1) (H + 1) (H - 1) (H + 1) H‖ := by ring
    _ = _ := by rw [hExp]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateAmplitudeStatistic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact giant-prior normalization for the data-dependent template statistic -/
namespace Ostmann
open scoped Classical BigOperators

local instance templateStatisticSum_neZero {J I : Type*} (q : J → ℕ) (p : I → ℕ)
    [∀ j, NeZero (q j)] [∀ i, NeZero (p i)] (i : J ⊕ I) :
    NeZero (Sum.elim q p i) := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

theorem movingTemplatePrimeAmplitude_smooth_average
    (P : Finset ℕ) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (ν : MovingRegularSlot n r m → P → ℝ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (H : ℝ) :
    movingTemplatePrimeAmplitude Subtype.val outside μ childBound pivotBound V F φ G n r m
      (smoothGiantPrimeRange H) (smoothGiantPrior (smoothGiantPrimeRange H) φ H) ν
      greg ggiant favorable =
    smoothGiantExternalAverage ν (V n) φ H H (fun s y XL XR =>
      movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G n r m s y XL XR *
        movingTaggedTransform (Sum.elim (fun b : Bool => if b then XL else XR) (Subtype.val ∘ y))
          (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s) := by
  unfold movingTemplatePrimeAmplitude smoothGiantExternalAverage
  simp only [finite_univ_canonical, Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext XL
    rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext s
    arg 2
    ext XL
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext s
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr (by ext; simp only [Finset.mem_univ])
  intro y _
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro XR _
  apply Finset.sum_congr rfl
  intro XL _
  ring

theorem movingTemplatePrimeAmplitude_statistic_eq
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0) (G : ℕ → ℝ) (n r m : ℕ)
    (ν : MovingRegularSlot n r m → P → ℝ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (H : ℝ) :
    movingTemplatePrimeAmplitude Subtype.val outside μ childBound pivotBound V F φ G n r m
      (smoothGiantPrimeRange H) (smoothGiantPrior (smoothGiantPrimeRange H) φ H) ν
      greg ggiant favorable =
    (Real.exp (2 * smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H) : ℂ) *
      movingTemplatePrimeStatistic P outside μ childBound pivotBound V F φ G n r m ν
        greg ggiant favorable H (H - 1) (H + 1) (H - 1) (H + 1) := by
  rw [movingTemplatePrimeAmplitude_smooth_average, smoothGiantExternalAverage_eq _ _ _ _ _ hout]
  rw [show smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H +
    smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H =
    2 * smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H by ring]
  apply congrArg (fun z : ℂ =>
    (Real.exp (2 * smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H) : ℂ) * z)
  unfold movingTemplatePrimeStatistic
  refine primeExternalAverage_congr_primes ν (V n) (H - 1) (H + 1) (H - 1) (H + 1) _ _ ?_
  intro s y XL XR hXL hXR
  let q := fun b : Bool => if b then XL else XR
  let _ : ∀ b, Fact (q b).Prime := fun b => ⟨by cases b <;> assumption⟩
  let _ : ∀ i, Fact ((Subtype.val ∘ y) i).Prime := fun i => ⟨hP _ (y i).property⟩
  have ht : movingTaggedTransform (Sum.elim q (Subtype.val ∘ y))
      (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s =
      movingRegularTransform (Sum.elim q (Subtype.val ∘ y))
        (fun i => match i with
          | .inl b => fun t => if favorable (q b) then complexUnitPhase (ggiant (q b) t) else 0
          | .inr j => greg (y j)) outside.prod s := by
    unfold movingTaggedTransform movingRegularTransform
    apply Finset.prod_congr rfl
    intro i _
    cases i <;> rfl
  have hf := movingTemplateCoefficient_full_transform Subtype.val outside μ childBound pivotBound V F
    φ G n r m s y q (fun i => hP _ (y i).property) greg ggiant favorable
  have hcore : movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F
      φ G n r m s y XL XR * movingTaggedTransform (Sum.elim q (Subtype.val ∘ y))
        (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s =
      (giantPairPhase ggiant favorable outside.prod (∏ i, (y i : ℕ)) XL XR s *
        primeProductTransform greg (outside.prod * XL * XR) (∏ i, (y i : ℕ)) s) *
        movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G n r m s y XL XR := by
    rw [mul_comm, ht]
    exact hf
  have hp : (0 : ℝ) < XL := Nat.cast_pos.mpr hXL.pos
  have hr : (0 : ℝ) < XR := Nat.cast_pos.mpr hXR.pos
  simp only [Real.exp_log hp, Real.exp_log hr, Nat.floor_natCast]
  rw [show (fun b : Bool => if b then XL else XR) = q from rfl, hcore]
  simp only [movingGiantPhase, movingExternalRegularFactor, movingTemplate_product,
    Real.exp_log hp, Real.exp_log hr, Nat.floor_natCast, giantOuterWeight,
    Bool.false_eq_true, ite_false, if_false, mul_one, positiveLogCutoff, hp, hr, ite_true, if_true]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSelectedInitialFinalStatistic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual final prime statistic under the selected harmonic laws -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_initial_final_statistic
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ) (hk : 0 < k) (hn : n + 2 ≤ k)
    (A Wwin Bφ Dφ c K εdiag gain : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hεdiag : 0 < εdiag)
    (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
    ∀ᶠ L : ℝ in atTop, ∀ b : ℕ, spectatorBulkCount k L = b + b →
      let m := b + b
      let Cprior := K + 1
      ∀ (tierB : MovingRegularSlot (n + 2) r₀ m → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (d r : ℕ) (sl sr : Fin d → primes) (fallback : primes)
        (childBound pivotBound V : ℕ → ℕ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ)
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot (n + 2) r₀ m → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (H cb cd : ℝ)
        (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool),
      let slot := movingTemplateBulk (n + 2) r₀ m
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let ν := fun j => primeSubsetPrior primes (Qν j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V (n + 2))).erase 0
      r₀ + 4 * (n + 2) = r + r →
      Monotone V →
      (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
      (V (n + 2) : ℝ) ≤ Real.exp (A * m) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      0 ≤ Δ → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
      1 ≤ H - 1 →
      (∀ i, (n + 2) ≤ tierB i) →
      1 ≤ m → (∀ i, primeCutoff ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      (∀ x, 0 ≤ φ x) → (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) → S ⊆ primes →
      ((global.card + (Fintype.card (MovingRegularSlot (n + 2) r₀ m) + 4 * (n + 2) * 2 ^ (n + 2)) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
      (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ H - 1 →
      (∀ j, j < n + 2 → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
      V (n + 2) ≤ primeLo → V (n + 2) < cutoff → cutoff ≤ primeLo →
      (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qμ j) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
      (∀ z, selectedPageZero P (bulkProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      ‖movingTemplatePrimeStatistic primes outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val p
          (initialMovingDataCutoff Subtype.val b d r cb cd sl sr fallback)
          (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
        φ G (n + 2) r₀ m ν (normalizedResidueFamily setsReg) ggiant favorable
        H (H - 1) (H + 1) (H - 1) (H + 1)‖ ^ 2 ≤
      diagonalOuterMajorant Bφ Dφ false * (2 * V (n + 2) + 1 : ℕ) * Real.exp 5 *
      (4 * ((((2 ^ (n + 2) + 1) * (2 ^ (n + 2)) ^ (2 * 2 ^ (n + 2)) : ℕ) : ℝ) *
        Real.exp ((2 ^ (n + 2) : ℝ) * m *
          (-(3 / 4 : ℝ) * Real.log (2 ^ (n + 2) : ℕ) + 5 / 4)) *
        (Real.exp ((2 ^ (n + 2) : ℕ) * Δ +
          (Real.log 12 + 1) * (2 ^ (n + 2) : ℕ) * m + εdiag * m) +
            5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) +
        Real.exp (-gain * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)))) := by
  obtain ⟨ε, hε, hε1, primeCutoff, hpc, henergy⟩ :=
    P.moving_selected_initial_full_energy C hM ψ n r₀ k hk hn
      A Wwin Bφ Dφ c K εdiag gain hA hWwin hBφ hDφ hc hK hεdiag hdepth Dlog hDlog hloglip
  refine ⟨ε, hε, hε1, primeCutoff, hpc, ?_⟩
  filter_upwards [henergy] with L henergy
  intro b hsize
  have he := henergy b hsize
  dsimp only at he ⊢
  intro tierB primes hprimes _ d r sl sr fallback childBound pivotBound V outside p _ Dq sets β
    primeLo cutoff tier X Δ hi φ G global Qμ Qν setsReg H cb cd ggiant favorable
    hlen hV hcard hVn hV0 hΔ hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν
    hμP hνP hμmass hνmass hμrange hνrange houtcover hinjp hHbig hμtier hνtier
    hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep hdeleteν hdeletebulk hsetsReg
  have hbound := he tierB primes hprimes d r sl sr fallback childBound pivotBound V outside p Dq sets β
    primeLo cutoff tier X Δ hi φ G (fun _ => true) global Qμ Qν setsReg H cb cd
    hlen hV hcard hVn hV0 hΔ hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν
    hμP hνP hμmass hνmass hμrange hνrange (fun _ => rfl) houtcover hinjp hHbig hμtier hνtier
    hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep hdeleteν hdeletebulk hsetsReg
  have hmass (j) : ∑ q : primes, primeSubsetPrior primes (Qν j) q = 1 := by
    apply primeSubsetPrior_mass primes (Qν j) (hνP j)
    exact (lt_of_lt_of_le (div_pos hc (Real.exp_pos _)) (hνmass j)).ne'
  have hidentical (i j) : primeSubsetPrior primes (Qν (movingTemplateBulk (n + 2) r₀ (b + b) i)) =
      primeSubsetPrior primes (Qν (movingTemplateBulk (n + 2) r₀ (b + b) j)) := by
    rw [hν i, hν j]
  apply (movingTemplatePrimeStatistic_full_cell_bound primes hprimes outside
    (fun j => primeSubsetPrior primes (Qμ j)) childBound pivotBound V
    (movingOriginalLeaf Subtype.val p
      (initialMovingDataCutoff Subtype.val b d r cb cd sl sr fallback)
      (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
    φ hφpos Bφ Dφ hBφ hDφ hφ hlip hφout G (n + 2) r₀ (b + b)
    (fun j => primeSubsetPrior primes (Qν j)) (fun j q => primeSubsetPrior_nonneg _ _ q)
    hmass hidentical (normalizedResidueFamily setsReg) ggiant favorable H).trans
  exact mul_le_mul_of_nonneg_left hbound
    (mul_nonneg (mul_nonneg (diagonalOuterMajorant_pos Bφ Dφ false).le
      (Nat.cast_nonneg _)) (Real.exp_nonneg _))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSelectedInitialContradiction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Contradiction at the last depth for the actual initial half-cutoff leaf -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_initial_final_contradiction_varying_window
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (Bs BD Bz B Bφ Dφ c K : ℝ)
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) (hc : 0 < c) (hK : 0 ≤ K)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|) :
    ∀ᶠ k : ℕ in atTop, ∀ Wwin : ℝ, 0 ≤ Wwin → 8 * (K + 1) ≤ (k : ℝ) ^ 3 →
    let A := movingFrequencyRate Bs BD Bz ((k : ℝ) ^ 4) k
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
    ∀ᶠ L : ℝ in atTop, ∀ b : ℕ, spectatorBulkCount k L = b + b →
      let m := b + b
      let Cprior := K + 1
      ∀ (tierB : MovingRegularSlot k 6 m → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (d r : ℕ) (sl sr : Fin d → primes) (fallback : primes)
        (childBound pivotBound V : ℕ → ℕ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ)
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot k 6 m → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (H cb cd : ℝ)
        (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool),
      let slot := movingTemplateBulk k 6 m
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let ν := fun j => primeSubsetPrior primes (Qν j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V k)).erase 0
      6 + 4 * k = r + r →
      Monotone V →
      (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
      (V k : ℝ) ≤ Real.exp (A * m) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      0 ≤ Δ → Δ ≤ spectatorBaseGap Bs ((k : ℝ) ^ 4) m → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
      1 ≤ H - 1 →
      (∀ i, k ≤ tierB i) →
      1 ≤ m → (∀ i, primeCutoff ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      (∀ x, 0 ≤ φ x) → (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) → S ⊆ primes →
      ((global.card + (Fintype.card (MovingRegularSlot k 6 m) + 4 * k * 2 ^ k) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
      (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ H - 1 →
      (∀ j, j < k → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
      V k ≤ primeLo → V k < cutoff → cutoff ≤ primeLo →
      (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qμ j) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
      (∀ z, selectedPageZero P (bulkProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H ≤ L →
      Real.exp (-B * (2 : ℝ) ^ k * m) ≤
        ‖movingTemplatePrimeAmplitude Subtype.val outside μ childBound pivotBound V
          (movingOriginalLeaf Subtype.val p
            (initialMovingDataCutoff Subtype.val b d r cb cd sl sr fallback)
            (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
          φ G k 6 m (smoothGiantPrimeRange H) (smoothGiantPrior (smoothGiantPrimeRange H) φ H)
          ν (normalizedResidueFamily setsReg) ggiant favorable‖ → False := by
  filter_upwards [eventually_moving_normalized_numeric_contradiction Bs BD Bz B
    (diagonalOuterMajorant Bφ Dφ false) (diagonalOuterMajorant_pos Bφ Dφ false).le,
    eventually_ge_atTop (2 : ℕ)] with k hnumeric hk
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  intro Wwin hWwin hdepth A
  have hk0 : 0 < (n + 2) := by omega
  have hA : 0 ≤ A := by
    dsimp only [A, movingFrequencyRate]
    have hlog : 0 ≤ Real.log (((n + 2 : ℕ) : ℝ) ^ 4) := Real.log_nonneg
      (one_le_pow₀ (show (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) by exact_mod_cast hk0) )
    have hlogr : 0 ≤ Real.log ((2 : ℝ) ^ (n + 2)) := Real.log_nonneg (one_le_pow₀ (by norm_num))
    exact mul_nonneg (by positivity) (by nlinarith [mul_nonneg hBz hlog])
  let gain := A + (2 * (B + 1) + 1) * (2 : ℝ) ^ (n + 2) + 1
  obtain ⟨ε, hε, hε1, primeCutoff, hpc, he⟩ :=
    P.moving_selected_initial_final_statistic C hM ψ n 6 (n + 2) hk0 (by omega)
      A Wwin Bφ Dφ c K 1 gain hA hWwin hBφ hDφ hc hK (by norm_num) hdepth Dlog hDlog hloglip
  refine ⟨ε, hε, hε1, primeCutoff, hpc, ?_⟩
  filter_upwards [he, hnumeric] with L he hnumeric
  intro b hsize
  have he := he b hsize
  dsimp only at he ⊢
  intro tierB primes hprimes _ d r sl sr fallback childBound pivotBound V outside p _ Dq sets β
    primeLo cutoff tier X Δ hi φ G global Qμ Qν setsReg H cb cd ggiant favorable
    hlen hV hcard hVn hV0 hΔ hΔbound hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν
    hμP hνP hμmass hνmass hμrange hνrange houtcover hinjp hHbig hμtier hνtier
    hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep hdeleteν hdeletebulk hsetsReg
    hcg hlower
  have hstat := he tierB primes hprimes d r sl sr fallback childBound pivotBound V outside p Dq sets β
    primeLo cutoff tier X Δ hi φ G global Qμ Qν setsReg H cb cd ggiant favorable
    hlen hV hcard hVn hV0 hΔ hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν
    hμP hνP hμmass hνmass hμrange hνrange houtcover hinjp hHbig hμtier hνtier
    hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep hdeleteν hdeletebulk hsetsReg
  have hid := movingTemplatePrimeAmplitude_statistic_eq primes hprimes outside
    (fun j => primeSubsetPrior primes (Qμ j)) childBound pivotBound V
    (movingOriginalLeaf Subtype.val p
      (initialMovingDataCutoff Subtype.val b d r cb cd sl sr fallback)
      (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
    φ hφout G (n + 2) 6 (b + b) (fun j => primeSubsetPrior primes (Qν j))
    (normalizedResidueFamily setsReg) ggiant favorable H
  have hmcast : (spectatorBulkCount (n + 2) L : ℝ) = (b + b : ℕ) := by exact_mod_cast hsize
  have hf := hnumeric (V (n + 2)) (by simpa only [hmcast] using hVn) hA Δ
    (smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H)
    (by simpa only [hmcast, spectatorBaseGap] using hΔbound) hcg _ _ hid
    (by simpa only [hmcast] using hlower)
  apply hf
  simpa only [hmcast, gain, A, Nat.cast_pow, Nat.cast_ofNat, one_mul, mul_assoc, add_assoc] using hstat

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

theorem forall₂_headD_drop {R : ℕ → ℝ → Prop} {cs : List ℕ} {ws : List ℝ}
    (h : List.Forall₂ R cs ws) (n : ℕ) (hn : n < cs.length) :
    R ((cs.drop n).headD 0) ((ws.drop n).headD 0) := by
  induction h generalizing n with
  | nil => simp at hn
  | cons h hrest ih =>
    cases n with
    | zero => exact h
    | succ n => simpa only [List.drop_succ_cons] using ih n (by simpa using hn)

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledFinalTemplate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The last stage retains exactly the six original top-cell copies -/
namespace Ostmann
open scoped Classical BigOperators

theorem scheduled_final_length (top : ℕ) (cs : List ℕ) (k : ℕ) (hlen : cs.length = k) :
    6 + 4 * k = (initialSmallCellList top cs).length + (initialSmallCellList top cs).length := by
  simp only [initialSmallCellList_length, hlen]
  omega

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedScheduledFinalContradiction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The last-depth contradiction for the actual selected finite schedule -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.selected_scheduled_final_contradiction_oai
    (P0 : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (Bs BD Bz B Dφ : ℝ)
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) (hDφ : 0 ≤ Dφ)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dφ * |x - y|) :
    ∀ᶠ k : ℕ in atTop, ∀ Wwin : ℝ, 0 ≤ Wwin → 120 ≤ (k : ℝ) ^ 3 →
    let Afreq := movingFrequencyRate (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4) k
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ p₀ : ℕ, 3 ≤ p₀ ∧
    ∀ᶠ L : ℝ in atTop, ∀ (Aset Bset : Set ℕ), Aset.Infinite → Bset.Infinite →
    ∀ N : ℕ, (∀ p, p.Prime → Disjoint (tailResidues Aset N p) (negTailResidues Bset N p)) →
    ∀ (b endpoint top : ℕ) (a Y G J cb cd Δ upper X : ℝ) (cs : List ℕ),
      spectatorBulkCount k L = b + b → cs.length = k →
      0 ≤ cb →
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
      smoothGiantLogNormalizer (smoothGiantPrimeRange G) logCellProfile G ≤ L →
      ∀ (q : Fin (b + b) → ℕ) [∀ i, Fact (q i).Prime],
      FrozenInitialSpectatorData Aset N q L ε p₀ D →
      ∀ (sl sr : Fin b → Q) (fallback : Q)
        (Dq : ∀ i, (ZMod (q i))ˣ) (childBound pivotBound V : ℕ → ℕ),
      Monotone V →
      (V k : ℝ) ≤ Real.exp (Afreq * (b + b : ℕ)) →
      ((transferFrequencyRange (V k)).card : ℝ) ≤ Real.exp (Afreq * (b + b : ℕ)) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * (b + b : ℕ))) →
      0 ≤ Δ → Δ ≤ spectatorBaseGap (Bs + 1) ((k : ℝ) ^ 4) (b + b : ℕ) →
      Real.exp Δ ≤ upper → upper - Real.exp Δ ≤ Real.exp (Wwin * (b + b : ℕ)) →
      ∀ favorable : ℕ → Bool,
      let F := movingOriginalLeaf Subtype.val q
        (initialMovingDataCutoff Subtype.val b b (initialSmallCellList top cs).length cb cd sl sr fallback)
        (fun i => normalizedResidueTransform (tailDensityMask Aset N (q i))) Dq Finset.univ
        ψ X (Real.exp Δ) upper
      Real.exp (-B * (2 : ℝ) ^ k * (b + b : ℕ)) ≤
        ‖scheduledCellAmplitude Subtype.val (List.ofFn q)
          (completedCompensationPrior Aset Bset N Y endpoint D Q top cs)
          childBound pivotBound V F logCellProfile (fun _ => G)
          (smoothGiantPrimeRange G) (smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G)
          (fun c => primeSubsetPrior Q (selectedTailCellPrimes Aset Bset N Y endpoint D c))
          (primeSubsetPrior Q Qb) top cs k (b + b)
          (normalizedResidueFamily (tailDensityMask Aset N))
          (normalizedResidueFamily (tailDensityMask Aset N)) favorable‖ → False := by
  have hf := P0.moving_selected_initial_final_contradiction_varying_window C hM ψ
    (Bs + 1) (BD + 2) Bz B 1 Dφ 1 2 (by linarith) (by linarith) hBz
    (by norm_num) hDφ (by norm_num) (by norm_num) Dφ hDφ hloglip
  filter_upwards [hf, eventually_ge_atTop (2 : ℕ)] with k hf hk
  intro Wwin hWwin hdepth Afreq
  obtain ⟨ε, hε, hε1, p₀, hp₀, he⟩ := hf Wwin hWwin (by linarith)
  refine ⟨ε, hε, hε1, p₀, hp₀, ?_⟩
  filter_upwards [he, eventual_scheduled_comparison_cutoffs k k p₀ (fun _ => Afreq),
    eventual_scheduled_comparison_count k, eventual_selected_bulk_mass hM,
    (spectatorBulkCount_tendsto k (by omega)).eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with L he hcut hcount hmass hm hL
  intro Aset Bset hA hB N hN b endpoint top a Y G J cb cd Δ upper X cs hsize hlen hcb
    hJ hJerr hJgap Q D Qb htop hcs hlower hG hcg q inst hq sl sr fallback Dq
    childBound pivotBound V hV hVbound hVcard hV0 hΔ hΔbound hupper hwindow favorable F hamp
  have hm' : 1 ≤ b + b := by
    exact_mod_cast (show (1 : ℝ) ≤ (b + b : ℕ) by simpa only [hsize] using hm)
  have hQprime := initialRegularPrimeRange_prime L
  let : Nonempty Q := ⟨⟨(selected_regular_alphabet_nonempty htop).choose,
    (selected_regular_alphabet_nonempty htop).choose_spec⟩⟩
  obtain ⟨hbulk, hbulklower⟩ := selected_bulk_prime_range L (by linarith) D
  have hDcard : D.card ≤ 2 := scheduledPageDeletions_card P0 L _
  obtain ⟨hμdata, hμlower, hνdata, hνlower⟩ := selected_schedule_prime_data htop hcs
    (by linarith) hlower hbulk hbulklower (hmass D hDcard)
  obtain ⟨tier, hμtier, hνtier⟩ := selected_cells_prime_tiers k (by omega) (by linarith)
    hBD hBz hcb hJ hJerr hJgap htop hcs
  have hdrop : cs.drop k = [] := by rw [← hlen, List.drop_length]
  have ht := hνtier k (b + b) k (by omega)
  rw [hdrop] at ht
  obtain ⟨tierB, hTierBound, hBtier⟩ := ht
  have hνd := hνdata k (b + b) k
  have hνl := hνlower k (b + b) k
  rw [hdrop] at hνd hνl
  let Qν := scheduledRegularPrimeSets (selectedTailCellPrimes Aset Bset N Y endpoint D)
    Qb top [] k (b + b)
  let setsReg := primeMaskExtension Q (tailDensityMask Aset N)
  have hsmallsets : ∀ p, p.Prime → (setsReg p).Nonempty ∧ (setsReg p).card < p :=
    tailPrimeMaskExtension_data hA hB N Q hQprime (fun p hp => hN p (hQprime p hp))
  have hcomplex : ((D.card + (Fintype.card (MovingRegularSlot k 6 (b + b)) +
      4 * k * 2 ^ k)) + (List.ofFn q).length : ℕ) ≤
      scheduledComparisonCount k (spectatorBulkCount k L) := by
    rw [hsize]
    exact scheduled_comparison_count k k 6 _ le_rfl (by omega) D (List.ofFn q) hDcard (by simp)
  have hcomplexReal : ((D.card + (Fintype.card (MovingRegularSlot k 6 (b + b)) +
      4 * k * 2 ^ k)) + (List.ofFn q).length : ℕ) ≤ Real.exp ((2 + 1) * L) := by
    have hh : (((D.card + (Fintype.card (MovingRegularSlot k 6 (b + b)) +
        4 * k * 2 ^ k)) + (List.ofFn q).length : ℕ) : ℝ) ≤
        scheduledComparisonCount k (spectatorBulkCount k L) := by exact_mod_cast hcomplex
    exact hh.trans (by norm_num; exact hcount)
  have hcuts := hcut.2.2.2.2 k le_rfl (V k) (by simpa only [hsize] using hVbound)
  have hprimeBand (i) := hcut.2.2.2.1 (q i) (hq.lower i) (hq.upper i)
  have hbulkD : Disjoint Qb D :=
    Finset.disjoint_left.mpr (fun _ hp hd => (Finset.mem_sdiff.mp hp).2 hd)
  have hpage := selected_schedule_avoids_giant_page P0 Aset Bset N endpoint Y L
    (scheduledComparisonCutoff L) top cs Qb hbulkD
  have hpageν (z : PrimitiveRealZero)
      (hz : selectedPageZero P0 (giantProgressionCutoff L) = some z)
      (p : ℕ) (hp : deletedConductorPrime z.modulus (scheduledComparisonCutoff L) = some p)
      (i : MovingRegularSlot k 6 (b + b)) : p ∉ Qν i := by
    have hh := (hpage z hz p hp).2 k (b + b) k
    rw [hdrop] at hh
    exact hh i
  have hShell : primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
      (Real.exp ((6 / 1000 : ℝ) * L)) ⊆ Q := by
    simpa only [Finset.sdiff_empty] using initial_broad_cell_subset L (4 / 1000)
      (6 / 1000) (by linarith) (by norm_num) ∅
  have hfreqCard : (((transferFrequencyRange (V k)).erase 0).card : ℝ) ≤
      Real.exp (Afreq * (b + b : ℕ)) := by
    have he : (((transferFrequencyRange (V k)).erase 0).card : ℝ) ≤
        (transferFrequencyRange (V k)).card := by exact_mod_cast Finset.card_erase_le
    exact he.trans hVcard
  have hd := he b hsize
  dsimp only at hd
  apply hd tierB Q hQprime b (initialSmallCellList top cs).length sl sr fallback
    childBound pivotBound V (List.ofFn q) q Dq (fun i => tailDensityMask Aset N (q i))
    (fun _ => ε / 2) (scheduledComparisonPrimeLo L) (scheduledComparisonCutoff L)
    (fun p => tier p) X Δ upper logCellProfile (fun _ => G) D
    (completedCompensationSets Aset Bset N Y endpoint D top cs) Qν setsReg G cb cd
    (normalizedResidueFamily (tailDensityMask Aset N)) favorable
    (scheduled_final_length top cs k hlen) hV hfreqCard hVbound hV0 hΔ hΔbound hupper hwindow
    (by have he := Real.one_le_exp (show 0 ≤ (49 / 1000 : ℝ) * L by positivity); linarith)
    hTierBound hm' hq.ge_cutoff hq.nonempty hq.proper
    (hq.comparison_upper (by linarith)) hq.balanced_lower hq.balanced_upper (fun _ => by linarith)
    hq.character_bound logCellProfile_nonneg
    (fun x => (abs_of_nonneg (logCellProfile_nonneg x)).trans_le (logCellProfile_le_one x))
    hloglip logCellProfile_zero_outside hShell hcomplexReal
    (by intro p hp; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp; exact (inferInstance : Fact (q i).Prime).out)
    (fun _ => rfl) (fun j => (hμdata j).1) (fun i => (hνd i).1)
    (fun j => (hμdata j).2) (fun i => (hνd i).2) hμlower hνl
    (by intro p hp; exact List.mem_ofFn.mp hp) hq.injective hG
    (by intro j hj p hp; exact hμtier j (by omega) p hp) (fun i p hp => hBtier i p hp)
    hcuts.2 hcuts.1 hcut.2.1 hcut.2.2.1 (fun p => initialRegularPrimeRange_upper L p p.property)
    hprimeBand (fun z hz p hp j => (hpage z hz p hp).1 j) (hq.avoids_giant_page)
    hpageν (hq.avoids_bulk_page) hsmallsets hcg
  unfold scheduledCellAmplitude at hamp
  rw [hdrop, scheduledRegularPrior_prime] at hamp
  rw [movingTemplatePrimeAmplitude_regular_congr Subtype.val (List.ofFn q)
    (completedCompensationPrior Aset Bset N Y endpoint D Q top cs) childBound pivotBound V
    F logCellProfile (fun _ => G) k (scheduledSmallLength []) (b + b)
    (smoothGiantPrimeRange G) (smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G)
    (fun i => primeSubsetPrior Q (Qν i))
    (normalizedResidueFamily (tailDensityMask Aset N)) (normalizedResidueFamily setsReg)
    (normalizedResidueFamily (tailDensityMask Aset N)) favorable
    (fun p => (normalizedResidueFamily_primeMaskExtension Q (tailDensityMask Aset N) p p.property).symm)] at hamp
  exact hamp

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.PublishedProgressionInput.selected_scheduled_final_contradiction_oai := @OAI.Ostmann.PublishedProgressionInput.selected_scheduled_final_contradiction_oai
