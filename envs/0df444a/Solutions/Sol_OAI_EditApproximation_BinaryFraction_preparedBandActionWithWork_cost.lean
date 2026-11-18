-- Prove2me | solution 1 for OAI.EditApproximation.BinaryFraction.preparedBandActionWithWork_cost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:23:51.778023+00:00
-- url     : https://prove2.me/submissions/72e177a7-8dd3-4138-8346-42c5163e0445

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_OAIQ361V3Ea002
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_bandVerticesWithWork_cost
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_gradientCellWithWork_cost
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_maximizerWithWork_cost
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_onlineLinearWithWork_cost
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_optimizerUpdateWithWork_cost

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_Numerics
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Finite numerical optimizer for edit-distance refinement

These are the explicit fixed-step recurrence and rational mixture
calculations from Section 9 of *An Almost-Linear Approximation Scheme
for Edit Distance* (September 24, 2026). The recurrence is an internal
analytic obligation of the manuscript, not an assumed published theorem.
-/

namespace EditApproximation

open Finset

/-- Executable finite rational comparisons, with the first listed
maximizer selected in a tie. The fallback only applies to an empty list. -/


theorem rationalLinearizationMaximizer_spec {ι : Type*} (coordinates : Finset ι)
    (vertices : List (ι → ℚ)) (gradient : ι → ℚ) (hvertices : vertices ≠ []) :
    rationalLinearizationMaximizer coordinates vertices gradient ∈ vertices ∧
      ∀ p ∈ vertices, (∑ i ∈ coordinates, gradient i * p i) ≤
        ∑ i ∈ coordinates, gradient i * rationalLinearizationMaximizer coordinates vertices gradient i := by
  unfold rationalLinearizationMaximizer
  cases harg : vertices.argmax (fun p => ∑ i ∈ coordinates, gradient i * p i) with
  | none => exact False.elim (hvertices (List.argmax_eq_none.mp harg))
  | some selected =>
    simp only [Option.getD_some]
    have hmem : selected ∈ vertices.argmax (fun p => ∑ i ∈ coordinates, gradient i * p i) := by
      rw [harg]
      simp
    exact ⟨List.argmax_mem hmem, fun p hp => List.le_of_mem_argmax
      (f := fun p : ι → ℚ => ∑ i ∈ coordinates, gradient i * p i) hp hmem⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_NumericalWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete numerical representation and arithmetic work

These are integer bit-length and exact rational-operation bounds for the
finite optimizer. They are not a RAM theorem: the costed evaluator below
counts rational arithmetic operations, while bit-operation costs also
require the charged evaluation model used by the surrounding algorithm.
-/

namespace EditApproximation

open Finset

theorem natural_product_bit_length (a b : ℕ) :
    Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  apply Nat.size_le.mpr
  calc
    a * b ≤ a * 2 ^ Nat.size b := Nat.mul_le_mul_left a (Nat.lt_size_self b).le
    _ < 2 ^ Nat.size a * 2 ^ Nat.size b :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) (by positivity)
    _ = 2 ^ (Nat.size a + Nat.size b) := (pow_add _ _ _).symm

theorem natural_sum_bit_length (a b : ℕ) :
    Nat.size (a + b) ≤ Nat.size a + Nat.size b + 1 := by
  apply Nat.size_le.mpr
  have ha : a < 2 ^ (Nat.size a + Nat.size b) :=
    (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hb : b < 2 ^ (Nat.size a + Nat.size b) :=
    (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [pow_succ]
  omega

theorem natural_power_bit_length (a n : ℕ) :
    Nat.size (a ^ n) ≤ n * Nat.size a + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hmul := natural_product_bit_length (a ^ n) a
    nlinarith

/-- Every logarithm series term is bounded on nonnegative inputs;
this controls the returned numerator without transcendental arithmetic. -/
theorem rationalLogApproximation_abs_bound (r : ℚ) (K : ℕ) (hr : 0 ≤ r) :
    |rationalLogApproximation r K| ≤ 2 * K := by
  let b := (r - 1) / (r + 1)
  have hrden : 0 < r + 1 := by linarith
  have hb : |b| ≤ 1 := by
    dsimp only [b]
    rw [abs_div, abs_of_pos hrden]
    apply (div_le_one₀ hrden).mpr
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hterm (k : ℕ) : |b ^ (2 * k + 1) / (2 * k + 1 : ℕ)| ≤ 1 := by
    have hden : (1 : ℚ) ≤ (2 * k + 1 : ℕ) := by norm_cast; omega
    have hdenpos : (0 : ℚ) < (2 * k + 1 : ℕ) := by positivity
    rw [abs_div, abs_pow, abs_of_pos hdenpos]
    calc
      _ ≤ (1 : ℚ) / (2 * k + 1 : ℕ) := div_le_div_of_nonneg_right
        (pow_le_one₀ (abs_nonneg b) hb) hdenpos.le
      _ ≤ 1 := (div_le_one₀ hdenpos).mpr hden
  have hsum : |∑ k ∈ range K, b ^ (2 * k + 1) / (2 * k + 1 : ℕ)| ≤ K := by
    calc
      _ ≤ ∑ k ∈ range K, |b ^ (2 * k + 1) / (2 * k + 1 : ℕ)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ range K, (1 : ℚ) := sum_le_sum (fun k _ => hterm k)
      _ = K := by simp
  unfold rationalLogApproximation
  push_cast at hsum
  dsimp only [b] at hsum
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 2)]
  linarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_UnreducedRational
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.nat_representation _root_.OAI.EditApproximation.BinaryFraction.representation_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.UnreducedRational.optimizerStep_value _root_.OAI.EditApproximation.UnreducedRational.value_nat _root_.OAI.EditApproximation.UnreducedRational.value_one _root_.OAI.EditApproximation.UnreducedRational.value_pow _root_.OAI.EditApproximation.UnreducedRational.value_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Exact fractions with positive, unreduced denominators. These operations
perform no greatest-common-divisor computation. The representation lemmas
apply to the intermediate fractions, not merely their reduced Rat values. -/

namespace EditApproximation



namespace UnreducedRational

theorem add_den_bits (a b : UnreducedRational) :
    Nat.size (a.add b).den ≤ Nat.size a.den + Nat.size b.den :=
  natural_product_bit_length _ _

theorem mul_den_bits (a b : UnreducedRational) :
    Nat.size (a.mul b).den ≤ Nat.size a.den + Nat.size b.den :=
  natural_product_bit_length _ _

theorem num_abs_le (a : UnreducedRational) (V : ℕ) (hvalue : |a.value| ≤ V) :
    a.num.natAbs ≤ V * a.den := by
  have hscaled := mul_le_mul_of_nonneg_right hvalue
    (show (0 : ℚ) ≤ a.den by exact_mod_cast a.den_pos.le)
  have hnum : |a.value| * (a.den : ℚ) = (a.num.natAbs : ℚ) := by
    unfold value
    rw [abs_div, abs_of_pos (by exact_mod_cast a.den_pos : (0 : ℚ) < a.den)]
    rw [div_mul_cancel₀ _ (by exact_mod_cast a.den_pos.ne' : (a.den : ℚ) ≠ 0)]
    simp [Int.cast_abs]
  rw [hnum] at hscaled
  exact_mod_cast hscaled

theorem storageBits_le (a : UnreducedRational) (V D : ℕ)
    (hvalue : |a.value| ≤ V) (hden : Nat.size a.den ≤ D) :
    a.storageBits ≤ Nat.size V + 2 * D + 1 := by
  have hnum := (Nat.size_le_size (a.num_abs_le V hvalue)).trans
    (natural_product_bit_length V a.den)
  unfold storageBits
  omega

end UnreducedRational

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_UnreducedNumerics
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.nat_representation _root_.OAI.EditApproximation.BinaryFraction.representation_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The numerical primitives executed on unreduced fractions. Their exact
values agree with the rational routines; their stored denominators
have polynomial bit length without cancellation or Euclidean normalization. -/

namespace EditApproximation

open Finset
namespace UnreducedRational

theorem pow_den (a : UnreducedRational) (n : ℕ) : (a.pow n).den = a.den ^ n := by
  induction n with
  | zero => simp [pow, one, ofRat]
  | succ n ih => simp [pow, mul, ih, pow_succ]

theorem pow_den_bits (a : UnreducedRational) (n : ℕ) :
    Nat.size (a.pow n).den ≤ n * Nat.size a.den + 1 := by
  rw [pow_den]
  exact natural_power_bit_length _ _

theorem nat_inv_den (n : ℕ) (hn : 0 < n) : (nat n).inv.den = n := by
  simp [nat, inv, hn.ne']

theorem logarithmPartial_value (b : UnreducedRational) (K : ℕ) :
    (logarithmPartial b K).value =
      ∑ k ∈ range K, b.value ^ (2 * k + 1) / (2 * k + 1 : ℕ) := by
  induction K with
  | zero => simp [logarithmPartial]
  | succ K ih => simp [logarithmPartial, ih, sum_range_succ]

@[simp] theorem logarithm_value (r : UnreducedRational) (K : ℕ) :
    (logarithm r K).value = rationalLogApproximation r.value K := by
  simp [logarithm, logarithmPartial_value, rationalLogApproximation]

theorem logarithmPartial_den_bits (b : UnreducedRational) (K : ℕ) :
    Nat.size (logarithmPartial b K).den ≤
      K * K * Nat.size b.den + K * (Nat.size (2 * K + 1) + 1) + 1 := by
  induction K with
  | zero => simp [logarithmPartial, zero]
  | succ K ih =>
    have hp := pow_den_bits b (2 * K + 1)
    have ht := mul_den_bits (b.pow (2 * K + 1)) (nat (2 * K + 1)).inv
    rw [nat_inv_den _ (by omega)] at ht
    have ha := add_den_bits (logarithmPartial b K)
      ((b.pow (2 * K + 1)).div (nat (2 * K + 1)))
    have hs := Nat.size_le_size (by omega : 2 * K + 1 ≤ 2 * (K + 1) + 1)
    change Nat.size ((logarithmPartial b K).add
      ((b.pow (2 * K + 1)).div (nat (2 * K + 1)))).den ≤ _
    change Nat.size ((b.pow (2 * K + 1)).div (nat (2 * K + 1))).den ≤ _ at ht
    have hweighted := Nat.mul_le_mul_left K hs
    nlinarith only [ih, hp, ht, ha, hweighted, hs]

theorem logarithm_storageBits (r : UnreducedRational) (K : ℕ) (hr : 0 ≤ r.value) :
    (logarithm r K).storageBits ≤ Nat.size (2 * K) +
      2 * (K * K * Nat.size ((r.sub one).div (r.add one)).den +
        K * (Nat.size (2 * K + 1) + 1) + 1) + 1 := by
  apply storageBits_le
  · rw [logarithm_value]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using rationalLogApproximation_abs_bound r.value K hr
  · simpa only [logarithm, mul, nat, Nat.one_mul] using
      logarithmPartial_den_bits ((r.sub one).div (r.add one)) K

theorem optimizerStep_den (j : ℕ) : (optimizerStep j).den = j + 2 := by
  change (nat 2).den * (nat (j + 2)).inv.den = j + 2
  rw [nat_inv_den _ (by omega)]
  simp [nat]

theorem optimizerIterate_den_bits {ι : Type*} (initial : ι → UnreducedRational)
    (selected : ℕ → ι → UnreducedRational) (K B : ℕ) (i : ι)
    (hinitial : Nat.size (initial i).den ≤ B)
    (hselected : ∀ j < K, Nat.size (selected j i).den ≤ B) :
    Nat.size (optimizerIterate initial selected K i).den ≤
      B + K * (2 * Nat.size (K + 1) + B) := by
  induction K with
  | zero => simpa [optimizerIterate] using hinitial
  | succ K ih =>
    have hp := ih (fun j hj => hselected j (by omega))
    have hs := hselected K (by omega)
    have hsize := Nat.size_le_size (by omega : K + 1 ≤ K + 1 + 1)
    have hfirst := mul_den_bits (one.sub (optimizerStep K)) (optimizerIterate initial selected K i)
    have hsecond := mul_den_bits (optimizerStep K) (selected K i)
    have hsum := add_den_bits
      ((one.sub (optimizerStep K)).mul (optimizerIterate initial selected K i))
      ((optimizerStep K).mul (selected K i))
    have hcomplement : (one.sub (optimizerStep K)).den = K + 2 := by
      simp only [sub, add, neg, one, ofRat, Rat.den_one, Nat.one_mul, optimizerStep_den]
    rw [hcomplement] at hfirst
    rw [optimizerStep_den] at hsecond
    change Nat.size (((one.sub (optimizerStep K)).mul (optimizerIterate initial selected K i)).add
      ((optimizerStep K).mul (selected K i))).den ≤ _
    have hweighted := Nat.mul_le_mul_left K hsize
    nlinarith only [hp, hs, hfirst, hsecond, hsum, hweighted]

end UnreducedRational
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_OptimizerBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Representation bounds for the actual stored optimizer iterates. -/

namespace EditApproximation

open Finset

theorem finiteRationalOptimizer_coordinate_bounds {ι : Type*}
    (coordinates : Finset ι) (vertices : List (ι → ℚ)) (linear : ι → ℚ)
    (G j : ℕ) (hvertices : vertices ≠ []) (i : ι)
    (hinput : ∀ vertex ∈ vertices, 0 ≤ vertex i ∧ vertex i ≤ 1) :
    0 ≤ finiteRationalOptimizer coordinates vertices linear G j i ∧
      finiteRationalOptimizer coordinates vertices linear G j i ≤ 1 := by
  induction j with
  | zero =>
    cases vertices with
    | nil => exact False.elim (hvertices rfl)
    | cons vertex rest => exact hinput vertex List.mem_cons_self
  | succ j ih =>
    have hselected := (rationalLinearizationMaximizer_spec coordinates vertices
      (rationalSmoothedGradient G linear (finiteRationalOptimizer coordinates vertices linear G j))
      hvertices).1
    have hbounds := hinput _ hselected
    have hden : (0 : ℚ) < (j : ℚ) + 2 := by positivity
    have hweight : (0 : ℚ) ≤ 2 / ((j : ℚ) + 2) := by positivity
    have hweightOne : (2 : ℚ) / ((j : ℚ) + 2) ≤ 1 :=
      (div_le_one₀ hden).2 (by have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg _; linarith)
    change 0 ≤ (1 - 2 / ((j : ℚ) + 2)) * _ + 2 / ((j : ℚ) + 2) * _ ∧
      (1 - 2 / ((j : ℚ) + 2)) * _ + 2 / ((j : ℚ) + 2) * _ ≤ 1
    have hcomplement : 0 ≤ 1 - (2 : ℚ) / ((j : ℚ) + 2) := sub_nonneg.mpr hweightOne
    constructor
    · exact add_nonneg (mul_nonneg hcomplement ih.1) (mul_nonneg hweight hbounds.1)
    · calc
        _ ≤ (1 - 2 / ((j : ℚ) + 2)) * 1 + (2 : ℚ) / ((j : ℚ) + 2) * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left ih.2 hcomplement)
            (mul_le_mul_of_nonneg_left hbounds.2 hweight)
        _ = 1 := by ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_UnreducedOptimizer
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.nat_representation _root_.OAI.EditApproximation.BinaryFraction.representation_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fraction-only implementation of the actual finite optimizer. None of
its arithmetic or score comparisons requires reduced rational numbers. -/

namespace EditApproximation

open Finset
namespace UnreducedRational

theorem scoredArgmax_spec {α : Type*} (score : α → UnreducedRational) (values : List α) :
    scoredArgmax score values =
      (values.argmax (fun a => (score a).value)).map (fun a => (a, score a)) := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
    simp only [scoredArgmax, ih, List.argmax_cons]
    cases h : rest.argmax (fun a => (score a).value) with
    | none => rfl
    | some best => simp only [Option.map_some, lt_eq_true]; split_ifs <;> rfl

theorem gradient_value {d : ℕ} (G : ℕ) (linear point : Vector UnreducedRational d) (i : Fin d) :
    ((gradient G linear point).get i).value =
      rationalSmoothedGradient G (fun i => (linear.get i).value) (fun i => (point.get i).value) i := by
  simp [gradient, gradientCell, rationalSmoothedGradient, one_div]

theorem maximizer_value {d : ℕ} (gradient : Vector UnreducedRational d)
    (vertices : List (Vector UnreducedRational d)) :
    (fun i => ((maximizer gradient vertices).get i).value) =
      rationalLinearizationMaximizer univ
        (vertices.map fun vertex i => (vertex.get i).value) (fun i => (gradient.get i).value) := by
  have hmap := argmax_map_commutes (fun vertex : Vector UnreducedRational d => fun i => (vertex.get i).value)
    (fun vertex => ∑ i, (gradient.get i).value * vertex i) vertices
  simp only [maximizer, scoredArgmax_spec, dot_value, Option.map_map, Function.comp_def]
  unfold rationalLinearizationMaximizer
  rw [hmap]
  cases h : vertices.argmax (fun vertex => ∑ i, (gradient.get i).value * (vertex.get i).value) with
  | none => funext i; simp [value_zero]
  | some vertex => rfl

theorem finiteOptimizer_value {d : ℕ} (vertices : List (Vector UnreducedRational d))
    (linear : Vector UnreducedRational d) (G K : ℕ) :
    (fun i => ((finiteOptimizer vertices linear G K).get i).value) =
      finiteRationalOptimizer univ (vertices.map fun vertex i => (vertex.get i).value)
        (fun i => (linear.get i).value) G K := by
  induction K with
  | zero =>
    cases vertices with
    | nil => funext i; simp [finiteOptimizer, finiteRationalOptimizer]
    | cons vertex rest => rfl
  | succ K ih =>
    funext i
    simp only [finiteOptimizer, vector_get_ofFn, value_add, value_mul, value_sub, value_one,
      optimizerStep_value, finiteRationalOptimizer]
    rw [congrFun ih i]
    have hm := maximizer_value (gradient G linear (finiteOptimizer vertices linear G K)) vertices
    have hg : (fun i => ((gradient G linear (finiteOptimizer vertices linear G K)).get i).value) =
        rationalSmoothedGradient G (fun i => (linear.get i).value)
          (finiteRationalOptimizer univ (vertices.map fun vertex i => (vertex.get i).value)
            (fun i => (linear.get i).value) G K) := by
      funext i
      rw [gradient_value]
      rw [ih]
    rw [hg] at hm
    rw [congrFun hm i]

theorem maximizer_mem {d : ℕ} (gradient : Vector UnreducedRational d)
    (vertices : List (Vector UnreducedRational d)) (hvertices : vertices ≠ []) :
    maximizer gradient vertices ∈ vertices := by
  unfold maximizer
  rw [scoredArgmax_spec]
  cases h : vertices.argmax (fun vertex => (dot gradient vertex).value) with
  | none => exact False.elim (hvertices (List.argmax_eq_none.mp h))
  | some vertex =>
    simp only [Option.map_some, Option.getD_some]
    exact List.argmax_mem (by rw [h]; simp)

theorem finiteOptimizer_eq_iterate {d : ℕ} (vertices : List (Vector UnreducedRational d))
    (linear : Vector UnreducedRational d) (G K : ℕ) (i : Fin d) :
    (finiteOptimizer vertices linear G K).get i =
      optimizerIterate (vertices.headD (Vector.replicate d zero)).get
        (fun j => (maximizer (gradient G linear (finiteOptimizer vertices linear G j)) vertices).get) K i := by
  induction K with
  | zero => rfl
  | succ K ih => simp only [finiteOptimizer, vector_get_ofFn, optimizerIterate, ih]

theorem finiteOptimizer_den_bits {d : ℕ} (vertices : List (Vector UnreducedRational d))
    (linear : Vector UnreducedRational d) (G K B : ℕ) (i : Fin d)
    (hvertices : vertices ≠ [])
    (hinput : ∀ vertex ∈ vertices, Nat.size (vertex.get i).den ≤ B) :
    Nat.size ((finiteOptimizer vertices linear G K).get i).den ≤
      B + K * (2 * Nat.size (K + 1) + B) := by
  rw [finiteOptimizer_eq_iterate]
  apply optimizerIterate_den_bits
  · apply hinput
    cases vertices with
    | nil => exact False.elim (hvertices rfl)
    | cons vertex rest => exact List.mem_cons_self
  · intro j _
    exact hinput _ (maximizer_mem _ vertices hvertices)

theorem finiteOptimizer_storageBits {d : ℕ} (vertices : List (Vector UnreducedRational d))
    (linear : Vector UnreducedRational d) (G K B : ℕ) (i : Fin d)
    (hvertices : vertices ≠ [])
    (hinput : ∀ vertex ∈ vertices,
      (0 ≤ (vertex.get i).value ∧ (vertex.get i).value ≤ 1) ∧ Nat.size (vertex.get i).den ≤ B) :
    ((finiteOptimizer vertices linear G K).get i).storageBits ≤
      2 * (B + K * (2 * Nat.size (K + 1) + B)) + 2 := by
  have hlist : (vertices.map fun vertex j => (vertex.get j).value) ≠ [] := by
    intro h
    exact hvertices (List.map_eq_nil_iff.mp h)
  have hpoint := finiteRationalOptimizer_coordinate_bounds univ
    (vertices.map fun vertex j => (vertex.get j).value) (fun j => (linear.get j).value)
    G K hlist i (by
      intro vertex hv
      obtain ⟨stored, hs, rfl⟩ := List.mem_map.mp hv
      exact (hinput stored hs).1)
  rw [← congrFun (finiteOptimizer_value vertices linear G K) i] at hpoint
  have h := storageBits_le ((finiteOptimizer vertices linear G K).get i) 1
    (B + K * (2 * Nat.size (K + 1) + B)) (by
      rw [abs_of_nonneg hpoint.1]
      exact hpoint.2) (finiteOptimizer_den_bits vertices linear G K B i hvertices
        (fun vertex hv => (hinput vertex hv).2))
  simp only [Nat.size_one] at h
  omega

end UnreducedRational
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCanonicalWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.denominatorInteger_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Removing only leading zero bits of an integer word. This is unrelated
to rational reduction: no common divisor is computed. -/

namespace EditApproximation



theorem trimBitWordWithWork_canonical (bits : List Bool) :
    (trimBitWordWithWork bits).1 = (bitWordValue bits).bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    by_cases hzero : bitWordValue bits = 0
    · rw [trimBitWordWithWork, ih, hzero]
      cases bit <;> simp [bitWordValue, hzero]
    · have hnonempty : (bitWordValue bits).bits ≠ [] := by
        intro h
        have hv := bitWordValue_bits (bitWordValue bits)
        rw [h] at hv
        exact hzero hv.symm
      have hvalue : bitWordValue (bit :: bits) = Nat.bit bit (bitWordValue bits) := by
        cases bit <;> simp [bitWordValue, Nat.bit, Nat.add_comm]
      rw [trimBitWordWithWork, ih, ite_eq_right (by simp [hnonempty]), hvalue,
        Nat.bits_append_bit _ _ (fun h => False.elim (hzero h))]

theorem trimBitWordWithWork_length (bits : List Bool) :
    (trimBitWordWithWork bits).1.length = Nat.size (bitWordValue bits) := by
  rw [trimBitWordWithWork_canonical, Nat.size_eq_bits_len]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryFractionWork
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Unreduced fractions stored as Boolean words. Every numerator operation
below runs the literal signed ripple/shift-add code; denominator products
run the literal Boolean multiplication routine. -/

namespace EditApproximation



namespace BinaryFraction







theorem neg_value (a : BinaryFraction) : a.neg.value = -a.value := by
  simp [neg, value, neg_div]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_CanonicalFractionWork
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_representation _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.UnreducedRational.logarithm_value _root_.OAI.EditApproximation.UnreducedRational.value_pow _root_.OAI.EditApproximation.UnreducedRational.value_sub _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Fractions retain their unreduced numerator and denominator, but discard
leading zero bits after each operation. This exposes actual storage length
without charging or performing rational normalization. -/

namespace EditApproximation
namespace BinaryFraction



theorem canonicalizeWithWork_width (a : BinaryFraction) :
    (canonicalizeWithWork a).1.width =
      max (Nat.size a.representation.num.natAbs) (Nat.size a.representation.den) := by
  have hnum : a.numerator.value.natAbs = bitWordValue a.numerator.bits := by
    cases h : a.numerator.negative <;> simp [SignedBinary.value, signedMagnitude, h]
  simp only [canonicalizeWithWork, width, trimBitWordWithWork_length, representation, hnum]

theorem canonicalizeWithWork_width_le_storageBits (a : BinaryFraction) :
    (canonicalizeWithWork a).1.width ≤ a.representation.storageBits := by
  rw [canonicalizeWithWork_width]
  unfold UnreducedRational.storageBits
  exact max_le (by omega) (by omega)

theorem canonicalAddWithWork_width_le_storageBits (a b : BinaryFraction) :
    (canonicalAddWithWork a b).1.width ≤
      (a.representation.add b.representation).storageBits := by
  have h := canonicalizeWithWork_width_le_storageBits (a.addWithWork b).1
  rw [addWithWork_representation] at h
  exact h

theorem canonicalMulWithWork_width_le_storageBits (a b : BinaryFraction) :
    (canonicalMulWithWork a b).1.width ≤
      (a.representation.mul b.representation).storageBits := by
  have h := canonicalizeWithWork_width_le_storageBits (a.mulWithWork b).1
  rw [mulWithWork_representation] at h
  exact h

theorem canonicalAddWithWork_self_width (a b : BinaryFraction) :
    (canonicalAddWithWork a b).1.width ≤ (canonicalAddWithWork a b).1.representation.storageBits := by
  rw [canonicalAddWithWork_representation]
  exact canonicalAddWithWork_width_le_storageBits a b

theorem canonicalMulWithWork_self_width (a b : BinaryFraction) :
    (canonicalMulWithWork a b).1.width ≤ (canonicalMulWithWork a b).1.representation.storageBits := by
  rw [canonicalMulWithWork_representation]
  exact canonicalMulWithWork_width_le_storageBits a b

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRawNumerics
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The optimizer's numerical loops executed on Boolean fraction storage.
The value proofs identify the unreduced numerator and denominator, not just
the represented rational. Thus the raw storage bounds apply to this code. -/

namespace EditApproximation
namespace BinaryFraction



theorem powWithWork_representation (a : BinaryFraction) (k : ℕ) :
    (a.powWithWork k).1.representation = a.representation.pow k := by
  induction k with
  | zero => exact one_representation
  | succ k ih => simp only [powWithWork, canonicalMulWithWork_representation,
      UnreducedRational.pow, ih]



theorem logarithmPartialWithWork_representation (b : BinaryFraction) (k : ℕ) :
    (b.logarithmPartialWithWork k).1.representation = b.representation.logarithmPartial k := by
  induction k with
  | zero => exact zero_representation
  | succ k ih => simp only [logarithmPartialWithWork, canonicalAddWithWork_representation,
      divWithWork_representation, powWithWork_representation, nat_representation,
      UnreducedRational.logarithmPartial, ih]



theorem logarithmWithWork_representation (r : BinaryFraction) (k : ℕ) :
    (r.logarithmWithWork k).1.representation = r.representation.logarithm k := by
  simp only [logarithmWithWork, canonicalMulWithWork_representation,
    logarithmPartialWithWork_representation, divWithWork_representation,
    subWithWork_representation, canonicalAddWithWork_representation,
    nat_representation, one_representation, UnreducedRational.logarithm]



theorem gradientCellWithWork_representation {d : ℕ} (G : ℕ)
    (linear point : Vector BinaryFraction d) (i : Fin d) :
    (gradientCellWithWork G linear point i).1.representation =
      UnreducedRational.gradientCell G (linear.map representation) (point.map representation) i := by
  simp only [gradientCellWithWork, canonicalAddWithWork_representation,
    subWithWork_representation, logarithmWithWork_representation, neg_representation,
    one_representation, invWithWork_representation, powWithWork_representation,
    nat_representation, UnreducedRational.gradientCell, vector_map_get]

theorem zero_width_le_storageBits : zero.width ≤ zero.representation.storageBits := by decide

theorem gradientCellWithWork_width_le_storageBits {d : ℕ} (G : ℕ)
    (linear point : Vector BinaryFraction d) (i : Fin d) :
    (gradientCellWithWork G linear point i).1.width ≤
      (gradientCellWithWork G linear point i).1.representation.storageBits := by
  dsimp only [gradientCellWithWork]
  exact canonicalAddWithWork_self_width _ _

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRawOptimizer
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Complete materialized entropy optimizer on Boolean fraction storage.
Every arithmetic operation invokes the counted Boolean implementation. -/

namespace EditApproximation
namespace BinaryFraction

open Finset



theorem gradientWithWork_representation {d : ℕ} (G : ℕ) (linear point : Vector BinaryFraction d) :
    (gradientWithWork G linear point).1.map representation =
      UnreducedRational.gradient G (linear.map representation) (point.map representation) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  change ((gradientWithWork G linear point).1.get ⟨i, hi⟩).representation =
    (UnreducedRational.gradient G (linear.map representation) (point.map representation)).get ⟨i, hi⟩
  rw [gradientWithWork, vectorMapWithWork_value]
  simpa only [UnreducedRational.gradient, vector_get_ofFn] using
    gradientCellWithWork_representation G linear point ⟨i, hi⟩



theorem scoredArgmaxWithWork_value {α : Type*} (score : α → BinaryFraction × ℕ) (values : List α) :
    (scoredArgmaxWithWork score values).1 =
      (values.argmax (fun a => (score a).1.value)).map (fun a => (a, (score a).1)) := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
    simp only [scoredArgmaxWithWork, ih, List.argmax_cons]
    cases h : rest.argmax (fun a => (score a).1.value) with
    | none => rfl
    | some best => simp only [Option.map_some, ltWithWork_value]; split_ifs <;> rfl



theorem maximizerWithWork_representation {d : ℕ} (gradient : Vector BinaryFraction d)
    (vertices : List (Vector BinaryFraction d)) :
    (maximizerWithWork gradient vertices).1.map representation =
      UnreducedRational.maximizer (gradient.map representation) (vertices.map fun v => v.map representation) := by
  have hscore (v : Vector BinaryFraction d) :
      (dotWithWork gradient v).1.value =
        (UnreducedRational.dot (gradient.map representation) (v.map representation)).value := by
    rw [← dotWithWork_representation, representation_value]
  have hmap := argmax_map_commutes (fun v : Vector BinaryFraction d => v.map representation)
    (fun v => (UnreducedRational.dot (gradient.map representation) v).value) vertices
  simp only [maximizerWithWork, scoredArgmaxWithWork_value, hscore, Option.map_map,
    Function.comp_def, UnreducedRational.maximizer, UnreducedRational.scoredArgmax_spec]
  rw [hmap]
  cases h : vertices.argmax (fun v =>
      (UnreducedRational.dot (gradient.map representation) (v.map representation)).value) with
  | none =>
    apply Vector.ext
    intro i hi
    simp [zero_representation]
  | some v => rfl



theorem optimizerUpdateWithWork_representation {d : ℕ} (j : ℕ)
    (previous selected : Vector BinaryFraction d) (i : Fin d) :
    ((optimizerUpdateWithWork j previous selected).1.get i).representation =
      ((UnreducedRational.one.sub (UnreducedRational.optimizerStep j)).mul
        (previous.get i).representation).add
      ((UnreducedRational.optimizerStep j).mul (selected.get i).representation) := by
  simp only [optimizerUpdateWithWork, vectorMapWithWork_value,
    canonicalAddWithWork_representation, canonicalMulWithWork_representation,
    subWithWork_representation, divWithWork_representation, nat_representation,
    one_representation, UnreducedRational.optimizerStep]



theorem finiteOptimizerWithWork_representation {d : ℕ} (vertices : List (Vector BinaryFraction d))
    (linear : Vector BinaryFraction d) (G K : ℕ) :
    (finiteOptimizerWithWork vertices linear G K).1.map representation =
      UnreducedRational.finiteOptimizer (vertices.map fun v => v.map representation)
        (linear.map representation) G K := by
  induction K with
  | zero =>
    cases vertices with
    | nil =>
      apply Vector.ext
      intro i hi
      simp [finiteOptimizerWithWork, UnreducedRational.finiteOptimizer, zero_representation]
    | cons v vs => rfl
  | succ K ih =>
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map]
    change (((optimizerUpdateWithWork K (finiteOptimizerWithWork vertices linear G K).1
      (maximizerWithWork (gradientWithWork G linear
        (finiteOptimizerWithWork vertices linear G K).1).1 vertices).1).1.get ⟨i, hi⟩).representation) = _
    rw [optimizerUpdateWithWork_representation]
    have hg := gradientWithWork_representation G linear (finiteOptimizerWithWork vertices linear G K).1
    rw [ih] at hg
    have hm := maximizerWithWork_representation
      (gradientWithWork G linear (finiteOptimizerWithWork vertices linear G K).1).1 vertices
    rw [hg] at hm
    have hp := congrArg (fun v : Vector UnreducedRational d => v.get ⟨i, hi⟩) ih
    have hs := congrArg (fun v : Vector UnreducedRational d => v.get ⟨i, hi⟩) hm
    simpa only [UnreducedRational.finiteOptimizer, vector_map_get, Vector.getElem_ofFn] using
      congrArg₂ UnreducedRational.add
        (congrArg (UnreducedRational.mul (UnreducedRational.one.sub (UnreducedRational.optimizerStep K))) hp)
        (congrArg (UnreducedRational.mul (UnreducedRational.optimizerStep K)) hs)

theorem finiteOptimizerWithWork_value {d : ℕ} (vertices : List (Vector BinaryFraction d))
    (linear : Vector BinaryFraction d) (G K : ℕ) :
    (fun i => ((finiteOptimizerWithWork vertices linear G K).1.get i).value) =
      finiteRationalOptimizer univ (vertices.map fun v i => (v.get i).value)
        (fun i => (linear.get i).value) G K := by
  have h := finiteOptimizerWithWork_representation vertices linear G K
  have hvalue := UnreducedRational.finiteOptimizer_value
    (vertices.map fun v => v.map representation) (linear.map representation) G K
  rw [← h] at hvalue
  simpa only [vector_map_get, representation_value, List.map_map, Function.comp_def] using hvalue

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_UnreducedStorage
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.nat_representation _root_.OAI.EditApproximation.BinaryFraction.representation_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial raw storage bounds used by the Boolean numerical loops. -/

namespace EditApproximation
namespace UnreducedRational

open Finset

theorem storageBits_nat (n : ℕ) : (nat n).storageBits = Nat.size n + 2 := by
  simp [nat, storageBits]

theorem storageBits_one : one.storageBits = 3 := by decide

theorem storageBits_zero : zero.storageBits = 2 := by decide

theorem storageBits_neg (a : UnreducedRational) : a.neg.storageBits = a.storageBits := by
  simp [neg, storageBits]

theorem storageBits_add (a b : UnreducedRational) :
    (a.add b).storageBits ≤ 2 * a.storageBits + 2 * b.storageBits + 2 := by
  have hnum := (Nat.size_le_size (Int.natAbs_add_le (a.num * b.den) (b.num * a.den))).trans
    (natural_sum_bit_length (a.num * b.den).natAbs (b.num * a.den).natAbs)
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hnum
  have hleft := natural_product_bit_length a.num.natAbs b.den
  have hright := natural_product_bit_length b.num.natAbs a.den
  have hden := add_den_bits a b
  dsimp only [add, storageBits] at *
  omega

theorem storageBits_mul (a b : UnreducedRational) :
    (a.mul b).storageBits ≤ a.storageBits + b.storageBits := by
  have hnum := natural_product_bit_length a.num.natAbs b.num.natAbs
  have hden := mul_den_bits a b
  simp only [mul, storageBits, Int.natAbs_mul] at *
  omega

theorem storageBits_sub (a b : UnreducedRational) :
    (a.sub b).storageBits ≤ 2 * a.storageBits + 2 * b.storageBits + 2 := by
  simpa only [sub, storageBits_neg] using storageBits_add a b.neg

theorem storageBits_inv (a : UnreducedRational) : a.inv.storageBits ≤ a.storageBits + 2 := by
  by_cases h : a.num = 0
  · simp only [inv, h, ↓reduceDIte, storageBits_zero]
    omega
  · simp only [inv, h, ↓reduceDIte, storageBits, Int.natAbs_mul,
      Int.natAbs_sign_of_ne_zero h, Int.natAbs_natCast, Nat.one_mul]
    omega

theorem storageBits_div (a b : UnreducedRational) :
    (a.div b).storageBits ≤ a.storageBits + b.storageBits + 2 := by
  exact (storageBits_mul a b.inv).trans (by have h := storageBits_inv b; omega)

theorem logarithmRatio_storageBits (r : UnreducedRational) :
    ((r.sub one).div (r.add one)).storageBits ≤ 4 * r.storageBits + 18 := by
  have hsub := storageBits_sub r one
  have hadd := storageBits_add r one
  have hdiv := storageBits_div (r.sub one) (r.add one)
  rw [storageBits_one] at hsub hadd
  omega

theorem logarithm_storageBits_poly (r : UnreducedRational) (K : ℕ) (hr : 0 ≤ r.value) :
    (logarithm r K).storageBits ≤
      Nat.size (2 * K) + 2 * (K * K * (4 * r.storageBits + 18) +
        K * (Nat.size (2 * K + 1) + 1) + 1) + 1 := by
  have h := logarithm_storageBits r K hr
  have hratio := logarithmRatio_storageBits r
  have hd : Nat.size ((r.sub one).div (r.add one)).den ≤ 4 * r.storageBits + 18 := by
    exact (by dsimp only [storageBits]; omega :
      Nat.size ((r.sub one).div (r.add one)).den ≤ ((r.sub one).div (r.add one)).storageBits).trans hratio
  have hm := Nat.mul_le_mul_left (K * K) hd
  omega

theorem pow_storageBits (a : UnreducedRational) (n : ℕ) :
    (a.pow n).storageBits ≤ 3 + n * a.storageBits := by
  induction n with
  | zero => simpa only [pow, Nat.zero_mul, Nat.add_zero] using storageBits_one.le
  | succ n ih =>
    have hm := storageBits_mul (a.pow n) a
    simp only [pow]
    nlinarith only [ih, hm]

theorem logarithmStorageBudget_mono {A B : ℕ} (h : A ≤ B) (K : ℕ) :
    logarithmStorageBudget A K ≤ logarithmStorageBudget B K := by
  have hm := Nat.mul_le_mul_left (K * K) (show 4 * A + 18 ≤ 4 * B + 18 by omega)
  unfold logarithmStorageBudget
  omega

theorem gradientCell_storageBits {d : ℕ} (G : ℕ) (linear point : Vector UnreducedRational d)
    (i : Fin d) (hpoint : 0 ≤ (point.get i).value) :
    (gradientCell G linear point i).storageBits ≤
      gradientStorageBudget G (point.get i).storageBits (linear.get i).storageBits := by
  let smoothing := (nat G).pow 50
  let shifted := (point.get i).add smoothing.inv
  have hs : smoothing.storageBits ≤ 3 + 50 * (Nat.size G + 2) := by
    simpa only [smoothing, storageBits_nat] using pow_storageBits (nat G) 50
  have hi := storageBits_inv smoothing
  have ha := storageBits_add (point.get i) smoothing.inv
  have hshift : shifted.storageBits ≤ 2 * (point.get i).storageBits +
      2 * (5 + 50 * (Nat.size G + 2)) + 2 := by
    dsimp only [shifted]
    omega
  have hpositive : 0 ≤ shifted.value := by
    dsimp only [shifted, smoothing]
    simp only [value_add, value_inv, value_pow, value_nat]
    exact add_nonneg hpoint (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg G) _))
  have hlog := (logarithm_storageBits_poly shifted (G ^ 60) hpositive).trans
    (logarithmStorageBudget_mono hshift (G ^ 60))
  have hsub := storageBits_sub (logarithm shifted (G ^ 60)).neg one
  rw [storageBits_neg, storageBits_one] at hsub
  have hadd := storageBits_add ((logarithm shifted (G ^ 60)).neg.sub one) (linear.get i)
  change (((logarithm shifted (G ^ 60)).neg.sub one).add (linear.get i)).storageBits ≤ _
  unfold gradientStorageBudget
  omega

theorem dotList_den_bits {d : ℕ} (left right : Vector UnreducedRational d)
    (indices : List (Fin d)) (L R : ℕ)
    (hl : ∀ i ∈ indices, Nat.size (left.get i).den ≤ L)
    (hr : ∀ i ∈ indices, Nat.size (right.get i).den ≤ R) :
    Nat.size (dotList left right indices).den ≤ 1 + indices.length * (L + R) := by
  induction indices with
  | nil => simp [dotList, zero]
  | cons i rest ih =>
    have ht := ih (fun i hi => hl i (List.mem_cons_of_mem _ hi))
      (fun i hi => hr i (List.mem_cons_of_mem _ hi))
    have hi := mul_den_bits (left.get i) (right.get i)
    have hs := add_den_bits ((left.get i).mul (right.get i)) (dotList left right rest)
    have hil := hl i List.mem_cons_self
    have hir := hr i List.mem_cons_self
    change Nat.size (((left.get i).mul (right.get i)).add (dotList left right rest)).den ≤ _
    simp only [List.length_cons]
    nlinarith only [ht, hi, hs, hil, hir]

theorem dotList_abs_le {d : ℕ} (left right : Vector UnreducedRational d)
    (indices : List (Fin d)) (L R : ℕ)
    (hl : ∀ i ∈ indices, |(left.get i).value| ≤ L)
    (hr : ∀ i ∈ indices, |(right.get i).value| ≤ R) :
    |(dotList left right indices).value| ≤ indices.length * L * R := by
  induction indices with
  | nil => simp [dotList]
  | cons i rest ih =>
    have ht := ih (fun i hi => hl i (List.mem_cons_of_mem _ hi))
      (fun i hi => hr i (List.mem_cons_of_mem _ hi))
    have hi := mul_le_mul (hl i List.mem_cons_self) (hr i List.mem_cons_self)
      (abs_nonneg _) (Nat.cast_nonneg L)
    simp only [dotList, value_add, value_mul]
    calc
      _ ≤ |(left.get i).value * (right.get i).value| + |(dotList left right rest).value| := abs_add_le _ _
      _ ≤ (L : ℚ) * R + rest.length * L * R := by rw [abs_mul]; exact add_le_add hi ht
      _ = (i :: rest).length * L * R := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one] <;> ring

theorem dotList_storageBits {d : ℕ} (left right : Vector UnreducedRational d)
    (indices : List (Fin d)) (BL BR VL VR : ℕ)
    (hlbits : ∀ i ∈ indices, Nat.size (left.get i).den ≤ BL)
    (hrbits : ∀ i ∈ indices, Nat.size (right.get i).den ≤ BR)
    (hlvalue : ∀ i ∈ indices, |(left.get i).value| ≤ VL)
    (hrvalue : ∀ i ∈ indices, |(right.get i).value| ≤ VR) :
    (dotList left right indices).storageBits ≤ Nat.size (indices.length * VL * VR) +
      2 * (1 + indices.length * (BL + BR)) + 1 := by
  apply storageBits_le
  · simpa only [Nat.cast_mul] using dotList_abs_le left right indices VL VR hlvalue hrvalue
  · exact dotList_den_bits left right indices BL BR hlbits hrbits

end UnreducedRational
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRawStorage
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Boolean word lengths in the materialized numerical implementation.
These bounds use the stored unreduced values, without a gcd reduction. -/

namespace EditApproximation
namespace BinaryFraction

theorem gradientCellWithWork_width {d : ℕ} (G : ℕ)
    (linear point : Vector BinaryFraction d) (i : Fin d) (hpoint : 0 ≤ (point.get i).value) :
    (gradientCellWithWork G linear point i).1.width ≤
      UnreducedRational.gradientStorageBudget G (point.get i).representation.storageBits
        (linear.get i).representation.storageBits := by
  have hraw := UnreducedRational.gradientCell_storageBits G (linear.map representation)
    (point.map representation) i (by simpa only [vector_map_get, representation_value] using hpoint)
  simp only [vector_map_get] at hraw
  have hwidth := gradientCellWithWork_width_le_storageBits G linear point i
  rw [gradientCellWithWork_representation] at hwidth
  exact hwidth.trans hraw

theorem finiteOptimizerWithWork_coordinate_normalized {d : ℕ}
    (vertices : List (Vector BinaryFraction d)) (linear : Vector BinaryFraction d) (G K : ℕ)
    (hvertices : vertices ≠ [])
    (hinput : ∀ v ∈ vertices, ∀ i : Fin d, (v.get i).width ≤ (v.get i).representation.storageBits)
    (i : Fin d) :
    ((finiteOptimizerWithWork vertices linear G K).1.get i).width ≤
      ((finiteOptimizerWithWork vertices linear G K).1.get i).representation.storageBits := by
  cases K with
  | zero =>
    cases vertices with
    | nil => exact False.elim (hvertices rfl)
    | cons v vs => exact hinput v List.mem_cons_self i
  | succ K =>
    simp only [finiteOptimizerWithWork, optimizerUpdateWithWork, vectorMapWithWork_value]
    exact canonicalAddWithWork_self_width _ _

theorem finiteOptimizerWithWork_coordinate_width {d : ℕ}
    (vertices : List (Vector BinaryFraction d)) (linear : Vector BinaryFraction d) (G K B : ℕ)
    (hvertices : vertices ≠ [])
    (hinput : ∀ v ∈ vertices, ∀ i : Fin d,
      (v.get i).width ≤ (v.get i).representation.storageBits ∧
      (0 ≤ (v.get i).value ∧ (v.get i).value ≤ 1) ∧ Nat.size (v.get i).representation.den ≤ B)
    (i : Fin d) :
    ((finiteOptimizerWithWork vertices linear G K).1.get i).width ≤
      2 * (B + K * (2 * Nat.size (K + 1) + B)) + 2 := by
  have hn : (vertices.map fun v => v.map representation) ≠ [] := by
    intro h
    exact hvertices (List.map_eq_nil_iff.mp h)
  have hr := UnreducedRational.finiteOptimizer_storageBits
    (vertices.map fun v => v.map representation) (linear.map representation) G K B i hn (by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
      simpa only [vector_map_get, representation_value] using (hinput w hw i).2)
  have hrep := congrArg (fun v : Vector UnreducedRational d => v.get i)
    (finiteOptimizerWithWork_representation vertices linear G K)
  simp only [vector_map_get] at hrep
  rw [← hrep] at hr
  exact (finiteOptimizerWithWork_coordinate_normalized vertices linear G K hvertices
    (fun v hv i => (hinput v hv i).1) i).trans hr

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRawCost
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bit-operation bounds for the literal Boolean arithmetic calls and
bounded-width power loops used inside the entropy optimizer. -/

namespace EditApproximation
namespace BinaryFraction

theorem representation_storageBits_le (a : BinaryFraction) :
    a.representation.storageBits ≤ 2 * a.width + 1 := by
  have hn : Nat.size (bitWordValue a.numerator.bits) ≤ a.numerator.bits.length :=
    Nat.size_le.mpr (bitWordValue_lt_pow_length _)
  have hd : Nat.size (bitWordValue a.denominator) ≤ a.denominator.length :=
    Nat.size_le.mpr (bitWordValue_lt_pow_length _)
  have hmag : a.numerator.value.natAbs = bitWordValue a.numerator.bits := by
    cases h : a.numerator.negative <;> simp [SignedBinary.value, signedMagnitude, h]
  have hnw : a.numerator.bits.length ≤ a.width := le_max_left _ _
  have hdw : a.denominator.length ≤ a.width := le_max_right _ _
  simp only [representation, UnreducedRational.storageBits, hmag]
  omega

theorem representation_den_bits_le_width (a : BinaryFraction) :
    Nat.size a.representation.den ≤ a.width := by
  have hd : Nat.size (bitWordValue a.denominator) ≤ a.denominator.length :=
    Nat.size_le.mpr (bitWordValue_lt_pow_length _)
  exact hd.trans (le_max_right _ _)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLogWork
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bit cost of the finite logarithm series on unreduced Boolean fractions.
Every bound is for the executed power/division/addition loops. -/

namespace EditApproximation
namespace BinaryFraction

theorem divWithWork_self_width (a b : BinaryFraction) :
    (a.divWithWork b).1.width ≤ (a.divWithWork b).1.representation.storageBits :=
  canonicalMulWithWork_self_width _ _

theorem logarithmPartialBitStep_mono {A B : ℕ} (h : A ≤ B) (K : ℕ) :
    logarithmPartialBitStep A K ≤ logarithmPartialBitStep B K := by
  have h1 := Nat.mul_self_le_mul_self (show A + 1 ≤ B + 1 by omega)
  have h2 := Nat.mul_self_le_mul_self (show A + 2 ≤ B + 2 by omega)
  simp only [← pow_two] at h1 h2
  have hm := Nat.mul_le_mul_left (2 * K + 1)
    (show 2000 * (A + 1) ^ 2 + 1 ≤ 2000 * (B + 1) ^ 2 + 1 by omega)
  unfold logarithmPartialBitStep
  omega

theorem logarithmUniversalWordBudget_mono {A B : ℕ} (h : A ≤ B) (K : ℕ) :
    logarithmUniversalWordBudget A K ≤ logarithmUniversalWordBudget B K := by
  have hquad := Nat.mul_le_mul_left (K * K) h
  have hlin := Nat.mul_le_mul_left (2 * K + 1) h
  unfold logarithmUniversalWordBudget
  omega

theorem logarithmBitBudget_mono {A B : ℕ} (h : A ≤ B) (K : ℕ) :
    logarithmBitBudget A K ≤ logarithmBitBudget B K := by
  have hw := logarithmUniversalWordBudget_mono (show 8 * A + 22 ≤ 8 * B + 22 by omega) K
  have hs := Nat.mul_le_mul_left K (logarithmPartialBitStep_mono hw K)
  have h1 := Nat.mul_self_le_mul_self (show A + 4 ≤ B + 4 by omega)
  have h2 := Nat.mul_self_le_mul_self (show 4 * A + 12 ≤ 4 * B + 12 by omega)
  have h3 := Nat.mul_self_le_mul_self (show logarithmUniversalWordBudget (8 * A + 22) K + 5 ≤
      logarithmUniversalWordBudget (8 * B + 22) K + 5 by omega)
  simp only [← pow_two] at h1 h2 h3
  unfold logarithmBitBudget
  dsimp only
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGradientWork
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bit-operation bound for each actually materialized gradient coordinate. -/

namespace EditApproximation
namespace BinaryFraction

theorem gradientCellBitBudget_mono (G : ℕ) {A B C D : ℕ} (hpoint : A ≤ B) (hlinear : C ≤ D) :
    gradientCellBitBudget G A C ≤ gradientCellBitBudget G B D := by
  have hR : shiftedStorageBudget G A ≤ shiftedStorageBudget G B := by
    unfold shiftedStorageBudget
    omega
  have hL : gradientLogStorageBudget G A ≤ gradientLogStorageBudget G B :=
    UnreducedRational.logarithmStorageBudget_mono hR _
  have hc := logarithmBitBudget_mono hR (G ^ 60)
  have h1 := Nat.mul_self_le_mul_self
    (show A + smoothingStorageBudget G + 2 ≤ B + smoothingStorageBudget G + 2 by omega)
  have h2 := Nat.mul_self_le_mul_self
    (show gradientLogStorageBudget G A + 4 ≤ gradientLogStorageBudget G B + 4 by omega)
  have h3 := Nat.mul_self_le_mul_self
    (show C + 2 * gradientLogStorageBudget G A + 9 ≤ D + 2 * gradientLogStorageBudget G B + 9 by omega)
  simp only [← pow_two] at h1 h2 h3
  unfold gradientCellBitBudget
  dsimp only
  omega

theorem vectorMapWithWork_cost_le {α : Type*} (d : ℕ) (f : Fin d → α × ℕ)
    (C : ℕ) (hC : ∀ i, (f i).2 ≤ C) :
    (vectorMapWithWork d f).2 ≤ d * (C + 6) := by
  simp only [vectorMapWithWork, Vector.toList_map, Vector.toList_ofFn,
    List.map_ofFn, Function.comp_def, List.sum_ofFn]
  have hs : (∑ i : Fin d, (f i).2) ≤ d * C := by
    calc
      _ ≤ ∑ _ : Fin d, C := Finset.sum_le_sum (fun i _ => hC i)
      _ = d * C := by simp
  nlinarith only [hs]

theorem gradientWithWork_cost {d : ℕ} (G : ℕ) (linear point : Vector BinaryFraction d)
    (P L : ℕ) (hp : ∀ i, 0 ≤ (point.get i).value)
    (hpw : ∀ i, (point.get i).width ≤ P) (hlw : ∀ i, (linear.get i).width ≤ L) :
    (gradientWithWork G linear point).2 ≤ d * (gradientCellBitBudget G P L + 6) := by
  apply vectorMapWithWork_cost_le
  intro i
  exact (gradientCellWithWork_cost G linear point i (hp i)).trans
    (gradientCellBitBudget_mono G (hpw i) (hlw i))

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryOptimizerWork
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Total bit operations of the executed Boolean-fraction optimizer.
The bound includes logarithm sums, gradient materialization, scored vertex
search and every coordinate update, with no unit-cost rational primitive. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

theorem maximizerWithWork_mem {d : ℕ} (gradient : Vector BinaryFraction d)
    (vertices : List (Vector BinaryFraction d)) (hvertices : vertices ≠ []) :
    (maximizerWithWork gradient vertices).1 ∈ vertices := by
  unfold maximizerWithWork
  dsimp only
  rw [scoredArgmaxWithWork_value]
  cases h : vertices.argmax (fun vertex => (dotWithWork gradient vertex).1.value) with
  | none => exact False.elim (hvertices (List.argmax_eq_none.mp h))
  | some vertex =>
    simp only [Option.map_some, Option.getD_some]
    exact List.argmax_mem (by rw [h]; simp)

theorem gradientStorageBudget_mono (G : ℕ) {A B C D : ℕ}
    (hpoint : A ≤ B) (hlinear : C ≤ D) :
    UnreducedRational.gradientStorageBudget G A C ≤
      UnreducedRational.gradientStorageBudget G B D := by
  have hs := UnreducedRational.logarithmStorageBudget_mono
    (show 2 * A + 2 * (5 + 50 * (Nat.size G + 2)) + 2 ≤
      2 * B + 2 * (5 + 50 * (Nat.size G + 2)) + 2 by omega) (G ^ 60)
  unfold UnreducedRational.gradientStorageBudget
  omega

theorem gradientWithWork_width {d : ℕ} (G : ℕ) (linear point : Vector BinaryFraction d)
    (P L : ℕ) (hp : ∀ i, 0 ≤ (point.get i).value)
    (hpw : ∀ i, (point.get i).width ≤ P) (hlw : ∀ i, (linear.get i).width ≤ L) (i : Fin d) :
    ((gradientWithWork G linear point).1.get i).width ≤
      UnreducedRational.gradientStorageBudget G (2 * P + 1) (2 * L + 1) := by
  simp only [gradientWithWork, vectorMapWithWork_value]
  apply (gradientCellWithWork_width G linear point i (hp i)).trans
  apply gradientStorageBudget_mono
  · exact (representation_storageBits_le _).trans (by have h := hpw i; omega)
  · exact (representation_storageBits_le _).trans (by have h := hlw i; omega)

theorem gradientWithWork_abs {d : ℕ} (G V : ℕ) (linear point : Vector BinaryFraction d)
    (hp : ∀ i, 0 ≤ (point.get i).value)
    (hlv : ∀ i, |(linear.get i).value| ≤ V) (i : Fin d) :
    |((gradientWithWork G linear point).1.get i).value| ≤ (2 * G ^ 60 + 1 + V : ℕ) := by
  have hv := congrArg (fun v : Vector UnreducedRational d => (v.get i).value)
    (gradientWithWork_representation G linear point)
  simp only [vector_map_get, representation_value, UnreducedRational.gradient_value] at hv
  rw [hv]
  have hpos : 0 ≤ (point.get i).value + 1 / (G : ℚ) ^ 50 :=
    add_nonneg (hp i) (div_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg _) _))
  have hlog := rationalLogApproximation_abs_bound _ (G ^ 60) hpos
  unfold rationalSmoothedGradient
  calc
    _ ≤ |-rationalLogApproximation ((point.get i).value + 1 / (G : ℚ) ^ 50) (G ^ 60) - 1| +
      |(linear.get i).value| := abs_add_le _ _
    _ ≤ |rationalLogApproximation ((point.get i).value + 1 / (G : ℚ) ^ 50) (G ^ 60)| + 1 +
      |(linear.get i).value| := by
        have h := abs_add_le (-rationalLogApproximation
          ((point.get i).value + 1 / (G : ℚ) ^ 50) (G ^ 60)) (-1)
        exact add_le_add (by simpa only [sub_eq_add_neg, abs_neg, abs_one] using h) le_rfl
    _ ≤ 2 * (G ^ 60 : ℕ) + 1 + (V : ℚ) := add_le_add (add_le_add hlog le_rfl) (hlv i)
    _ = _ := by push_cast; rfl

theorem finiteOptimizerWithWork_cost {d : ℕ}
    (vertices : List (Vector BinaryFraction d)) (linear : Vector BinaryFraction d)
    (G K B Bv L V : ℕ) (hvertices : vertices ≠ [])
    (hinput : ∀ v ∈ vertices, ∀ i : Fin d,
      (v.get i).width ≤ (v.get i).representation.storageBits ∧
      (0 ≤ (v.get i).value ∧ (v.get i).value ≤ 1) ∧
      Nat.size (v.get i).representation.den ≤ B)
    (hvw : ∀ v ∈ vertices, ∀ i, (v.get i).width ≤ Bv)
    (hlw : ∀ i, (linear.get i).width ≤ L)
    (hlv : ∀ i, |(linear.get i).value| ≤ V) :
    (finiteOptimizerWithWork vertices linear G K).2 ≤
      optimizerBitBudget d vertices.length G K B Bv L V := by
  let P := optimizerPointWordBudget K B Bv
  let W := optimizerGradientWordBudget G K B Bv L
  have hpoint (j : ℕ) (hj : j ≤ K) (i : Fin d) :
      ((finiteOptimizerWithWork vertices linear G j).1.get i).width ≤ P := by
    have hw := finiteOptimizerWithWork_coordinate_width vertices linear G j B hvertices hinput i
    have hsize := Nat.size_le_size (show j + 1 ≤ K + 1 by omega)
    have hm := Nat.mul_le_mul hj
      (show 2 * Nat.size (j + 1) + B ≤ 2 * Nat.size (K + 1) + B by omega)
    dsimp only [P, optimizerPointWordBudget]
    omega
  have hpositive (j : ℕ) (i : Fin d) :
      0 ≤ ((finiteOptimizerWithWork vertices linear G j).1.get i).value := by
    have hn : (vertices.map fun v i => (v.get i).value) ≠ [] := by
      intro h
      exact hvertices (List.map_eq_nil_iff.mp h)
    have h := finiteRationalOptimizer_coordinate_bounds univ
      (vertices.map fun v i => (v.get i).value) (fun i => (linear.get i).value) G j hn i (by
        intro v hv
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
        exact (hinput w hw i).2.1)
    rw [← congrFun (finiteOptimizerWithWork_value vertices linear G j) i] at h
    exact h.1
  have hvert (v : Vector BinaryFraction d) (hv : v ∈ vertices) (i : Fin d) : (v.get i).width ≤ P := by
    have h := hvw v hv i
    dsimp only [P, optimizerPointWordBudget]
    omega
  have hvertexAbs (v : Vector BinaryFraction d) (hv : v ∈ vertices) (i : Fin d) :
      |(v.get i).value| ≤ (2 * G ^ 60 + 1 + V + 1 : ℕ) := by
    rw [abs_of_nonneg (hinput v hv i).2.1.1]
    exact (hinput v hv i).2.1.2.trans (by exact_mod_cast (show 1 ≤ 2 * G ^ 60 + 1 + V + 1 by omega))
  have hcost : ∀ j ≤ K, (finiteOptimizerWithWork vertices linear G j).2 ≤
      d + 1 + j * optimizerRoundBitBudget d vertices.length G K B Bv L V := by
    intro j
    induction j with
    | zero => intro _; simp only [finiteOptimizerWithWork, Nat.zero_mul, Nat.add_zero, le_refl]
    | succ j ih =>
      intro hj
      have hj' : j ≤ K := by omega
      have hcprev := ih hj'
      let previous := (finiteOptimizerWithWork vertices linear G j).1
      let grad := (gradientWithWork G linear previous).1
      let selected := (maximizerWithWork grad vertices).1
      have hcgrad := gradientWithWork_cost G linear previous P L
        (hpositive j) (hpoint j hj') hlw
      have hwgrad (i : Fin d) : (grad.get i).width ≤ W :=
        gradientWithWork_width G linear previous P L (hpositive j) (hpoint j hj') hlw i
      have hvgrad (i : Fin d) : |(grad.get i).value| ≤ (2 * G ^ 60 + 1 + V + 1 : ℕ) :=
        (gradientWithWork_abs G V linear previous (hpositive j) hlv i).trans (by exact_mod_cast Nat.le_add_right _ 1)
      have hcmax := maximizerWithWork_cost grad vertices (max P W) (2 * G ^ 60 + 1 + V + 1)
        (fun i => (hwgrad i).trans (Nat.le_max_right _ _)) hvgrad
        (fun v hv i => (hvert v hv i).trans (Nat.le_max_left _ _)) hvertexAbs
      have hcupdate := optimizerUpdateWithWork_cost j K P hj' previous selected
        (hpoint j hj') (fun i => hvert selected (maximizerWithWork_mem grad vertices hvertices) i)
      change (finiteOptimizerWithWork vertices linear G j).2 + (gradientWithWork G linear previous).2 +
        (maximizerWithWork grad vertices).2 + (optimizerUpdateWithWork j previous selected).2 + 3 ≤ _
      change _ ≤ d + 1 + (j + 1) *
        (d * (gradientCellBitBudget G P L + 6) +
          maximizerBitBudget d vertices.length (max P W) (2 * G ^ 60 + 1 + V + 1) +
          optimizerUpdateBitBudget d K P + 3)
      change (finiteOptimizerWithWork vertices linear G j).2 ≤ d + 1 + j *
        (d * (gradientCellBitBudget G P L + 6) +
          maximizerBitBudget d vertices.length (max P W) (2 * G ^ 60 + 1 + V + 1) +
          optimizerUpdateBitBudget d K P + 3) at hcprev
      rw [Nat.add_mul, Nat.one_mul]
      omega
  exact hcost K le_rfl

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryActionSelection
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The final Boolean maximization retains the actual action label. This
is the sampled atom of the optimizer, rather than its averaged vector. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

theorem scoredArgmaxWithWork_map_cost {α β : Type*} (mapping : α → β)
    (score : β → BinaryFraction × ℕ) (values : List α) :
    (scoredArgmaxWithWork (fun a => score (mapping a)) values).2 =
      (scoredArgmaxWithWork score (values.map mapping)).2 := by
  have h : (scoredArgmaxWithWork score (values.map mapping)).1 =
      (scoredArgmaxWithWork (fun a => score (mapping a)) values).1.map
        (fun result => (mapping result.1, result.2)) ∧
      (scoredArgmaxWithWork (fun a => score (mapping a)) values).2 =
        (scoredArgmaxWithWork score (values.map mapping)).2 := by
    induction values with
    | nil => exact ⟨rfl, rfl⟩
    | cons head tail ih =>
      simp only [List.map_cons, scoredArgmaxWithWork, ih.1, ← ih.2]
      cases htail : (scoredArgmaxWithWork (fun a => score (mapping a)) tail).1 with
      | none => exact ⟨rfl, rfl⟩
      | some best =>
        simp only [Option.map_some]
        split_ifs <;> simp
  exact h.2

theorem selectionWithWork_cost {α : Type*} {d : ℕ}
    (vertices : List (α × Vector BinaryFraction d)) (linear : Vector BinaryFraction d)
    (G K B Bv L V : ℕ) (hvertices : vertices ≠ [])
    (hinput : ∀ v ∈ vertices, ∀ i : Fin d,
      (v.2.get i).width ≤ (v.2.get i).representation.storageBits ∧
      (0 ≤ (v.2.get i).value ∧ (v.2.get i).value ≤ 1) ∧
      Nat.size (v.2.get i).representation.den ≤ B)
    (hvw : ∀ v ∈ vertices, ∀ i, (v.2.get i).width ≤ Bv)
    (hlw : ∀ i, (linear.get i).width ≤ L)
    (hlv : ∀ i, |(linear.get i).value| ≤ V) :
    (selectionWithWork vertices linear G K).2 ≤ selectionBitBudget d vertices.length G K B Bv L V := by
  let points := vertices.map Prod.snd
  let point := (finiteOptimizerWithWork points linear G K).1
  let grad := (gradientWithWork G linear point).1
  let P := optimizerPointWordBudget K B Bv
  let W := optimizerGradientWordBudget G K B Bv L
  have hpnonempty : points ≠ [] := by
    intro h
    exact hvertices (List.map_eq_nil_iff.mp h)
  have hpinput (v : Vector BinaryFraction d) (hv : v ∈ points) (i : Fin d) :
      (v.get i).width ≤ (v.get i).representation.storageBits ∧
      (0 ≤ (v.get i).value ∧ (v.get i).value ≤ 1) ∧ Nat.size (v.get i).representation.den ≤ B := by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    exact hinput a ha i
  have hpw (v : Vector BinaryFraction d) (hv : v ∈ points) (i : Fin d) : (v.get i).width ≤ Bv := by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    exact hvw a ha i
  have hpoint (i : Fin d) : (point.get i).width ≤ P := by
    have h := finiteOptimizerWithWork_coordinate_width points linear G K B hpnonempty hpinput i
    change (point.get i).width ≤ _ at h
    dsimp only [P, optimizerPointWordBudget]
    omega
  have hpositive (i : Fin d) : 0 ≤ (point.get i).value := by
    have hn : (points.map fun v i => (v.get i).value) ≠ [] := by
      intro h
      exact hpnonempty (List.map_eq_nil_iff.mp h)
    have h := finiteRationalOptimizer_coordinate_bounds univ
      (points.map fun v i => (v.get i).value) (fun i => (linear.get i).value) G K hn i (by
        intro v hv
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
        exact (hpinput w hw i).2.1)
    rw [← congrFun (finiteOptimizerWithWork_value points linear G K) i] at h
    exact h.1
  have hgw (i : Fin d) : (grad.get i).width ≤ W :=
    gradientWithWork_width G linear point P L hpositive hpoint hlw i
  have hgv (i : Fin d) : |(grad.get i).value| ≤ (2 * G ^ 60 + 1 + V + 1 : ℕ) :=
    (gradientWithWork_abs G V linear point hpositive hlv i).trans
      (by exact_mod_cast Nat.le_add_right (2 * G ^ 60 + 1 + V) 1)
  have hvP (v : Vector BinaryFraction d) (hv : v ∈ points) (i : Fin d) : (v.get i).width ≤ P := by
    have h := hpw v hv i
    dsimp only [P, optimizerPointWordBudget]
    omega
  have hvabs (v : Vector BinaryFraction d) (hv : v ∈ points) (i : Fin d) :
      |(v.get i).value| ≤ (2 * G ^ 60 + 1 + V + 1 : ℕ) := by
    rw [abs_of_nonneg (hpinput v hv i).2.1.1]
    exact (hpinput v hv i).2.1.2.trans (by exact_mod_cast
      (show 1 ≤ 2 * G ^ 60 + 1 + V + 1 by omega))
  have hiterate := finiteOptimizerWithWork_cost points linear G K B Bv L V hpnonempty hpinput hpw hlw hlv
  have hgradient := gradientWithWork_cost G linear point P L hpositive hpoint hlw
  have hselected := maximizerWithWork_cost grad points (max P W) (2 * G ^ 60 + 1 + V + 1)
    (fun i => (hgw i).trans (Nat.le_max_right _ _)) hgv
    (fun v hv i => (hvP v hv i).trans (Nat.le_max_left _ _)) hvabs
  rw [maximizerWithWork, ← scoredArgmaxWithWork_map_cost Prod.snd (dotWithWork grad) vertices] at hselected
  simp only [points, List.length_map] at hiterate hselected
  change (finiteOptimizerWithWork points linear G K).2 ≤ _ at hiterate
  change (finiteOptimizerWithWork points linear G K).2 + (gradientWithWork G linear point).2 +
    (scoredArgmaxWithWork (fun vertex => dotWithWork grad vertex.2) vertices).2 + 1 ≤ _
  change _ ≤ optimizerBitBudget d vertices.length G K B Bv L V +
    d * (gradientCellBitBudget G P L + 6) +
      maximizerBitBudget d vertices.length (max P W) (2 * G ^ 60 + 1 + V + 1)
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandNumericalBits
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The probability vectors actually stored for band actions have polynomial
encodings in the input child masses. No accuracy event is needed. -/

namespace EditApproximation

open Finset

theorem actionVector_zero_one {M : ℕ} {σ : Type*} [DecidableEq σ]
    (mass : Fin M → ℚ) (action : Fin M → σ) (coordinate : Fin M × σ)
    (hpos : ∀ i, 0 < mass i) :
    0 ≤ actionVector mass action coordinate ∧ actionVector mass action coordinate ≤ 1 := by
  have hsum : 0 < ∑ i, mass i :=
    (hpos coordinate.1).trans_le (Finset.single_le_sum (fun i _ => (hpos i).le) (mem_univ _))
  unfold actionVector
  split_ifs
  · exact ⟨(div_pos (hpos _) hsum).le,
      (div_le_one₀ hsum).2 (single_le_sum (fun i _ => (hpos i).le) (mem_univ _))⟩
  · norm_num

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandInputs
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Actual Boolean construction of the normalized band vertices.
The input masses are stored fractions; their sum and divisions use the
counted routines and no reduced-rational conversion is performed. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

theorem bandMassTotalWithWork_storage {M : ℕ} (mass : Vector BinaryFraction M)
    (B : ℕ) (hmass : ∀ i, (mass.get i).width ≤ B) :
    (bandMassTotalWithWork mass).1.representation.storageBits ≤ bandMassTotalStorageBudget M B := by
  have hvalue (i : Fin M) : |(mass.get i).value| ≤ ((2 ^ B : ℕ) : ℚ) := by
    have h := (value_abs_le_pow_width (mass.get i)).trans
      (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (hmass i))
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h
  have h := UnreducedRational.dotList_storageBits
    (mass.map representation) ((Vector.replicate M one).map representation)
    (List.finRange M) B 1 (2 ^ B) 1
    (by intro i _; simpa only [vector_map_get] using (representation_den_bits_le_width (mass.get i)).trans (hmass i))
    (by intro i _; simp [one_representation, UnreducedRational.one, UnreducedRational.ofRat])
    (by intro i _; simpa only [vector_map_get, representation_value] using hvalue i)
    (by intro i _; simp [one_representation])
  simp only [List.length_finRange, Nat.mul_one] at h
  have hsize := (natural_product_bit_length M (2 ^ B)).trans
    (Nat.add_le_add_left (by rw [Nat.size_pow] : Nat.size (2 ^ B) ≤ B + 1) M.size)
  rw [bandMassTotalWithWork, dotWithWork_representation]
  change (UnreducedRational.dotList (mass.map representation)
    ((Vector.replicate M one).map representation) (List.finRange M)).storageBits ≤ _
  unfold bandMassTotalStorageBudget
  omega

theorem bandCoordinateWithWork_value {M : ℕ} {σ : Type*} [DecidableEq σ]
    (mass : Vector BinaryFraction M) (action : Fin M → σ) (coordinate : Fin M × σ) :
    (bandCoordinateWithWork mass (bandMassTotalWithWork mass).1 action coordinate).1.value =
      actionVector (fun i => (mass.get i).value) action coordinate := by
  unfold bandCoordinateWithWork actionVector
  split_ifs
  · rw [← representation_value, divWithWork_representation,
      UnreducedRational.value_div, representation_value, representation_value,
      bandMassTotalWithWork_value]
  · simp [zero, value, SignedBinary.value, signedMagnitude, bitWordValue]

theorem bandCoordinateWithWork_bounds {M : ℕ} {σ : Type*} [DecidableEq σ]
    (mass : Vector BinaryFraction M) (action : Fin M → σ) (coordinate : Fin M × σ)
    (B : ℕ) (hmass : ∀ i, (mass.get i).width ≤ B) (hpos : ∀ i, 0 < (mass.get i).value) :
    let output := (bandCoordinateWithWork mass (bandMassTotalWithWork mass).1 action coordinate).1
    output.width ≤ output.representation.storageBits ∧
      (0 ≤ output.value ∧ output.value ≤ 1) ∧
      output.representation.storageBits ≤ bandVertexWordBudget M B := by
  dsimp only
  have hvalues := actionVector_zero_one (fun i => (mass.get i).value) action coordinate hpos
  rw [← bandCoordinateWithWork_value mass action coordinate] at hvalues
  refine ⟨?_, hvalues, ?_⟩
  · unfold bandCoordinateWithWork
    split_ifs
    · exact divWithWork_self_width _ _
    · exact zero_width_le_storageBits
  · have ht := bandMassTotalWithWork_storage mass B hmass
    have hm := representation_storageBits_le (mass.get coordinate.1)
    have hi := hmass coordinate.1
    unfold bandCoordinateWithWork
    split_ifs
    · rw [divWithWork_representation]
      have hd := UnreducedRational.storageBits_div (mass.get coordinate.1).representation
        (bandMassTotalWithWork mass).1.representation
      unfold bandVertexWordBudget
      omega
    · change UnreducedRational.zero.storageBits ≤ _
      rw [UnreducedRational.storageBits_zero]
      unfold bandVertexWordBudget
      omega

theorem bandVerticesWithWork_input_bounds {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (band : List (Fin M → σ)) (B : ℕ)
    (hmass : ∀ i, (mass.get i).width ≤ B) (hpos : ∀ i, 0 < (mass.get i).value)
    (v : Vector BinaryFraction d) (hv : v ∈ (bandVerticesWithWork coordinates mass band).1)
    (i : Fin d) :
    (v.get i).width ≤ (v.get i).representation.storageBits ∧
      (0 ≤ (v.get i).value ∧ (v.get i).value ≤ 1) ∧
      Nat.size (v.get i).representation.den ≤ bandVertexWordBudget M B ∧
      (v.get i).width ≤ bandVertexWordBudget M B := by
  simp only [bandVerticesWithWork, List.map_map, Function.comp_def] at hv
  obtain ⟨action, _, rfl⟩ := List.mem_map.mp hv
  simp only [vectorMapWithWork_value]
  have h := bandCoordinateWithWork_bounds mass action (coordinates.get i) B hmass hpos
  dsimp only at h
  refine ⟨h.1, h.2.1, ?_, h.1.trans h.2.2⟩
  apply le_trans ?_ h.2.2
  unfold UnreducedRational.storageBits
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_OnlineLinearBits
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite optimistic-history sum has polynomial encoding
length. Its normalized table entries are bounded by the fixed envelopes. -/

namespace EditApproximation

open Finset

theorem childGain_abs_le_one {β σ : Type*} (mass : β → ℚ) (table : ℕ → β × σ → ℚ)
    (s : ℕ) (i : β × σ) (hm : 0 < mass i.1)
    (ht : 0 ≤ table s i ∧ table s i ≤ mass i.1) : |childGain mass table s i| ≤ 1 := by
  rw [childGain, abs_div, abs_neg, abs_of_nonneg ht.1, abs_of_pos hm]
  exact (div_le_one₀ hm).mpr ht.2

theorem childDecrement_abs_le_one {β σ : Type*} (mass : β → ℚ) (table : ℕ → β × σ → ℚ)
    (s : ℕ) (i : β × σ) (hm : 0 < mass i.1)
    (ht : 0 ≤ table s i ∧ table s i ≤ mass i.1)
    (ht' : 0 ≤ table (s + 1) i ∧ table (s + 1) i ≤ mass i.1) :
    |childDecrement mass table s i| ≤ 1 := by
  rw [childDecrement, abs_div, abs_of_pos hm]
  apply (div_le_one₀ hm).mpr
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem rationalOnlineLinear_abs {β σ : Type*} (mass : β → ℚ)
    (table : ℕ → β × σ → ℚ) (eta kappa : ℚ) (t E : ℕ) (i : β × σ)
    (heta : |eta| ≤ E) (hmass : 0 < mass i.1) (hkappa : 0 ≤ kappa ∧ kappa ≤ 1)
    (htable : ∀ s ≤ t + 1, 0 ≤ table s i ∧ table s i ≤ mass i.1) :
    |rationalOnlineLinear eta kappa (childGain mass table) (childDecrement mass table) t i| ≤ E * (2 * t + 1) := by
  have hc : |1 - 2 * kappa| ≤ 1 := abs_le.mpr ⟨by linarith [hkappa.2], by linarith [hkappa.1]⟩
  have hterm (s : ℕ) (hs : s ∈ range t) :
      |childGain mass table s i + (1 - 2 * kappa) * childDecrement mass table s i| ≤ 2 := by
    have hs' := mem_range.mp hs
    have hg := childGain_abs_le_one mass table s i hmass (htable s (by omega))
    have hd := childDecrement_abs_le_one mass table s i hmass (htable s (by omega)) (htable (s + 1) (by omega))
    have hp := mul_le_mul hc hd (abs_nonneg _) (by norm_num : (0 : ℚ) ≤ 1)
    exact (abs_add_le _ _).trans (by rw [abs_mul]; linarith)
  have hsum : |rationalOptimisticHistory kappa (childGain mass table) (childDecrement mass table) t i| ≤ 2 * t := by
    unfold rationalOptimisticHistory
    calc
      _ ≤ ∑ s ∈ range t, |childGain mass table s i + (1 - 2 * kappa) * childDecrement mass table s i| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _s ∈ range t, (2 : ℚ) := sum_le_sum hterm
      _ = _ := by simp <;> ring
  have hg := childGain_abs_le_one mass table t i hmass (htable t (by omega))
  unfold rationalOnlineLinear
  rw [abs_mul]
  exact mul_le_mul heta ((abs_add_le _ _).trans (add_le_add hsum hg)) (abs_nonneg _) (Nat.cast_nonneg _)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryOnlineInputs
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The actual optimistic linear objective constructed from stored Boolean
fractions, using counted sums, products and divisions. No reduced-rational
conversion is used between the table inputs and the optimizer. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

@[simp] theorem gainWithWork_value {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (s : ℕ) (i : β × σ) :
    (gainWithWork mass table s i).1.value =
      childGain (fun j => (mass j).value) (fun t j => (table t j).value) s i := by
  simp only [gainWithWork, divWithWork_value, neg_value, childGain]

theorem onlineLinearWithWork_value {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (eta kappa : BinaryFraction)
    (t : ℕ) (i : β × σ) :
    (onlineLinearWithWork mass table eta kappa t i).1.value =
      rationalOnlineLinear eta.value kappa.value (childGain (fun j => (mass j).value)
        (fun s j => (table s j).value))
        (childDecrement (fun j => (mass j).value) (fun s j => (table s j).value)) t i := by
  simp only [onlineLinearWithWork, canonicalMulWithWork_value, canonicalAddWithWork_value,
    bandMassTotalWithWork_value, vectorMapWithWork_value, optimisticTermWithWork,
    coefficientWithWork_value, gainWithWork_value, decrementWithWork_value]
  unfold rationalOnlineLinear rationalOptimisticHistory
  congr 2
  exact Fin.sum_univ_eq_sum_range (fun s => childGain (fun j => (mass j).value)
    (fun s j => (table s j).value) s i + (1 - 2 * kappa.value) *
      childDecrement (fun j => (mass j).value) (fun s j => (table s j).value) s i) t

theorem gainWithWork_storage {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (s : ℕ) (i : β × σ) (Bm Bt : ℕ)
    (hm : (mass i.1).width ≤ Bm) (ht : (table s i).width ≤ Bt) :
    (gainWithWork mass table s i).1.representation.storageBits ≤ 2 * Bt + 2 * Bm + 4 := by
  have hm' := representation_storageBits_le (mass i.1)
  have ht' := representation_storageBits_le (table s i)
  change (divWithWork (table s i).neg (mass i.1)).1.representation.storageBits ≤ _
  rw [divWithWork_representation, neg_representation]
  have h := UnreducedRational.storageBits_div (table s i).representation.neg (mass i.1).representation
  rw [UnreducedRational.storageBits_neg] at h
  omega

theorem decrementWithWork_storage {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (s : ℕ) (i : β × σ) (Bm Bt : ℕ)
    (hm : (mass i.1).width ≤ Bm) (ht : (table s i).width ≤ Bt) (ht' : (table (s + 1) i).width ≤ Bt) :
    (decrementWithWork mass table s i).1.representation.storageBits ≤ 8 * Bt + 2 * Bm + 9 := by
  have hm' := representation_storageBits_le (mass i.1)
  have ho := representation_storageBits_le (table s i)
  have hn := representation_storageBits_le (table (s + 1) i)
  have hs := UnreducedRational.storageBits_sub (table s i).representation (table (s + 1) i).representation
  have hd := UnreducedRational.storageBits_div ((table s i).representation.sub (table (s + 1) i).representation) (mass i.1).representation
  change (divWithWork (subWithWork (table s i) (table (s + 1) i)).1 (mass i.1)).1.representation.storageBits ≤ _
  rw [divWithWork_representation, subWithWork_representation]
  omega

theorem coefficientWithWork_storage (kappa : BinaryFraction) (Bk : ℕ) (hk : kappa.width ≤ Bk) :
    (coefficientWithWork kappa).1.representation.storageBits ≤ 4 * Bk + 18 := by
  have hk' := representation_storageBits_le kappa
  have hm := UnreducedRational.storageBits_mul (UnreducedRational.nat 2) kappa.representation
  have hs := UnreducedRational.storageBits_sub UnreducedRational.one
    ((UnreducedRational.nat 2).mul kappa.representation)
  have htwo : (UnreducedRational.nat 2).storageBits = 4 := by decide
  rw [htwo] at hm
  rw [UnreducedRational.storageBits_one] at hs
  change (subWithWork one (canonicalMulWithWork (nat 2) kappa).1).1.representation.storageBits ≤ _
  rw [subWithWork_representation, one_representation, canonicalMulWithWork_representation, nat_representation]
  omega

theorem optimisticTermWithWork_storage {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (coefficient : BinaryFraction)
    (s : ℕ) (i : β × σ) (Bm Bt Bc : ℕ)
    (hm : (mass i.1).width ≤ Bm) (ht : (table s i).width ≤ Bt)
    (ht' : (table (s + 1) i).width ≤ Bt) (hc : coefficient.width ≤ Bc) :
    (optimisticTermWithWork mass table coefficient s i).1.representation.storageBits ≤
      optimisticTermStorageBudget Bm Bt Bc := by
  have hg := gainWithWork_storage mass table s i Bm Bt hm ht
  have hd := decrementWithWork_storage mass table s i Bm Bt hm ht ht'
  have hc' := representation_storageBits_le coefficient
  have hp := UnreducedRational.storageBits_mul coefficient.representation
    (decrementWithWork mass table s i).1.representation
  have ha := UnreducedRational.storageBits_add (gainWithWork mass table s i).1.representation
    (coefficient.representation.mul (decrementWithWork mass table s i).1.representation)
  change (canonicalAddWithWork (gainWithWork mass table s i).1
    (canonicalMulWithWork coefficient (decrementWithWork mass table s i).1).1).1.representation.storageBits ≤ _
  rw [canonicalAddWithWork_representation, canonicalMulWithWork_representation]
  unfold optimisticTermStorageBudget
  omega

theorem onlineLinearWithWork_storage {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (eta kappa : BinaryFraction)
    (t : ℕ) (i : β × σ) (Be Bk Bm Bt : ℕ)
    (he : eta.width ≤ Be) (hk : kappa.width ≤ Bk) (hm : (mass i.1).width ≤ Bm)
    (ht : ∀ s ≤ t + 1, (table s i).width ≤ Bt) :
    (onlineLinearWithWork mass table eta kappa t i).1.width ≤
      onlineLinearStorageBudget Be Bk Bm Bt t := by
  let coefficient := (coefficientWithWork kappa).1
  let terms := (vectorMapWithWork t fun s => optimisticTermWithWork mass table coefficient s.val i).1
  let history := (bandMassTotalWithWork terms).1
  let current := (gainWithWork mass table t i).1
  have hcn := canonicalAddWithWork_self_width one (canonicalMulWithWork (nat 2) kappa).1.neg
  change coefficient.width ≤ coefficient.representation.storageBits at hcn
  have hc : coefficient.width ≤ 4 * Bk + 18 := hcn.trans (coefficientWithWork_storage kappa Bk hk)
  have hterms (s : Fin t) : (terms.get s).width ≤ optimisticTermStorageBudget Bm Bt (4 * Bk + 18) := by
    have hs := optimisticTermWithWork_storage mass table coefficient s.val i Bm Bt (4 * Bk + 18)
      hm (ht s.val (by omega)) (ht (s.val + 1) (by omega)) hc
    simp only [terms, vectorMapWithWork_value]
    exact (canonicalAddWithWork_self_width _ _).trans hs
  have hh := bandMassTotalWithWork_storage terms (optimisticTermStorageBudget Bm Bt (4 * Bk + 18)) hterms
  change history.representation.storageBits ≤ _ at hh
  have hg := gainWithWork_storage mass table t i Bm Bt hm (ht t (by omega))
  change current.representation.storageBits ≤ _ at hg
  have he' := representation_storageBits_le eta
  have ha := UnreducedRational.storageBits_add history.representation current.representation
  have hp := UnreducedRational.storageBits_mul eta.representation (history.representation.add current.representation)
  change (canonicalMulWithWork eta (canonicalAddWithWork history current).1).1.width ≤ _
  have hw := canonicalMulWithWork_self_width eta (canonicalAddWithWork history current).1
  rw [canonicalMulWithWork_representation, canonicalAddWithWork_representation] at hw
  unfold onlineLinearStorageBudget
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandAction
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Materialized Boolean vertices retain their band labels. The resulting
selected action, including every tie, is the action used by the online
sampler in the accuracy development. -/

namespace EditApproximation
namespace BinaryFraction

theorem labeledBandVerticesWithWork_vectors {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (band : List (Fin M → σ)) :
    (labeledBandVerticesWithWork coordinates mass band).1.map Prod.snd =
      (bandVerticesWithWork coordinates mass band).1 := by
  simp only [labeledBandVerticesWithWork, bandVerticesWithWork, List.map_map, Function.comp_def]

theorem labeledBandVerticesWithWork_cost {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (band : List (Fin M → σ)) :
    (labeledBandVerticesWithWork coordinates mass band).2 =
      (bandVerticesWithWork coordinates mass band).2 + 2 * band.length := by
  simp only [labeledBandVerticesWithWork, bandVerticesWithWork, List.map_map, Function.comp_def]
  omega

theorem preparedBandActionWithWork_cost_oai {M : ℕ} {σ : Type*} [DecidableEq σ]
    (mass : Vector BinaryFraction M) (table : ℕ → Fin M × σ → BinaryFraction)
    (eta kappa : BinaryFraction) (band : List (Fin M → σ)) (G K t Be Bk Bm Bt E : ℕ)
    (hband : band ≠ []) (he : eta.width ≤ Be) (hk : kappa.width ≤ Bk)
    (hm : ∀ j, (mass.get j).width ≤ Bm) (hmpos : ∀ j, 0 < (mass.get j).value)
    (ht : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (table s ((listedBandCoordinateVector band).get i)).width ≤ Bt)
    (heabs : |eta.value| ≤ E) (hkrange : 0 ≤ kappa.value ∧ kappa.value ≤ 1)
    (htrange : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      0 ≤ (table s ((listedBandCoordinateVector band).get i)).value ∧
        (table s ((listedBandCoordinateVector band).get i)).value ≤
          (mass.get ((listedBandCoordinateVector band).get i).1).value) :
    (preparedBandActionWithWork mass table eta kappa band G K t).2 ≤
      preparedBandActionBitBudget M (listedBandCoordinates band).length band.length G K t Be Bk Bm Bt E := by
  let coordinates := listedBandCoordinateVector band
  let vertices := (labeledBandVerticesWithWork coordinates mass band).1
  let linear := (vectorMapWithWork _ fun i =>
    onlineLinearWithWork (fun j => mass.get j) table eta kappa t (coordinates.get i)).1
  have hlength : vertices.length = band.length := by
    simp only [vertices, labeledBandVerticesWithWork, List.length_map]
  have hvertices : vertices ≠ [] := by
    intro h
    rw [h, List.length_nil] at hlength
    exact hband (List.length_eq_zero_iff.mp hlength.symm)
  have hv (v : (Fin M → σ) × Vector BinaryFraction (listedBandCoordinates band).length)
      (hmem : v ∈ vertices) (i : Fin (listedBandCoordinates band).length) :=
    bandVerticesWithWork_input_bounds coordinates mass band Bm hm hmpos v.2
      (by rw [← labeledBandVerticesWithWork_vectors]
          exact List.mem_map.mpr ⟨v, hmem, rfl⟩) i
  have hlwidth (i : Fin (listedBandCoordinates band).length) :
      (linear.get i).width ≤ onlineLinearStorageBudget Be Bk Bm Bt t := by
    simp only [linear, vectorMapWithWork_value]
    exact onlineLinearWithWork_storage (fun j => mass.get j) table eta kappa t
      (coordinates.get i) Be Bk Bm Bt he hk (hm _) (fun s hs => ht s hs i)
  have hlvalue (i : Fin (listedBandCoordinates band).length) :
      |(linear.get i).value| ≤ (E * (2 * t + 1) : ℕ) := by
    simp only [linear, vectorMapWithWork_value, onlineLinearWithWork_value]
    have h := rationalOnlineLinear_abs (fun j => (mass.get j).value)
      (fun s j => (table s j).value) eta.value kappa.value t E (coordinates.get i)
      heabs (hmpos _) hkrange (fun s hs => htrange s hs i)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using h
  have hc := selectionWithWork_cost vertices linear G K (bandVertexWordBudget M Bm)
    (bandVertexWordBudget M Bm) (onlineLinearStorageBudget Be Bk Bm Bt t) (E * (2 * t + 1))
    hvertices (fun v hv' i => ⟨(hv v hv' i).1, (hv v hv' i).2.1, (hv v hv' i).2.2.1⟩)
    (fun v hv' i => (hv v hv' i).2.2.2) hlwidth hlvalue
  rw [hlength] at hc
  have hp := bandVerticesWithWork_cost coordinates mass band Bm hm
  have hl := vectorMapWithWork_cost_le _
    (fun i => onlineLinearWithWork (fun j => mass.get j) table eta kappa t (coordinates.get i))
    (onlineLinearBitBudget Be Bk Bm Bt t) (fun i => onlineLinearWithWork_cost
      (fun j => mass.get j) table eta kappa t (coordinates.get i) Be Bk Bm Bt
      he hk (hm _) (fun s hs => ht s hs i))
  change (labeledBandVerticesWithWork coordinates mass band).2 +
    (vectorMapWithWork _ (fun i => onlineLinearWithWork (fun j => mass.get j)
      table eta kappa t (coordinates.get i))).2 +
    (selectionWithWork vertices linear G K).2 + 2 ≤ _
  rw [labeledBandVerticesWithWork_cost]
  unfold preparedBandActionBitBudget
  omega

end BinaryFraction
end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.BinaryFraction.preparedBandActionWithWork_cost_oai.{u_1} := @OAI.EditApproximation.BinaryFraction.preparedBandActionWithWork_cost_oai.{u_1}
