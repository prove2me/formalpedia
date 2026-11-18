-- Prove2me | solution 1 for OAI.EditApproximation.integerStoredDataSpace_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:22:27.449094+00:00
-- url     : https://prove2.me/submissions/6fc9a10f-59b6-4970-b51e-37a9adbeb42c

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Nat
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_OAIQ361V3Ea002

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryMemo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A finite binary dictionary for gathered and globally memoized inputs.
Each recursive step reads one key bit and touches one node. The explicit
counters charge pointer/node operations; multiword key/value processing
is accounted for separately by their bit lengths. -/

namespace EditApproximation



namespace BinaryMemo

variable {α : Type*}











theorem lookup_insert_other (tree : BinaryMemo α) (key query : List Bool) (a : α)
    (hne : query ≠ key) : (tree.insert key a).lookup query = tree.lookup query := by
  induction key generalizing tree query with
  | nil =>
    cases query with
    | nil => exact False.elim (hne rfl)
    | cons b rest => cases b <;> rfl
  | cons b rest ih =>
    cases query with
    | nil => cases b <;> rfl
    | cons c tail =>
      cases b <;> cases c
      · exact ih tree.left tail (fun h => hne (congrArg (List.cons false) h))
      · rfl
      · rfl
      · exact ih tree.right tail (fun h => hne (congrArg (List.cons true) h))

theorem child_nodes (tree : BinaryMemo α) :
    tree.left.nodes + tree.right.nodes ≤ tree.nodes := by
  cases tree <;> simp only [left, right, nodes] <;> omega

theorem insert_nodes (tree : BinaryMemo α) (key : List Bool) (a : α) :
    (tree.insert key a).nodes ≤ tree.nodes + key.length + 1 := by
  induction key generalizing tree with
  | nil =>
    have h := child_nodes tree
    simp only [insert, nodes, List.length_nil]
    omega
  | cons b rest ih =>
    have h := child_nodes tree
    cases b
    · have hi := ih tree.left
      simp only [insert, nodes, List.length_cons]
      omega
    · have hi := ih tree.right
      simp only [insert, nodes, List.length_cons]
      omega

end BinaryMemo

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerSymbols
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Integer word labels are encoded injectively using a sign bit. The
encoding preserves the actual unit-cost edit distance and takes one
linear pass; no constant-alphabet hypothesis is used. -/

namespace EditApproximation



theorem integerSymbolCode_bound (z : ℤ) : integerSymbolCode z ≤ 2 * z.natAbs := by
  cases z <;> simp only [integerSymbolCode, Int.natAbs] <;> omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_OccurrencePrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Cached binary position counts. Inserting a position and counting positions
strictly below a boundary both follow one root-to-leaf path. Counts are stored
at internal nodes, so a prefixCount query does not traverse a whole interval. -/

namespace EditApproximation



namespace PositionCounts









theorem children_nodes (tree : PositionCounts) :
    tree.left.nodes + tree.right.nodes ≤ tree.nodes := by
  cases tree <;> simp only [left, right, nodes] <;> omega

theorem add_nodes (tree : PositionCounts) (d i : ℕ) :
    (tree.add d i).nodes ≤ tree.nodes + d + 1 := by
  induction d generalizing tree i with
  | zero =>
    have h := children_nodes tree
    simp only [add, nodes]
    omega
  | succ d ih =>
    have h := children_nodes tree
    simp only [add]
    split_ifs
    · have hrec := ih tree.left i
      simp only [nodes]
      omega
    · have hrec := ih tree.right (i - 2 ^ d)
      simp only [nodes]
      omega

end PositionCounts

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Parameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
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
















theorem inputHeight_covers_length (N : ℕ) : N + 2 ≤ 2 ^ inputHeight N := by
  have hlog := Nat.le_pow_clog (by decide : 1 < 2) (N + 2)
  have hheight := Nat.le_pow_clog (by decide : 1 < 2) (Nat.clog 2 (N + 2))
  exact hlog.trans (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hheight)

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

theorem natural_power_bit_length (a n : ℕ) :
    Nat.size (a ^ n) ≤ n * Nat.size a + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hmul := natural_product_bit_length (a ^ n) a
    nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerOccurrenceIndex
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Uniform input preparation chooses dictionary widths from the actual
integer words. No alphabet size or polynomial exponent is an algorithm input. -/

namespace EditApproximation



theorem integerMagnitude_mem (zs : List ℤ) (z : ℤ) (hz : z ∈ zs) :
    z.natAbs ≤ integerMagnitude zs := by
  induction zs with
  | nil => simp at hz
  | cons a zs ih =>
    rcases List.mem_cons.mp hz with rfl | hz
    · exact le_max_left _ _
    · exact (ih hz).trans (le_max_right _ _)

theorem integerMagnitude_le (zs : List ℤ) (B : ℕ) (h : ∀ z ∈ zs, z.natAbs ≤ B) :
    integerMagnitude zs ≤ B := by
  induction zs with
  | nil => exact Nat.zero_le _
  | cons z zs ih =>
    exact max_le (h z List.mem_cons_self) (ih fun a ha => h a (List.mem_cons_of_mem _ ha))





theorem integerInputSymbolBits_fits (source target : List ℤ) (z : ℤ)
    (hz : z ∈ source ++ target) :
    integerSymbolCode z < 2 ^ integerInputSymbolBits source target := by
  exact ((integerSymbolCode_bound z).trans
    (Nat.mul_le_mul_left 2 (integerMagnitude_mem _ z hz))).trans_lt (Nat.lt_size_self _)

theorem integerInputSymbolBits_le (source target : List ℤ) (B : ℕ)
    (h : ∀ z ∈ source ++ target, z.natAbs ≤ B) :
    integerInputSymbolBits source target ≤ Nat.size (2 * B) :=
  Nat.size_le_size (Nat.mul_le_mul_left 2 (integerMagnitude_le _ B h))



/-- Polynomially bounded input words produce logarithmic dictionary keys;
the polynomial degree is only an analysis parameter. -/
theorem integerInputSymbolBits_polynomial (source target : List ℤ) (N C : ℕ)
    (h : ∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) :
    integerInputSymbolBits source target ≤ C * Nat.size (N + 2) + 3 := by
  have hbits := integerInputSymbolBits_le source target ((N + 2) ^ C) h
  have hmul := natural_product_bit_length 2 ((N + 2) ^ C)
  have hpow := natural_power_bit_length (N + 2) C
  have htwo : Nat.size 2 = 2 := by decide
  omega

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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterLocalAsymptotics
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar bounds for the local enumeration exponent. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem inputHeight_real_tendsto :
    Tendsto (fun N => (inputHeight N : ℝ)) atTop atTop := by
  simpa only [inputHeight, Nat.cast_pow, Nat.cast_ofNat, Function.comp_def] using
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp heightExponent_tendsto

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerPreprocessing
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open Filter
open scoped Topology



/-- Scans, integer encoding, indexed occurrence preprocessing and the
exact equality guard are charged before the local evaluator starts. -/


 theorem input_length_bits_le (N : ℕ) : Nat.size (N + 2) ≤ inputHeight N + 1 := by
  apply Nat.size_le.mpr
  exact (inputHeight_covers_length N).trans_lt
    (Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self _))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerCoarseSymbolBits
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter

theorem integer_encoded_symbol_bits (C : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℤ,
      (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
      ∀ a ∈ source.map integerSymbolCode ++ target.map integerSymbolCode,
        Nat.size a ≤ inputHeight N ^ 3 := by
  filter_upwards [inputHeight_real_tendsto.eventually
    (eventually_ge_atTop ((max 100 C : ℕ) : ℝ))] with N hH
  have hH' : max 100 C ≤ inputHeight N := by exact_mod_cast hH
  intro source target halphabet a ha
  rw [← List.map_append] at ha
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
  have hcode : Nat.size (integerSymbolCode z) ≤ integerInputSymbolBits source target :=
    Nat.size_le.mpr (integerInputSymbolBits_fits source target z hz)
  have hs := integerInputSymbolBits_polynomial source target N C halphabet
  have hn := input_length_bits_le N
  have hCH := Nat.mul_le_mul (show C ≤ inputHeight N by omega) hn
  have hcube : 100 * inputHeight N ^ 2 ≤ inputHeight N ^ 3 := by
    have hm := Nat.mul_le_mul_right (inputHeight N ^ 2) (show 100 ≤ inputHeight N by omega)
    nlinarith only [hm]
  have h100 : 100 ≤ inputHeight N := by omega
  nlinarith only [hcode, hs, hCH, hcube, h100]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RankedMemoStorage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every value retained by the actual binary dictionary obeys the
semantic value bound. This includes every allocated path, not only keys
queried after the computation. -/

namespace EditApproximation
namespace BinaryMemo

theorem allValues_empty {α : Type*} (P : α → Prop) : AllValues P (.empty : BinaryMemo α) := by
  intro key value h
  rw [lookup_empty] at h
  cases h

theorem AllValues.insert {α : Type*} {P : α → Prop} {memory : BinaryMemo α}
    (hmem : AllValues P memory) (key : List Bool) (a : α) (ha : P a) :
    AllValues P (memory.insert key a) := by
  intro query value hvalue
  by_cases heq : query = key
  · subst query
    rw [lookup_insert_same] at hvalue
    cases hvalue
    exact ha
  · rw [lookup_insert_other memory key query a heq] at hvalue
    exact hmem query value hvalue

end BinaryMemo

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedRequestSpace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial retained-cache bound for every execution. The estimate
uses only fixed-width key insertion and computed parameter sizes, and
therefore does not depend on an approximation success event. -/

namespace EditApproximation

theorem two_pow_inputHeight_le (N : ℕ) : 2 ^ inputHeight N ≤ 4 * (N + 2) ^ 2 := by
  have hc : 0 < Nat.clog 2 (N + 2) :=
    Nat.clog_pos (by decide : 1 < (2 : ℕ)) (by omega)
  have hH := (rejectionWord_range (Nat.clog 2 (N + 2)) hc).2
  have hN := (rejectionWord_range (N + 2) (by omega)).2
  change inputHeight N < 2 * Nat.clog 2 (N + 2) at hH
  change 2 ^ Nat.clog 2 (N + 2) < 2 * (N + 2) at hN
  calc
    _ ≤ 2 ^ (2 * Nat.clog 2 (N + 2)) := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hH.le
    _ = (2 ^ Nat.clog 2 (N + 2)) ^ 2 := by rw [← pow_mul]; congr 1; omega
    _ ≤ (2 * (N + 2)) ^ 2 := Nat.pow_le_pow_left hN.le 2
    _ = _ := by ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedRetainedValues
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

 theorem computed_height_polynomial (N : ℕ) : inputHeight N ≤ (N + 2) ^ 4 := by
  have h4 : 4 ≤ (N + 2) ^ 2 := by nlinarith only [Nat.zero_le N]
  calc
    _ ≤ 2 ^ inputHeight N := Nat.lt_two_pow_self.le
    _ ≤ 4 * (N + 2) ^ 2 := two_pow_inputHeight_le N
    _ ≤ (N + 2) ^ 2 * (N + 2) ^ 2 := Nat.mul_le_mul_right _ h4
    _ = _ := by rw [← pow_add]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseInputStorage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation



theorem storedNaturalBits_le (values : List ℕ) (A : ℕ)
    (h : ∀ a ∈ values, Nat.size a ≤ A) :
    storedNaturalBits values ≤ 1 + values.length * (A + 1) := by
  have hs : (values.map fun a => Nat.size a + 1).sum ≤ values.length * (A + 1) := by
    induction values with
    | nil => simp
    | cons a values ih =>
      have ha := h a List.mem_cons_self
      have ht := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  exact Nat.add_le_add_left hs 1



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerInputStorage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open Filter

/-- A sign field, magnitude bits and one pointer/header word per input symbol. -/


theorem storedIntegerBits_le (values : List ℤ) (A : ℕ)
    (h : ∀ z ∈ values, z.natAbs ≤ A) :
    storedIntegerBits values ≤ 1 + values.length * (A + 2) := by
  have hs : (values.map fun z => Nat.size z.natAbs + 2).sum ≤ values.length * (A + 2) := by
    induction values with
    | nil => simp
    | cons z values ih =>
      have hz : Nat.size z.natAbs ≤ A :=
        (Nat.size_le.mpr z.natAbs.lt_two_pow_self).trans (h z List.mem_cons_self)
      have ht := ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  exact Nat.add_le_add_left hs 1

private theorem pair_storage_power (X C nx ny sx sy : ℕ) (hX : 2 ≤ X)
    (hn : nx + ny ≤ X) (hs : sx ≤ 1 + nx * (X ^ C + 2))
    (ht : sy ≤ 1 + ny * (X ^ C + 2)) : sx + sy ≤ X ^ (C + 3) := by
  have hp : 1 ≤ X ^ C := one_le_pow₀ (by omega)
  have hc : 4 ≤ X ^ 2 := by nlinarith only [hX]
  calc
    _ ≤ 2 + (nx + ny) * (X ^ C + 2) := by nlinarith only [hs, ht]
    _ ≤ 4 * X * X ^ C := by
      have hm := Nat.mul_le_mul_right (X ^ C + 2) hn
      nlinarith only [hm, hX, Nat.mul_le_mul_left X hp]
    _ ≤ X ^ 2 * X * X ^ C := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right X hc)
    _ = X ^ (C + 3) := by rw [pow_add]; ring

theorem storedIntegerInput_polynomial (source target : List ℤ) (N C : ℕ)
    (hsize : source.length + target.length ≤ N)
    (hsymbol : ∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) :
    storedIntegerBits source + storedIntegerBits target ≤ (N + 2) ^ (C + 3) := by
  exact pair_storage_power (N + 2) C source.length target.length
    (storedIntegerBits source) (storedIntegerBits target) (by omega) (by omega)
    (storedIntegerBits_le source _ (fun z hz => hsymbol z (List.mem_append_left _ hz)))
    (storedIntegerBits_le target _ (fun z hz => hsymbol z (List.mem_append_right _ hz)))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_OccurrenceStorage
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryMemo.mapValues_lookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
namespace PositionCounts

theorem CountsLE.mono {C D : ℕ} (hCD : C ≤ D) {tree : PositionCounts}
    (h : tree.CountsLE C) : tree.CountsLE D := by
  induction tree with
  | empty => trivial
  | node n l r ihl ihr => exact ⟨h.1.trans hCD, ihl h.2.1, ihr h.2.2⟩

theorem CountsLE.count {C : ℕ} {tree : PositionCounts} (h : tree.CountsLE C) :
    tree.count ≤ C := by
  cases tree with
  | empty => exact Nat.zero_le _
  | node n l r => exact h.1

theorem CountsLE.left {C : ℕ} {tree : PositionCounts} (h : tree.CountsLE C) :
    tree.left.CountsLE C := by
  cases tree with
  | empty => trivial
  | node n l r => exact h.2.1

theorem CountsLE.right {C : ℕ} {tree : PositionCounts} (h : tree.CountsLE C) :
    tree.right.CountsLE C := by
  cases tree with
  | empty => trivial
  | node n l r => exact h.2.2

theorem CountsLE.add {C : ℕ} {tree : PositionCounts} (h : tree.CountsLE C) (d i : ℕ) :
    (tree.add d i).CountsLE (C + 1) := by
  induction d generalizing tree i with
  | zero => exact ⟨Nat.add_le_add_right h.count 1,
      h.left.mono (Nat.le_succ _), h.right.mono (Nat.le_succ _)⟩
  | succ d ih =>
    simp only [PositionCounts.add]
    split
    · exact ⟨Nat.add_le_add_right h.count 1, ih h.left _, h.right.mono (Nat.le_succ _)⟩
    · exact ⟨Nat.add_le_add_right h.count 1, h.left.mono (Nat.le_succ _), ih h.right _⟩

/-- A tag, two child pointers, and the binary counter at each allocated node. -/


theorem storageBits_le {tree : PositionCounts} {C : ℕ} (h : tree.CountsLE C) :
    tree.storageBits ≤ (Nat.size C + 3) * tree.nodes := by
  induction tree with
  | empty => simp only [storageBits, nodes, Nat.mul_zero, le_refl]
  | node n l r ihl ihr =>
    have hn := Nat.size_le_size h.1
    have hl := ihl h.2.1
    have hr := ihr h.2.2
    simp only [storageBits, nodes]
    nlinarith only [hn, hl, hr]

end PositionCounts
namespace BinaryMemo

/-- Concrete trie storage with the supplied stored-value representation. -/


theorem valueStorage_le {α : Type*} (bits : α → ℕ) (W : ℕ) (memory : BinaryMemo α)
    (h : AllValues (fun a => bits a ≤ W) memory) :
    valueStorage bits memory ≤ (W + 3) * memory.nodes := by
  induction memory with
  | empty => simp only [valueStorage, nodes, Nat.mul_zero, le_refl]
  | node value l r ihl ihr =>
    have hl : AllValues (fun a => bits a ≤ W) l := fun key a ha => h (false :: key) a ha
    have hr : AllValues (fun a => bits a ≤ W) r := fun key a ha => h (true :: key) a ha
    have hv : (value.map bits).getD 0 ≤ W := by
      cases value with
      | none => exact Nat.zero_le _
      | some a => exact h [] a rfl
    have hls := ihl hl
    have hrs := ihr hr
    simp only [valueStorage, nodes]
    nlinarith only [hv, hls, hrs]

end BinaryMemo

theorem occurrenceBuild_nodes (s p : ℕ) (entries : List (ℕ × ℕ)) :
    (occurrenceBuild s p entries).nodes ≤ entries.length * (s + 1) := by
  induction entries with
  | nil => simp only [occurrenceBuild, BinaryMemo.nodes, List.length_nil, Nat.zero_mul, le_refl]
  | cons e es ih =>
    have h := BinaryMemo.insert_nodes (occurrenceBuild s p es) (binaryMemoKey s e.1)
      (((occurrenceBuild s p es).lookup (binaryMemoKey s e.1)).getD .empty |>.add p e.2)
    simp only [binaryMemoKey_length] at h
    simp only [occurrenceBuild, List.length_cons]
    nlinarith only [h, ih]

theorem occurrenceBuild_values (s p : ℕ) (entries : List (ℕ × ℕ)) :
    BinaryMemo.AllValues (fun tree : PositionCounts =>
      tree.CountsLE entries.length ∧ tree.nodes ≤ entries.length * (p + 1))
      (occurrenceBuild s p entries) := by
  induction entries with
  | nil => exact BinaryMemo.allValues_empty _
  | cons e es ih =>
    have hold : let tree := ((occurrenceBuild s p es).lookup (binaryMemoKey s e.1)).getD .empty
        tree.CountsLE es.length ∧ tree.nodes ≤ es.length * (p + 1) := by
      cases hfind : (occurrenceBuild s p es).lookup (binaryMemoKey s e.1) with
      | none => simp only [Option.getD_none, PositionCounts.CountsLE, PositionCounts.nodes]; exact ⟨trivial, Nat.zero_le _⟩
      | some tree => exact ih _ _ hfind
    apply BinaryMemo.AllValues.insert
    · intro key tree htree
      obtain ⟨hc, hn⟩ := ih key tree htree
      exact ⟨hc.mono (by simp), hn.trans (Nat.mul_le_mul_right _ (by simp))⟩
    · refine ⟨hold.1.add p e.2, ?_⟩
      have hn := PositionCounts.add_nodes
        (((occurrenceBuild s p es).lookup (binaryMemoKey s e.1)).getD .empty) p e.2
      have ho := hold.2
      simp only [List.length_cons]
      nlinarith only [hn, ho]

theorem occurrenceBuild_storage (s p : ℕ) (entries : List (ℕ × ℕ)) :
    BinaryMemo.valueStorage PositionCounts.storageBits (occurrenceBuild s p entries) ≤
      ((Nat.size entries.length + 3) * (entries.length * (p + 1)) + 3) *
        (entries.length * (s + 1)) := by
  have hv := occurrenceBuild_values s p entries
  apply (BinaryMemo.valueStorage_le _ _ _ (fun key tree htree =>
    (PositionCounts.storageBits_le (hv key tree htree).1).trans
      (Nat.mul_le_mul_left _ (hv key tree htree).2))).trans
  exact Nat.mul_le_mul_left _ (occurrenceBuild_nodes s p entries)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerOccurrenceStorage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open Filter

/-- Actual counters and trie nodes of the encoded target occurrence index. -/


theorem integerOccurrenceStorage_bound (source target : List ℤ) (N C : ℕ)
    (hsize : source.length + target.length ≤ N)
    (hsymbol : ∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) :
    integerOccurrenceStorage source target ≤ 9 * (C + 2) * (N + 2) ^ 5 := by
  have h := occurrenceBuild_storage (integerInputSymbolBits source target)
    (integerInputPositionBits target) ((target.map integerSymbolCode).zipIdx)
  simp only [List.length_zipIdx, List.length_map] at h
  change integerOccurrenceStorage source target ≤ _ at h
  let X := N + 2
  have hX : 2 ≤ X := by dsimp only [X]; omega
  have hn : target.length ≤ X := by dsimp only [X]; omega
  have hsz : Nat.size target.length ≤ X :=
    (Nat.size_le_size hn).trans (Nat.size_le.mpr X.lt_two_pow_self)
  have hp : integerInputPositionBits target + 1 ≤ 2 * X := by
    change Nat.size target.length + 1 ≤ 2 * X
    omega
  have hs : integerInputSymbolBits source target + 1 ≤ (C + 2) * X := by
    have hs := integerInputSymbolBits_polynomial source target N C hsymbol
    have hb : Nat.size (N + 2) ≤ X := Nat.size_le.mpr X.lt_two_pow_self
    nlinarith only [hs, hb, hX]
  have hcounter : Nat.size target.length + 3 ≤ 3 * X := by omega
  have hpos := Nat.mul_le_mul hn hp
  have htree := Nat.mul_le_mul hcounter hpos
  have hdict := Nat.mul_le_mul hn hs
  have hunit : 1 ≤ X ^ 3 := one_le_pow₀ (by omega)
  have hv : (Nat.size target.length + 3) * (target.length *
      (integerInputPositionBits target + 1)) + 3 ≤ 9 * X ^ 3 := by
    nlinarith only [htree, hunit]
  calc
    _ ≤ ((Nat.size target.length + 3) * (target.length *
        (integerInputPositionBits target + 1)) + 3) *
        (target.length * (integerInputSymbolBits source target + 1)) := h
    _ ≤ (9 * X ^ 3) * (X * ((C + 2) * X)) := Nat.mul_le_mul hv hdict
    _ = _ := by ring

theorem integerOccurrenceStorage_polynomial (C : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℤ,
      source.length + target.length ≤ N →
      (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
      integerOccurrenceStorage source target ≤ (N + 2) ^ 6 := by
  filter_upwards [eventually_ge_atTop (9 * (C + 2))] with N hN
  intro source target hsize hsymbol
  calc
    _ ≤ 9 * (C + 2) * (N + 2) ^ 5 :=
      integerOccurrenceStorage_bound source target N C hsize hsymbol
    _ ≤ (N + 2) * (N + 2) ^ 5 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerStoredDataSpace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open Filter

private theorem natural_pair_storage (source target : List ℕ) (X A : ℕ)
    (hX : 2 ≤ X) (hsize : source.length + target.length ≤ X)
    (hwidth : ∀ a ∈ source ++ target, Nat.size a ≤ X ^ A) :
    storedNaturalBits source + storedNaturalBits target ≤ X ^ (A + 3) := by
  have hs := storedNaturalBits_le source (X ^ A)
    (fun a ha => hwidth a (List.mem_append_left _ ha))
  have ht := storedNaturalBits_le target (X ^ A)
    (fun a ha => hwidth a (List.mem_append_right _ ha))
  have hp : 1 ≤ X ^ A := one_le_pow₀ (by omega)
  have hm := Nat.mul_le_mul_right (X ^ A + 1) hsize
  have hc : 4 ≤ X ^ 2 := by nlinarith only [hX]
  calc
    _ ≤ 4 * X * X ^ A := by nlinarith only [hs, ht, hm, hX, Nat.mul_le_mul_left X hp]
    _ ≤ X ^ 2 * X * X ^ A := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right X hc)
    _ = _ := by rw [pow_add]; ring

theorem storedNaturalInput_polynomial (source target : List ℕ) (N : ℕ)
    (hsize : source.length + target.length ≤ N)
    (hsymbol : ∀ a ∈ source ++ target, Nat.size a ≤ inputHeight N ^ 3) :
    storedNaturalBits source + storedNaturalBits target ≤ (N + 2) ^ 15 := by
  have hh := Nat.pow_le_pow_left (computed_height_polynomial N) 3
  rw [← pow_mul] at hh
  exact natural_pair_storage source target (N + 2) 12 (by omega) (by omega)
    (fun a ha => (hsymbol a ha).trans hh)

/-- The explicitly retained original integer input, its encoded arrays,
and the target occurrence index. -/


private theorem combine_input_storage (X C raw encoded index : ℕ) (hX : 2 ≤ X)
    (hr : raw ≤ X ^ (C + 3)) (he : encoded ≤ X ^ 15) (hi : index ≤ X ^ 6) :
    raw + encoded + index ≤ X ^ (C + 22) := by
  let K := C + 20
  have hpos : 0 < X := by omega
  have hr' : raw ≤ X ^ K := hr.trans (Nat.pow_le_pow_right hpos (by dsimp only [K]; omega))
  have he' : encoded ≤ X ^ K := he.trans (Nat.pow_le_pow_right hpos (by dsimp only [K]; omega))
  have hi' : index ≤ X ^ K := hi.trans (Nat.pow_le_pow_right hpos (by dsimp only [K]; omega))
  calc
    _ ≤ 3 * X ^ K := by omega
    _ ≤ X ^ 2 * X ^ K := Nat.mul_le_mul_right _ (by nlinarith only [hX])
    _ = _ := by rw [← pow_add]; congr 1; dsimp only [K]; omega

theorem integerStoredDataSpace_polynomial_oai (C : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℤ,
      source.length + target.length ≤ N →
      (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
      integerStoredDataSpace source target ≤ (N + 2) ^ (C + 22) := by
  filter_upwards [integer_encoded_symbol_bits C, integerOccurrenceStorage_polynomial C]
    with N hbits hindex
  intro source target hsize hsymbols
  have hr := storedIntegerInput_polynomial source target N C hsize hsymbols
  have he := storedNaturalInput_polynomial (source.map integerSymbolCode)
    (target.map integerSymbolCode) N (by simpa only [List.length_map] using hsize)
    (hbits source target hsymbols)
  have hi := hindex source target hsize hsymbols
  have h := combine_input_storage (N + 2) C _ _ _ (by omega) hr he hi
  unfold integerStoredDataSpace
  omega

end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.integerStoredDataSpace_polynomial_oai := @OAI.EditApproximation.integerStoredDataSpace_polynomial_oai
