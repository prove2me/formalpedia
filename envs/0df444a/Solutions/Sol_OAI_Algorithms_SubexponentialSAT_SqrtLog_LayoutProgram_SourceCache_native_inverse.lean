-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceCache.native_inverse
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:07:16.714095+00:00
-- url     : https://prove2.me/submissions/2093b983-2c15-4747-afee-4162a83ed78d

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S157

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_LiftRing
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFinite _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The finite free ring used for prime-power counting

This file constructs the quotient by a monic polynomial, proves that a
positive-degree quotient retains the base ring, and constructs coefficient
reduction maps between these polynomial quotient rings.
-/

namespace SubexponentialSAT.LiftRing

noncomputable section

open Polynomial

section General

variable {R S : Type*} [CommRing R] [CommRing S]

theorem natCard_extension {F : R[X]} (hF : F.Monic) :
    Nat.card (Extension F) = Nat.card R ^ F.natDegree := by
  calc
    Nat.card (Extension F) = Nat.card (Fin F.natDegree → R) :=
      Nat.card_congr (coordinates hF).toEquiv
    _ = Nat.card R ^ F.natDegree := by rw [Nat.card_fun]; simp

end General

end

end SubexponentialSAT.LiftRing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_NilpotentDefect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Divisibility of the marked defect

After the input coordinates have been substituted, the coefficient of U in
each incidence argument is divisible by p. Polynomial operations preserve
the stronger invariant that the coefficient of U^j is divisible by p^j.
This proves the high-U vanishing needed by canonical truncation.
-/

namespace SubexponentialSAT.NilpotentDefect

noncomputable section

open scoped BigOperators

section Units

variable {R S : Type*} [CommRing R] [CommRing S]

theorem geometricInverse_mul (a b : R) (μ : ℕ)
    (hnil : (1 - a * b) ^ μ = 0) :
    geometricInverse a b μ * a = 1 := by
  rw [mul_comm]
  exact mul_geometricInverse a b μ hnil

end Units

end

end SubexponentialSAT.NilpotentDefect

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpResidueInverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable inversion by finite-field powering and nilpotent correction

The algorithm uses only scalar additions and multiplications, with explicit
finite loops. It constructs the entire inverse-difference table needed by CRT.
Its counters are ring-operation counts, not an assertion of machine time.
-/

namespace SubexponentialSAT.SubexpResidueInverse

open scoped BigOperators

section Algorithm

variable {A : Type*} [CommRing A]

theorem geometricHorner_value (z : A) (n : ℕ) :
    (geometricHornerWithCost z n).1 = ∑ i ∈ Finset.range n, z ^ i := by
  induction n with
  | zero => simp [geometricHornerWithCost]
  | succ n ih => simpa [geometricHornerWithCost, ih] using (@geom_sum_succ A _ z n).symm

theorem inverseWithCost_value (q μ : ℕ) (a : A) :
    (inverseWithCost q μ a).1 =
      NilpotentDefect.geometricInverse a (a ^ (q - 2)) μ := by
  simp only [inverseWithCost, SubexpPolynomialCost.scalarPower_value,
    geometricHorner_value, NilpotentDefect.geometricInverse]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

end Algorithm

section Correctness

variable {A E : Type*} [CommRing A] [Field E] [Fintype E]

/-- A finite-field Fermat power is an inverse after reduction. -/
theorem residue_fermat_inverse (ρ : A →+* E) (q : ℕ)
    (hq : Fintype.card E = q) (a : A) (ha : ρ a ≠ 0) :
    ρ (a * a ^ (q - 2)) = 1 := by
  have hq2 : 2 ≤ q := by
    rw [← hq]
    exact Fintype.one_lt_card
  rw [map_mul, map_pow, ← pow_succ']
  have he : q - 2 + 1 = q - 1 := by omega
  rw [he, ← hq]
  exact FiniteField.pow_card_sub_one_eq_one (ρ a) ha

/-- The principal-kernel condition converts the residue defect into a
nilpotent element of the original, possibly non-field ring. -/
theorem fermat_defect_nilpotent (ρ : A →+* E) (q : ℕ)
    (hq : Fintype.card E = q) (π : A) (μ : ℕ) (hπ : π ^ μ = 0)
    (hker : ∀ x, ρ x = 0 → π ∣ x) (a : A) (ha : ρ a ≠ 0) :
    (1 - a * a ^ (q - 2)) ^ μ = 0 := by
  have hz : ρ (1 - a * a ^ (q - 2)) = 0 := by
    rw [map_sub, map_one, residue_fermat_inverse ρ q hq a ha, sub_self]
  obtain ⟨d, hd⟩ := hker _ hz
  rw [hd, mul_pow, hπ, zero_mul]

theorem inverseWithCost_correct (ρ : A →+* E) (q : ℕ)
    (hq : Fintype.card E = q) (π : A) (μ : ℕ) (hπ : π ^ μ = 0)
    (hker : ∀ x, ρ x = 0 → π ∣ x) (a : A) (ha : ρ a ≠ 0) :
    (inverseWithCost q μ a).1 * a = 1 := by
  rw [inverseWithCost_value]
  exact NilpotentDefect.geometricInverse_mul a (a ^ (q - 2)) μ
    (fermat_defect_nilpotent ρ q hq π μ hπ hker a ha)

end Correctness

end SubexponentialSAT.SubexpResidueInverse

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramHorner
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native fixed-control Horner iteration, shared by scalar nilpotent repair
and the independently truncated local polynomial inverse. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem hornerValue_decode {C A : Type*} [CommRing A] (decode : C → A)
    (mulOp addOp : C → C → C)
    (hm : ∀ a b, decode (mulOp a b) = decode a * decode b)
    (ha : ∀ a b, decode (addOp a b) = decode a + decode b)
    (z one seed : C) (hone : decode one = 1) (hseed : decode seed = 0) (n : ℕ) :
    decode ((hornerValue mulOp addOp z one)^[n] seed) =
      ∑ i ∈ Finset.range n, decode z ^ i := by
  induction n with
  | zero => simpa using hseed
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      simp only [hornerValue, ha, hm, hone, ih]
      simpa only [mul_comm] using (@geom_sum_succ A _ (decode z) n).symm

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramInverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native residue-power preparation with dynamic extension degree and ring
precision. Stack 209 contains a unary residue-size-minus-two exponent;
stack 212 independently contains the unary ring precision. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem inverseValue_decode {C A : Type*} [CommRing A]
    (decode : C → A) (mulOp addOp : C → C → C)
    (hm : ∀ a b, decode (mulOp a b) = decode a * decode b)
    (ha : ∀ a b, decode (addOp a b) = decode a + decode b)
    (zero one minusOne a : C)
    (hz : decode zero = 0) (ho : decode one = 1) (hn : decode minusOne = -1)
    (q precision : ℕ) :
    decode (inverseValue mulOp addOp zero one minusOne a (q-2) precision) =
      (SubexponentialSAT.SubexpResidueInverse.inverseWithCost q precision (decode a)).1 := by
  rw [SubexponentialSAT.SubexpResidueInverse.inverseWithCost_value]
  simp only [inverseValue, hm, hornerValue_decode decode mulOp addOp hm ha _ one zero ho hz,
    iterate_mul_decode decode mulOp hm, ho, one_mul, ha, hn,
    SubexponentialSAT.NilpotentDefect.geometricInverse]
  have he : decode a ^ (q - 2) * decode a * -1 + 1 = 1 - decode a * decode a ^ (q - 2) := by ring
  rw [he, mul_comm]

theorem inverseValue_correct {C A E : Type*} [CommRing A] [Field E] [Fintype E]
    (decode : C → A) (mulOp addOp : C → C → C)
    (hm : ∀ a b, decode (mulOp a b) = decode a * decode b)
    (ha : ∀ a b, decode (addOp a b) = decode a + decode b)
    (zero one minusOne a : C)
    (hz : decode zero = 0) (ho : decode one = 1) (hn : decode minusOne = -1)
    (rho : A →+* E) (q : ℕ) (hq : Fintype.card E = q)
    (pi : A) (precision : ℕ) (hpi : pi ^ precision = 0)
    (hker : ∀ x, rho x = 0 → pi ∣ x) (hne : rho (decode a) ≠ 0) :
    decode (inverseValue mulOp addOp zero one minusOne a (q-2) precision) * decode a = 1 := by
  rw [inverseValue_decode decode mulOp addOp hm ha zero one minusOne a hz ho hn]
  exact SubexponentialSAT.SubexpResidueInverse.inverseWithCost_correct rho q hq pi precision hpi hker _ hne

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramDifference
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A physical inverse builder for a difference of two supplied nodes. The
residue exponent and nilpotence precision are the independent runtime inputs
209 and 212; no loop enumerates the lifted ring. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem differenceValue_decode {C A : Type*} [Ring A]
    (decode : C → A) (mulOp addOp : C → C → C)
    (hm : ∀ a b, decode (mulOp a b) = decode a * decode b)
    (ha : ∀ a b, decode (addOp a b) = decode a + decode b)
    (theta other minusOne : C) (hn : decode minusOne = -1) :
    decode (differenceValue mulOp addOp theta other minusOne) = decode theta - decode other := by
  simp [differenceValue, ha, hm, hn, sub_eq_add_neg]

theorem differenceInverse_correct {C A E : Type*} [CommRing A] [Field E] [Fintype E]
    (decode : C → A) (mulOp addOp : C → C → C)
    (hm : ∀ a b, decode (mulOp a b) = decode a * decode b)
    (ha : ∀ a b, decode (addOp a b) = decode a + decode b)
    (theta other zero one minusOne : C)
    (hz : decode zero = 0) (ho : decode one = 1) (hn : decode minusOne = -1)
    (rho : A →+* E) (q : ℕ) (hq : Fintype.card E = q)
    (pi : A) (precision : ℕ) (hpi : pi^precision = 0)
    (hker : ∀ x, rho x = 0 → pi ∣ x)
    (hne : rho (decode theta) ≠ rho (decode other)) :
    decode (inverseValue mulOp addOp zero one minusOne
      (differenceValue mulOp addOp theta other minusOne) (q-2) precision) *
        (decode theta - decode other) = 1 := by
  have hd := differenceValue_decode decode mulOp addOp hm ha theta other minusOne hn
  have hnonzero : rho (decode (differenceValue mulOp addOp theta other minusOne)) ≠ 0 := by
    rw [hd, map_sub]
    exact sub_ne_zero.mpr hne
  have h := inverseValue_correct decode mulOp addOp hm ha zero one minusOne
    (differenceValue mulOp addOp theta other minusOne) hz ho hn rho q hq pi precision hpi hker hnonzero
  simpa only [hd] using h

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Unramified ring attached to a supplied irreducible ternary polynomial

`Data.coefficients` is execution data. An irreducible-search correctness proof
can supply `Data.irreducible`; no separate choice of a minimum polynomial is
made in this model. All polynomial lifts use coefficient representatives.
-/

noncomputable section
namespace SubexponentialSAT.SqrtLog.RingModel

open Polynomial

namespace Data

variable {d : ℕ} (a : Data d) (t : ℕ)

theorem residue_cardinality : Nat.card a.E = 3 ^ d := by
  simpa only [a.residuePolynomial_degree, Nat.card_zmod] using
    LiftRing.natCard_extension a.residuePolynomial_monic

end Data

end SubexponentialSAT.SqrtLog.RingModel

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramNativeInverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A standalone native inverse of a node difference. The exponent is the
residue-field cardinality minus two; the separate repair loop has length t. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram.NativeInverse
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing

theorem value_correct (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (theta other minusOne : RingProgram.Code (RingProgram.ScalarCode 3 t) d)
    (hn : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (hne : a.rho t ht ((RingProgram.modelRing t ht hd a M cache).decode theta) ≠
      a.rho t ht ((RingProgram.modelRing t ht hd a M cache).decode other)) :
    (RingProgram.modelRing t ht hd a M cache).decode (value t a M cache theta other minusOne) *
      ((RingProgram.modelRing t ht hd a M cache).decode theta -
        (RingProgram.modelRing t ht hd a M cache).decode other) = 1 := by
  let ops := RingProgram.modelRing t ht hd a M cache
  exact differenceInverse_correct ops.decode
    (fun x y => (ops.mulRun x y).1) (fun x y => (ops.addRun x y).1)
    ops.mul_correct ops.add_correct theta other ops.zeroRun.1 ops.oneRun.1 minusOne
    ops.zero_correct ops.one_correct hn (a.rho t ht) (3^d)
    (by simpa only [Nat.card_eq_fintype_card] using a.residue_cardinality)
    3 t (a.prime_power_zero t) (fun x hx => (a.rho_eq_zero_iff t ht x).mp hx) hne

end SubexponentialSAT.SqrtLog.CRTLocalProgram.NativeInverse

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingNodeProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical radix generator emits precisely the coefficient encoding of
nodes in the actual supplied-polynomial unramified ring. -/
namespace SubexponentialSAT.SqrtLog.RingNodeProgram

open SubexponentialSAT BinaryArithmetic SubexpLiftRing SubexpQuarticRing
open RingProgram

theorem nodeCode_value (t d n : ℕ) (ht : 0 < t) (j : Fin d) :
    BinaryArithmetic.toNat (nodeCode t d n j).val = n / 3^j.val % 3 := by
  apply toNat_fixedBits_of_lt
  have hc : 2^2 ≤ 2^(2*t) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [ternary_baseWidth]
  have hm := Nat.mod_lt (n / 3^j.val) (by decide : 0 < 3)
  norm_num at hc
  omega

theorem residueNode_coordinate {d : ℕ} (a : RingModel.Data d) (Q : ℕ)
    (hQ : Q < 3^d) (i : Fin Q) (j : Fin d) :
    (a.fieldCoordinates (a.residueNode Q hQ i) j).val = (i.val+1) / 3^j.val % 3 := by
  let index : Fin (3^d) := ⟨i.val+1, by omega⟩
  let v : Fin d → ZMod 3 := fun j =>
    ZMod.finEquiv 3 ((finFunctionFinEquiv.symm index) j)
  change (a.fieldCoordinates (a.fieldCoordinates.symm v) j).val = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The physical words decode to the same nodes used by interpolation. -/
theorem nodeCode_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) (Q : ℕ) (hQ : Q < 3^d) (i : Fin Q) :
    (modelRing t ht hd a M cache).decode (nodeCode t d (i.val+1)) =
      a.node t Q ht hQ i := by
  rw [modelRing_decode]
  unfold RingModel.Data.node RingModel.Data.sectionValue
  congr 1
  funext j
  unfold wordValue
  rw [nodeCode_value t d (i.val+1) ht j, residueNode_coordinate]

theorem generated_residue_ne_zero (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) (Q : ℕ) (hQ : Q < 3^d) (i : Fin Q) :
    a.rho t ht ((modelRing t ht hd a M cache).decode (nodeCode t d (i.val+1))) ≠ 0 := by
  rw [nodeCode_decode t ht hd a M cache Q hQ, RingModel.Data.rho_node]
  exact a.residueNode_ne_zero Q hQ i

end SubexponentialSAT.SqrtLog.RingNodeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Values computed by the physical interpolation-cache producer. Every
entry is a typed output of an executable ring program. The uniform inverse
routine has an explicit zero-diagonal interpretation. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram

open SubexponentialSAT
open scoped BigOperators

theorem inverseValue_correct (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (minusOne x : Coeff t d)
    (hm : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (hx : a.rho t ht ((RingProgram.modelRing t ht hd a M cache).decode x) ≠ 0) :
    (RingProgram.modelRing t ht hd a M cache).decode (inverseValue t a M cache minusOne x) *
      (RingProgram.modelRing t ht hd a M cache).decode x = 1 := by
  let ops := RingProgram.modelRing t ht hd a M cache
  have hz : ops.decode ops.zeroRun.1=0 := ops.zero_correct
  have hz' : (RingProgram.modelRing t ht hd a M cache).decode ops.zeroRun.1=0 := hz
  have h := CRTLocalProgram.NativeInverse.value_correct t ht hd a M cache x
    ops.zeroRun.1 minusOne hm (by simpa only [hz',map_zero] using hx)
  rw [hz',sub_zero] at h
  exact h

theorem node_inverse_correct (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (minusOne : Coeff t d)
    (hm : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (Q : ℕ) (hQ : Q < 3^d) (i : Fin Q) :
    (RingProgram.modelRing t ht hd a M cache).decode
      (inverseValue t a M cache minusOne (RingNodeProgram.nodeCode t d (i.val+1))) *
      a.node t Q ht hQ i=1 := by
  rw [← RingNodeProgram.nodeCode_decode t ht hd a M cache Q hQ i]
  apply inverseValue_correct t ht hd a M cache minusOne _ hm
  exact RingNodeProgram.generated_residue_ne_zero t ht hd a M cache Q hQ i

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceCache
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native interpolation-cache values implement the exact node units used
by the universal source semantics. No field inverse is assumed in O. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceCache

open SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpRowInterpolation
open InterpolationCacheProgram

variable {d Q : ℕ}

private theorem inverse_unique {O : Type*} [CommRing O] {a x y : O}
    (hx : x*a=1) (hy : y*a=1) : x=y := by
  calc
    x=x*(a*y) := by rw [mul_comm a y,hy,mul_one]
    _=(x*a)*y := by ring
    _=y := by rw [hx,one_mul]

theorem native_inverse_oai (t : ℕ) (ht : 0 < t) (hd : 0 < d) (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (hm : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (hQ : Q < 3^d) (i : Fin Q) :
    (RingProgram.modelRing t ht hd a M cache).decode ((native t a M cache minusOne).inverse i)=
      (a.nodeUnits t Q ht hQ).nodeInverse i := by
  apply inverse_unique (a:=a.node t Q ht hQ i)
  · exact node_inverse_correct t ht hd a M cache minusOne hm Q hQ i
  · exact NodeUnits.nodeInverse_mul _ i

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceCache

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceCache.native_inverse_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceCache.native_inverse_oai
