-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.nativeStored_fixed_rows
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:23:10.227238+00:00
-- url     : https://prove2.me/submissions/7dbfba68-043a-49fc-960f-2d58f6be3a6b

import Mathlib
import Definitions.Def_OAIQ081S151
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationAssembly_shifted_tail_polynomial

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact native evaluation of a dynamically sized dense polynomial. Input
coefficients are in increasing degree order. Every other persistent stack is
preserved; the input stream and runtime counter are consumed. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec serviceSpec_frame lowFrame_refl lowFrame_update)

section Semantics
variable {C A : Type*} [CommRing A]

theorem fold_decode (decode : C → A) (mulOp addOp : C → C → C)
    (hm : ∀ a b, decode (mulOp a b) = decode a * decode b)
    (ha : ∀ a b, decode (addOp a b) = decode a + decode b)
    (x : C) (cs : List C) (seed : C) :
    decode (fold (stepValue mulOp addOp x) cs seed) =
      cs.foldl (fun value b => value * decode x + decode b) (decode seed) := by
  induction cs generalizing seed with
  | nil => rfl
  | cons c cs ih =>
      change decode (fold (stepValue mulOp addOp x) cs (stepValue mulOp addOp x seed c)) = _
      rw [ih, List.foldl_cons]
      simp only [stepValue, ha, hm]

theorem output_decode (decode : C → A) (mulOp addOp : C → C → C)
    (hm : ∀ a b, decode (mulOp a b) = decode a * decode b)
    (ha : ∀ a b, decode (addOp a b) = decode a + decode b)
    (P : List C) (x zero : C) (hz : decode zero = 0) :
    decode (fold (stepValue mulOp addOp x) P.reverse zero) =
      (PolynomialAlgorithm.denote (P.map decode)).eval (decode x) := by
  rw [fold_decode decode mulOp addOp hm ha, List.foldl_reverse, hz]
  induction P with
  | nil => simp []
  | cons a P ih =>
      simp only [List.foldr_cons, List.map_cons, PolynomialAlgorithm.denote,
        Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X, ih]
      ring

end Semantics
end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native Horner evaluation in the actual arbitrary-degree unramified
RingModel. The instruction table is independent of precision, extension
degree and polynomial length. Ring caches are explicit runtime inputs. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem modelValue_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (P : List (RingProgram.Code (RingProgram.ScalarCode 3 t) d))
    (x : RingProgram.Code (RingProgram.ScalarCode 3 t) d) :
    (RingProgram.modelRing t ht hd a M cache).decode (modelValue t a M cache P x) =
      (PolynomialAlgorithm.denote (P.map (RingProgram.modelRing t ht hd a M cache).decode)).eval
        ((RingProgram.modelRing t ht hd a M cache).decode x) := by
  let ops := RingProgram.modelRing t ht hd a M cache
  exact output_decode ops.decode (fun x y => (ops.mulRun x y).1)
    (fun x y => (ops.addRun x y).1) ops.mul_correct ops.add_correct P x
    ops.zeroRun.1 ops.zero_correct

end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsPerturbation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual row perturbations, rather than an assumed support invariant.
Every formal Boolean coordinate is multiplied by a polynomial with zero
constant term in Z. The construction is valid over any commutative ring. -/

namespace SubexponentialSAT.SqrtLog.Moments

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators

variable {V R : Type*} [DecidableEq V] [CommRing R]

theorem variableZ_coeff (v : V) (p : Polynomial R) (j : ℕ) :
    (variableZ v p).coeff j = Squarefree.monomial {v} (p.coeff j) := by
  simp only [variableZ, Polynomial.coeff_mul_C, Polynomial.coeff_map]
  change Squarefree.monomial ∅ (p.coeff j) * Squarefree.monomial {v} 1 = _
  simp

end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Computable normalized sparse coefficient lists. Zero coefficients may stay
in the list; keys are unique, so this does not enlarge the finite index bound.
No equality decision for coefficients or full ambient Boolean table is used. -/

namespace SubexponentialSAT.SqrtLog.Squarefree.Sparse

open scoped BigOperators

variable {K R A : Type*} [DecidableEq K] [AddCommMonoid R]

section Decode

variable [AddCommMonoid A]

omit [DecidableEq K] [AddCommMonoid R] in
theorem decode_append (atom : K → R → A) (a b : Data K R) :
    decode atom (a ++ b) = decode atom a + decode atom b := by
  induction a with
  | nil => simp [decode]
  | cons h a ih => simp [decode, ih, add_assoc]

end Decode
end SubexponentialSAT.SqrtLog.Squarefree.Sparse

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationProgramStored
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpDensePolynomial
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree Squarefree.Sparse

variable {C R V : Type*} [CommRing R] [DecidableEq V]

private theorem variableZ_add (v : V) (p q : Polynomial R) :
    Moments.variableZ v (p+q) = Moments.variableZ v p + Moments.variableZ v q := by
  simp [Moments.variableZ, add_mul]

private theorem atom_variable (v : V) (j : ℕ) (c : R) :
    atom (⟨0,j,{v}⟩ : Index V) c =
      Polynomial.C (Moments.variableZ v (Polynomial.monomial j c)) := by
  change Polynomial.C (Polynomial.monomial j (monomial {v} c)) = _
  congr 1
  ext z
  rw [Moments.variableZ_coeff]
  by_cases h : j = z <;> simp [Polynomial.coeff_monomial, h]

/-- Exact meaning of the emitted coefficient stream, before precision clipping. -/
theorem coefficientRecords_denote (ops : RepresentedRing C R) (v : V)
    (j : ℕ) (p : List C) :
    Sparse.denote (decodeRecords ops (coefficientRecords v j p)) =
      Polynomial.C (Moments.variableZ v (Polynomial.X^j * polynomial ops p)) := by
  induction p generalizing j with
  | nil => simp [coefficientRecords, decodeRecords, Sparse.denote, Sparse.decode,
      polynomial, SubexpDensePolynomial.decodeList, Moments.variableZ]
  | cons c cs ih =>
      change atom (⟨0,j,{v}⟩ : Index V) (ops.decode c) +
        Sparse.denote (decodeRecords ops (coefficientRecords v (j+1) cs)) = _
      rw [atom_variable, ih, ← Polynomial.C_add, ← variableZ_add]
      congr 2
      simp only [polynomial, SubexpDensePolynomial.decodeList, List.map_cons,
        PolynomialAlgorithm.denote_cons]
      rw [mul_add, pow_succ]
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      ring

end SubexponentialSAT.SqrtLog.PerturbationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyStoredCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Validity and exact denotation of the reversed, unnormalized coefficient
stream emitted by the new perturbation assembly. Zero coefficients remain. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT.SubexpSymbolicCost
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree Squarefree.Sparse PerturbationProgram
open scoped BigOperators

variable {C R : Type*} [CommRing R]

private theorem decode_reverse {n : ℕ} (ops : RepresentedRing C R)
    (l : List (Index (Fin n) × C)) :
    Sparse.denote (decodeRecords ops l.reverse) = Sparse.denote (decodeRecords ops l) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.reverse_cons,decodeRecords,List.map_append,Sparse.denote,
        Sparse.decode_append,List.map_cons,List.map_nil,Sparse.decode,add_zero]
      change Sparse.denote (decodeRecords ops l.reverse) + _ =
        _ + Sparse.denote (decodeRecords ops l)
      rw [ih,add_comm]

private theorem decode_flatten {n : ℕ} (ops : RepresentedRing C R)
    (ls : List (List (Index (Fin n) × C))) :
    Sparse.denote (decodeRecords ops ls.flatten) =
      (ls.map fun l => Sparse.denote (decodeRecords ops l)).sum := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
      simp only [List.flatten_cons,decodeRecords,List.map_append,Sparse.denote,
        Sparse.decode_append,List.map_cons,List.sum_cons]
      exact congrArg (_ + ·) ih

theorem rawWords_denote (ops : RepresentedRing C R) {n : ℕ}
    (beta : C) (tails : Fin n → List C) :
    Sparse.denote (decodeRecords ops (rawWords beta tails)) =
      atom Index.origin (ops.decode beta) +
        ∑ v, Polynomial.C (Moments.variableZ v
          (Polynomial.X * polynomial ops (tails v))) := by
  rw [rawWords,decode_reverse]
  change atom Index.origin (ops.decode beta) +
    Sparse.denote (decodeRecords ops (List.ofFn fun v =>
      coefficientRecords v 1 (tails v)).flatten) = _
  rw [decode_flatten,List.map_ofFn,List.sum_ofFn]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  simpa only [Function.comp_apply,pow_one] using
    coefficientRecords_denote ops v 1 (tails v)

theorem variableZ_trunc_C {n : ℕ} (t J : ℕ) (ht : 0 < t)
    (v : Fin n) (p : Polynomial R) :
    Polynomial.C (Moments.variableZ v (Truncation.trunc J p)) =
      canonical t J (Polynomial.C (Moments.variableZ v p)) := by
  ext u j
  by_cases hu : u=0 <;> by_cases hj : j < J <;>
    simp [Polynomial.coeff_C,hu,hj,ht,Moments.variableZ_coeff]

theorem rawWords_canonical_denote (ops : RepresentedRing C R) {n : ℕ}
    (t J : ℕ) (ht : 0 < t) (hJ : 0 < J)
    (beta : C) (tails : Fin n → List C) (row : Fin n → Polynomial R) (theta : R)
    (hrow : ∀ v, Polynomial.X * polynomial ops (tails v) =
      Truncation.trunc J (Moments.rowDelta (row v) theta)) :
    Sparse.denote (decodeRecords ops (rawWords beta tails)) =
      canonical t J (Moments.incidenceJet row theta (ops.decode beta)) := by
  rw [rawWords_denote]
  simp_rw [hrow,variableZ_trunc_C t J ht]
  have hc : atom Index.origin (ops.decode beta) =
      canonical t J (atom (Index.origin : Index (Fin n)) (ops.decode beta)) := by
    rw [canonical_atom]
    simp [Index.Kept,Index.origin,ht,hJ]
  rw [hc,←map_sum,←map_add]
  congr 1
  simp only [Moments.incidenceJet,Moments.incidenceZ,map_add,map_sum]
  rfl

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyStored
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual fixed-array Horner output is already valid Stored data.
The native order is reversed and zero coefficients are deliberately kept. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT.SubexpSymbolicCost
open DensePolynomialProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree PerturbationProgram

variable {B d n : ℕ} {R : Type*} [CommRing R]

theorem outputWords_denote (ops : RepresentedRing (Coeff B d) R)
    (t J : ℕ) (ht : 0 < t) (hJ : 0 < J)
    (theta beta : Coeff B d) (rows : Fin n → List (Coeff B d)) :
    Sparse.denote (decodeRecords ops (outputWords ops.program J theta beta rows)) =
      canonical t J (Moments.incidenceJet (fun v => polynomial ops (rows v))
        (ops.decode theta) (ops.decode beta)) := by
  apply rawWords_canonical_denote ops t J ht hJ beta
  intro v
  exact shifted_tail_polynomial ops J theta (rows v)

theorem outputStored_denote (ops : RepresentedRing (Coeff B d) R)
    (t J : ℕ) (ht : 0 < t) (hJ : 0 < J)
    (theta beta : Coeff B d) (rows : Fin n → List (Coeff B d)) :
    (outputStored ops t J ht hJ theta beta rows).denote =
      canonical t J (Moments.incidenceJet (fun v => polynomial ops (rows v))
        (ops.decode theta) (ops.decode beta)) :=
  outputWords_denote ops t J ht hJ theta beta rows

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives SubexpLiftRing SubexpQuarticRing

/-- The concrete arithmetic result of one selected row is its actual node
value plus the preceding accumulator. -/
theorem nextValue_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (P : List (Coeff t d))
    (theta acc : Coeff t d) :
    (RingProgram.modelRing t ht hd a M cache).decode (nextValue t a M cache P theta acc) =
      (PerturbationProgram.polynomial (RingProgram.modelRing t ht hd a M cache) P).eval
        ((RingProgram.modelRing t ht hd a M cache).decode theta) +
          (RingProgram.modelRing t ht hd a M cache).decode acc := by
  let ops := RingProgram.modelRing t ht hd a M cache
  change ops.decode (ops.addRun (HornerProgram.modelValue t a M cache P theta) acc).1 = _
  rw [ops.add_correct,HornerProgram.modelValue_decode t ht hd a M cache P theta]
  rfl

theorem fold_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (theta acc : Coeff t d)
    (rows : List (List (Coeff t d) × Bool)) :
    (RingProgram.modelRing t ht hd a M cache).decode
      (rows.foldl (stepValue t a M cache theta) acc) =
      (RingProgram.modelRing t ht hd a M cache).decode acc +
        PerturbationProgram.betaValue (RingProgram.modelRing t ht hd a M cache) theta rows := by
  induction rows generalizing acc with
  | nil => simp [PerturbationProgram.betaValue]
  | cons row rows ih =>
    rcases row with ⟨P,b⟩
    rw [List.foldl_cons,ih]
    cases b
    · simp [stepValue,PerturbationProgram.betaValue]
    · simp only [stepValue,ite_true, if_true]
      rw [nextValue_decode t ht hd a M cache P theta acc]
      simp only [PerturbationProgram.betaValue,List.map_cons,List.sum_cons,ite_true, if_true]
      ring

theorem runValue_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (theta : Coeff t d)
    (rows : List (List (Coeff t d) × Bool)) :
    (RingProgram.modelRing t ht hd a M cache).decode (runValue t a M cache theta rows) =
      PerturbationProgram.betaValue (RingProgram.modelRing t ht hd a M cache) theta rows := by
  rw [runValue,fold_decode t ht hd a M cache]
  have hz := (RingProgram.modelRing t ht hd a M cache).zero_correct
  rw [← RingProgram.modelRing_program t ht hd a M cache]
  simpa using congrArg (fun x => x + PerturbationProgram.betaValue
    (RingProgram.modelRing t ht hd a M cache) theta rows) hz

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyStoredNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The concrete low-variable output with its executed beta fold, rather than
a supplied beta premise. The full source-row interpretation remains explicit. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT
open DensePolynomialProgram _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree PerturbationProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open scoped BigOperators

theorem betaValue_pairedRows {B d N : ℕ} {R : Type*} [CommRing R]
    (ops : SubexpSymbolicCost.RepresentedRing (Coeff B d) R) (theta : Coeff B d)
    (rows : List (Fixed.Array B d N × Bool)) :
    betaValue ops theta (pairedRows rows) =
      ∑ v : Fin rows.length,
        (polynomial ops rows[v].1.val).eval (ops.decode theta) *
          (if rows[v].2 then 1 else 0) := by
  have hrows : pairedRows rows = List.ofFn (fun v : Fin rows.length =>
      (rows[v].1.val,rows[v].2)) := by
    simpa only [pairedRows, Fin.getElem_fin] using
      (List.ofFn_getElem_eq_map rows (fun row => (row.1.val,row.2))).symm
  rw [hrows,betaValue,List.map_ofFn,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro v _
  cases h : rows[v.val].2 <;> simp [Fin.getElem_fin,h]

theorem nativeStored_denote (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u J N : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) :
    (nativeStored t ht hd a M cache u J N hu hJ theta rows).denote =
      canonical u J (Moments.incidenceJet
        (fun v : Fin rows.length => polynomial (RingProgram.modelRing t ht hd a M cache) rows[v].1.val)
        ((RingProgram.modelRing t ht hd a M cache).decode theta)
        (∑ v : Fin rows.length,
          (polynomial (RingProgram.modelRing t ht hd a M cache) rows[v].1.val).eval
            ((RingProgram.modelRing t ht hd a M cache).decode theta) *
              (if rows[v].2 then 1 else 0))) := by
  rw [nativeStored,outputStored_denote,
    PerturbationBetaProgram.runValue_decode t ht hd a M cache,
    betaValue_pairedRows]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblySourceStored
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The executed source predicate determines the incidence jet independently
of the particular coefficient-array witness returned by each source call. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram
open scoped BigOperators

/-- Replacing decoded source rows and selected bits by their fixed meanings
commutes with the harmless equal-dimension transport of the emitted jet. -/
theorem nativeStored_fixed_rows_oai (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u J N n : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) (hlen : rows.length=n)
    (family : Fin n → Polynomial (a.O t)) (bits : Fin n → Bool)
    (hrow : ∀ i : Fin rows.length,
      PerturbationProgram.polynomial (RingProgram.modelRing t ht hd a M cache) rows[i].1.val =
        family (Fin.cast hlen i))
    (hbits : ∀ i : Fin rows.length, rows[i].2 = bits (Fin.cast hlen i)) :
    castJet hlen (nativeStored t ht hd a M cache u J N hu hJ theta rows).denote =
      Squarefree.canonical u J (Moments.incidenceJet family
        ((RingProgram.modelRing t ht hd a M cache).decode theta)
        (∑ v : Fin n, (family v).eval ((RingProgram.modelRing t ht hd a M cache).decode theta) *
          (if bits v then 1 else 0))) := by
  subst n
  simp only [Fin.cast_refl] at hrow hbits
  change (nativeStored t ht hd a M cache u J N hu hJ theta rows).denote = _
  rw [nativeStored_denote]
  simp_rw [hrow,hbits]
  rfl

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.nativeStored_fixed_rows_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.nativeStored_fixed_rows_oai
