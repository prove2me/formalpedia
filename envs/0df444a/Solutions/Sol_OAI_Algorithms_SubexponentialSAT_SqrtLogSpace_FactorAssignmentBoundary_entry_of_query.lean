-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary.entry_of_query
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:09:16.489+00:00
-- url     : https://prove2.me/submissions/5e63c100-1a8e-469f-9838-3951f5af7373

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S185

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramZero
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact zero bytes for the native padded-polynomial constructors. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

private theorem toNat_false (n : ℕ) :
    SubexponentialSAT.BinaryArithmetic.toNat (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,ih]

theorem zero_cache_bits (p t : ℕ) [Fact p.Prime] (cache : RingProgram.ScalarCache p t)
    (hz : SubexponentialSAT.BinaryArithmetic.toNat cache.zero.val < p^t) :
    cache.zero.val = List.replicate (baseWidth p t) false := by
  apply SubexponentialSAT.SubexpModulusConstruction.bits_eq_of_length_of_value
  · simp [cache.zero.property]
  · have hv := congrArg ZMod.val cache.zero_correct
    have hnum : SubexponentialSAT.BinaryArithmetic.toNat cache.zero.val = 0 := by
      simpa only [wordValue,ZMod.val_natCast,Nat.mod_eq_of_lt hz,ZMod.val_zero] using hv
    rw [hnum,toNat_false]

private theorem flatten_replicate_false (d B : ℕ) :
    (List.replicate d (List.replicate B false)).flatten = List.replicate (d*B) false := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [List.replicate_succ,List.flatten_cons,ih,← List.replicate_add]
      congr 1
      ring

theorem flat_constant_zero {B : ℕ} (z : Word B)
    (hz : z.val = List.replicate B false) (d : ℕ) :
    RingProgram.flat (fun _ : Fin d => z) = List.replicate (d*B) false := by
  simp only [RingProgram.flat,hz,List.ofFn_const]
  exact flatten_replicate_false d B

theorem model_zero_bits (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : SubexponentialSAT.BinaryArithmetic.toNat cache.zero.val < 3^t) :
    RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1 =
      List.replicate (d*baseWidth 3 t) false := by
  change RingProgram.flat (fun _ : Fin d => cache.zero) = _
  exact flat_constant_zero cache.zero (zero_cache_bits 3 t cache hz) d

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramTape
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Byte order for descending Horner application. A single whole-tape reversal
puts the last digit first and each digit's coefficients in c,b,a order. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open SubexpQuarticRing

theorem coefficient_tape {B t : ℕ} (code : RingProgram.Code (Word B) (3*t)) :
    RingProgram.flat code=triplesTape (List.ofFn (coefficientTriple t code)) := by
  unfold RingProgram.flat
  rw [List.ofFn_mul']
  simp [triplesTape,tripleTape,coefficientTriple,IdempotentProgram.digitIndex,List.map_ofFn,List.flatten_flatten,List.ofFn_succ,Function.comp_def]

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentBoundary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The real initializer and paid cache setup establish the physical boundary
for the actual stored-ID fold. Bounds are fixed before that fold; the current
Good-empty-support seed is serialized on151, the unread suffix on150 and the
reversed original ID on149. No execution service is a field below. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary
open OAI BitProgram StructuredCalls SubexpSetupStorage
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open FactorAssignmentProgram

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The genuine query's physical ring words and the accepted assignment word
supply the scalar producer boundary; its zero law comes from the same model. -/
theorem query_scalar {r Q n d M : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)}
    {a : FactorAssignmentProgram.Data}
    (h : QueryTupleState.QueryReady q node H high E U M a)
    (hchoices : (a.stacks 145).length = n) :
    FactorTableNative.ScalarMasters q.p.t q.p.model q.p.modulus q.p.cache q.J q.p.R
      q.theta (projectState localRegister FactorTableProgram.basePort a) n := by
  constructor
  · exact Nat.mul_pos q.p.ht (Nat.zero_lt_succ _)
  · exact q.p.hz
  · exact DensePolynomialProgram.model_zero_bits q.p.t q.p.model q.p.modulus q.p.cache q.p.hz
  · exact h.modulus
  · change (a.stacks 202).length = _
    rw [h.width]
    exact q.widthLength
  · exact h.scalarZero
  · exact h.table
  · change (a.stacks 204).length = d
    rw [h.degree,List.length_replicate]
  · exact hchoices
  · exact h.zero
  · exact h.one
  · exact h.theta
  · exact h.ambient
  · exact h.order
  · exact h.radius
  · change (a.stacks 703).length = n
    rw [h.highBits,List.length_ofFn]

/-- All source-row metadata come from the actual query's retained words. -/
theorem query_source {r Q n d M : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)}
    {a : FactorAssignmentProgram.Data}
    (h : QueryTupleState.QueryReady q node H high E U M a) :
    FactorTableNative.SourceMasters q.p q.ps q.packing
      (projectState localRegister FactorTableProgram.basePort a) := by
  refine ⟨h.colors,h.nodes,h.typeWidth,h.positive,h.negative,h.sourceWidth,h.power,
    h.powerNegative,h.radius,h.offset,h.metadata,h.plans,h.inverses,h.negatives,
    h.differences,h.ringWidth,h.rowWidth,h.zero,h.one,?_,h.inverseDenominator⟩
  change a.stacks 211 = RingProgram.flat q.p.minusOne
  rw [h.minus,h.sourceMinus]

/-- The actual query masters, accepted145 overlay and produced low-bank reset
instantiate the assignment boundary. Master cap M and structural cap P remain
separate so setup restores P before every accepted assignment. -/
theorem entry_of_query_oai {r Q n d P M S : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)}
    {a : FactorAssignmentProgram.Data}
    (h : QueryTupleState.QueryReady q node H high E U M a)
    (ha : WordBound P a) (hchoices : (a.stacks 145).length = n)
    (hlow : ∀ i : Fin 56, a.stacks (i.castAdd 840) = [])
    (hcache : 4*M+6 ≤ P)
    (hseed : FactorAssignmentLoop.byteBound n (baseWidth 3 q.p.t) d q.u q.J ≤ P)
    (hsize : 1029*P+99+n+n*FactorTableProgram.literalRecordBound n
      (FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d)+1 ≤ S)
    (hradius : q.p.R+1 ≤ Q) : Entry q P M S a := by
  refine ⟨query_scalar h hchoices,query_source h,ha,h.cacheCaps,h.ambientCap,h.oneCap,
    hcache,hseed,hlow,h.width,h.degree,?_,h.sourceMinus,?_,h.rows,h.clauses,
    h.rowCount,h.markedIndex,h.markedFlag,?_,h.indexWidth,h.indexModulus,hsize,hradius⟩
  · rw [h.lifting]
    exact h.precision
  · exact h.code.trans (IdempotentApplyProgram.coefficient_tape q.code)
  · rw [h.inner,List.length_ofFn]

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary.entry_of_query_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary.entry_of_query_oai
