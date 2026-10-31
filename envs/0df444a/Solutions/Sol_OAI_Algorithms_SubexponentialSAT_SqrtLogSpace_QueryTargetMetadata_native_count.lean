-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.native_count
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:28:05.809776+00:00
-- url     : https://prove2.me/submissions/1f11f5f9-b25d-4fb1-8f1d-be4852732227

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S181
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentProgram_binaryLiftWords_indicator
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_NodeConcrete_completedRows_origin
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_NodeSemantics_queryPolynomial_origin

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentTernary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The three-residue idempotent coefficient family.  The only coefficient
assumption is a supplied inverse `u` of two. -/

namespace SubexponentialSAT.SqrtLog.Idempotent

open Polynomial

variable {A O K : Type*} [CommRing A] [CommRing O] [CommRing K]

theorem map_two (φ : A →+* O) : φ (2 : A) = (2 : O) := by
  rw [show (2 : A) = 1 + 1 by ring, map_add, map_one]
  ring

end SubexponentialSAT.SqrtLog.Idempotent

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramLift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Integer representative lifting of the ternary selector coefficients.
Only reduction is a ring homomorphism. The lift itself is a finite choice of
0, 1, or 2, and no ring homomorphism from `ZMod 3` into the thickened ring is
assumed. All statements use the supplied irreducible polynomial. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram

section Naturality
variable {V C R S : Type*} [CommRing R] [CommRing S]

theorem map_literalValue (rho : R →+* S) (value : V → R) (l : SAT.Literal V) :
    rho (literalValue (ringAlgebra R) value l) =
      literalValue (ringAlgebra S) (fun v => rho (value v)) l := by
  cases hp : l.positive <;> simp [literalValue, ringAlgebra, hp]

theorem map_clauseValue (rho : R →+* S) (value : V → R) (ls : List (SAT.Literal V)) :
    rho (clauseValue (ringAlgebra R) value ls) =
      clauseValue (ringAlgebra S) (fun v => rho (value v)) ls := by
  induction ls with
  | nil => simp [clauseValue, ringAlgebra]
  | cons l ls ih =>
      change rho (literalValue (ringAlgebra R) value l * clauseValue (ringAlgebra R) value ls) =
        literalValue (ringAlgebra S) (fun v => rho (value v)) l *
          clauseValue (ringAlgebra S) (fun v => rho (value v)) ls
      rw [map_mul, map_literalValue, ih]

theorem map_rowValue (rho : R →+* S) (decode : C → R) (value : V → R)
    (terms : SparseRow V C) :
    rho (rowValue (ringAlgebra R) decode value terms) =
      rowValue (ringAlgebra S) (fun c => rho (decode c)) (fun v => rho (value v)) terms := by
  induction terms with
  | nil => simp [rowValue, ringAlgebra]
  | cons term rest ih =>
      rcases term with ⟨c, ls⟩
      change rho (decode c * clauseValue (ringAlgebra R) value ls +
        rowValue (ringAlgebra R) decode value rest) =
        rho (decode c) * clauseValue (ringAlgebra S) (fun v => rho (value v)) ls +
          rowValue (ringAlgebra S) (fun c => rho (decode c)) (fun v => rho (value v)) rest
      rw [map_add, map_mul, map_clauseValue, ih]

end Naturality

namespace TernaryLift

variable {d : ℕ} (a : RingModel.Data d) (t : ℕ)

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

omit [DecidableEq V] in
/-- Sparse-list version of the same bridge, matching the executable evaluator's
input representation and preserving empty rows and empty clauses. -/
theorem reduction_sparseRow (ht : 0 < t) (x : SAT.Assignment V)
    (terms : SparseRow V (ZMod 3)) :
    a.rho t ht
      (rowValue (ringAlgebra (a.O t)) (coefficient a t)
        (fun v => HashInput.boolValue (R := a.O t) (x v)) terms) =
      LiftRing.of a.residuePolynomial
        (rowValue (ringAlgebra (ZMod 3)) id
          (fun v => HashInput.boolValue (R := ZMod 3) (x v)) terms) := by
  rw [map_rowValue, map_rowValue]
  congr 1
  · funext c
    exact reduction_coefficient a t ht c
  · funext v
    cases h : x v <;> simp [HashInput.boolValue ]

end TernaryLift
end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native integer-representative coefficient lifting. The only arithmetic
performed by the machine is the audited dynamic padding/clearing routine. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.SubexpSymbolicCost
open SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularRingPrograms

theorem constantVector_decode (t d : ℕ) (ht : 0 < t) (a : RingModel.Data (d+1))
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (c : ZMod 3) :
    (RingProgram.modelRing t ht (Nat.succ_pos d) a M cache).decode
      (constantVector t d c) = LeafProgram.TernaryLift.coefficient a t c := by
  change (∑ i : Fin (d+1), SubexponentialSAT.LiftRing.of (a.F t)
    (wordValue 3 t (constantVector t d c i)) * RingBasis.basis (a.F t) i) = _
  rw [Fin.sum_univ_succ]
  simp [constantVector,RingProgram.liftCoefficientRun_correct t ht,
    SubexponentialSAT.SubexpPreparedQuartic.zeroWord_value,RingBasis.basis,
    LeafProgram.TernaryLift.coefficient]
  change (SubexponentialSAT.LiftRing.of (a.F t)) (c.val : ZMod (3^t)) = (c.val : a.O t)
  exact map_natCast _ _

end SubexponentialSAT.SqrtLog.HashInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramExpansion
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact bytes and coefficient meaning at the raw-row/interpreter boundary.
The full extension dimension is D; the assembler parameter is D-1. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Expansion
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open HashCircuitProgram.Native
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem coefficient_decode (t D : ℕ) (ht : 0 < t) (hD : 0 < D)
    (model : RingModel.Data D) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (c : ZMod 3) :
    (RingProgram.modelRing t ht hD model M cache).decode (coefficient t D c)=
      LeafProgram.TernaryLift.coefficient model t c := by
  cases D with
  | zero => omega
  | succ d => exact constantVector_decode t d ht model M cache c

theorem weightedRow_decode {n : ℕ} (t D : ℕ) (ht : 0 < t) (hD : 0 < D)
    (model : RingModel.Data D) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (encodedClauses source).length × ZMod 3)) :
    (weightedRow t D source terms).map
      (fun w => ((RingProgram.modelRing t ht hD model M cache).decode w.scalar,w.literals))=
      terms.map (fun term => (LeafProgram.TernaryLift.coefficient model t term.2,
        originalClause source term.1)) := by
  simp only [weightedRow,List.map_map]
  apply List.map_congr_left
  intro term _
  simp only [Function.comp_apply,weightedClause,coefficient_decode t D ht hD model M cache]

end SubexponentialSAT.SqrtLog.HashInputProgram.Expansion

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete coefficient choices over `ZMod (3^t)` and specialization to
the actual unramified counting ring. -/

namespace SubexponentialSAT.SqrtLog.Idempotent

open Polynomial
attribute [local instance] Classical.propDecidable

theorem prime_three_cases (a : ZMod 3) : a = 0 ∨ a = 1 ∨ a = 2 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

end SubexponentialSAT.SqrtLog.Idempotent

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The idempotent specification specialized to the execution-supplied
irreducible polynomial, rather than the semantic minimum-polynomial model. -/
namespace SubexponentialSAT.SqrtLog.Idempotent

open Polynomial
attribute [local instance] Classical.propDecidable

theorem model_residue_cases {d : ℕ} (a : RingModel.Data d) (y : a.E)
    (hy : ∃ c : ZMod 3, y = algebraMap (ZMod 3) a.E c) :
    y = 0 ∨ y = 1 ∨ y = 2 := by
  obtain ⟨c, rfl⟩ := hy
  rcases prime_three_cases c with h | h | h
  · left; simp only [h, map_zero]
  · right; left; simp only [h, map_one]
  · right; right; rw [h, map_two]

end SubexponentialSAT.SqrtLog.Idempotent

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Original IDs and fixed-high constants are retained in the source path.
All summation variables are free coordinates. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
noncomputable section

variable {R V : Type*} [CommRing R] [Fintype V] [DecidableEq V]

theorem branchPath_origin (H : Finset V) (high : H → Bool)
    (rows : ℕ → V → ResidualEmbedding.Free H → R[X])
    (horigin : ∀ i (v : ResidualEmbedding.Free H) w,
      (rows i v.val w).eval 0 = if w=v then 1 else 0)
    (x : ResidualEmbedding.Free H → Bool) (i : ℕ) (v : V) :
    (branchPath H high rows x i v).eval 0 =
      HashInput.boolValue (HighIncidence.glue H high x v) := by
  by_cases hv : v∈H
  · simp [branchPath,HighIncidence.glue,hv]
  · simp only [branchPath,dite_eq_right hv,Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C]
    have hr := horigin i ⟨v,hv⟩
    simp only [hr,ite_mul,zero_mul,one_mul]
    simp [HighIncidence.glue,hv]

omit [Fintype V] [DecidableEq V] in
theorem rowValue_map_coeff {C D S : Type*} [CommRing S]
    (lift : C → D) (decode : D → S) (value : V → S) (ws : SparseRow V C) :
    rowValue (ringAlgebra S) decode value (ws.map (fun w => (lift w.1,w.2))) =
      rowValue (ringAlgebra S) (decode ∘ lift) value ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [List.map_cons,rowValue,ih]; rfl

omit [Fintype V] [DecidableEq V] in
theorem liftedHashes_residue {d : ℕ} (a : RingModel.Data d) (t : ℕ) (ht : 0 < t)
    (hashes : List (SparseRow V (ZMod 3))) (x : V → Bool)
    (i : Fin (liftedHashes a t hashes).length) :
    a.rho t ht (sourceHash (liftedHashes a t hashes) x i)=0 ∨
      a.rho t ht (sourceHash (liftedHashes a t hashes) x i)=1 ∨
      a.rho t ht (sourceHash (liftedHashes a t hashes) x i)=2 := by
  apply Idempotent.model_residue_cases a
  have hi : (liftedHashes a t hashes)[i] ∈ liftedHashes a t hashes := List.getElem_mem i.isLt
  obtain ⟨ws,hws,he⟩ := List.mem_map.mp hi
  refine ⟨rowValue (ringAlgebra (ZMod 3)) id (fun v => HashInput.boolValue (x v)) ws,?_⟩
  change a.rho t ht (rowValue (ringAlgebra (a.O t)) id
    (fun v => HashInput.boolValue (x v)) (liftedHashes a t hashes)[i]) = _
  rw [← he,rowValue_map_coeff]
  exact TernaryLift.reduction_sparseRow a t ht x ws

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsCountSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The recovered constant counts the original ternary row constraints.
The extension-ring residue test introduces no additional acceptance rule. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem accepted_lifted_iff {d : ℕ} (a : RingModel.Data d) (t : ℕ) (ht : 0 < t)
    (hashes : List (SparseRow V (ZMod 3))) (marked : Bool) (clause : List (SAT.Literal V))
    (x : V → Bool) :
    accepted (a.rho t ht) (liftedHashes a t hashes) marked clause x ↔
      ternaryAccepted hashes marked clause x := by
  classical
  unfold accepted ternaryAccepted
  apply and_congr_left
  intro _
  have hrow (ws : SparseRow V (ZMod 3)) :
      a.rho t ht (rowValue (ringAlgebra (a.O t)) id
        (fun v => HashInput.boolValue (x v))
        (ws.map (fun w => (TernaryLift.coefficient a t w.1,w.2))))=0 ↔
      rowValue (ringAlgebra (ZMod 3)) id (fun v => HashInput.boolValue (x v)) ws=0 := by
    rw [rowValue_map_coeff]
    simp only [Function.id_comp]
    rw [TernaryLift.reduction_sparseRow a t ht]
    exact (LiftRing.of a.residuePolynomial).injective.eq_iff' (map_zero _)
  constructor
  · intro h ws hw
    apply (hrow ws).mp
    have hm : ws.map (fun w => (TernaryLift.coefficient a t w.1,w.2))∈liftedHashes a t hashes :=
      List.mem_map.mpr ⟨ws,hw,rfl⟩
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hm
    simpa only [sourceHash,Fin.getElem_fin,he] using h ⟨i,hi⟩
  · intro h i
    have hm := List.getElem_mem i.isLt
    obtain ⟨ws,hw,he⟩ := List.mem_map.mp (show (liftedHashes a t hashes)[i]∈liftedHashes a t hashes from hm)
    change a.rho t ht (rowValue _ id _ (liftedHashes a t hashes)[i])=0
    rw [← he]
    exact (hrow ws).mpr (h ws hw)

theorem fixedHighCount_lifted {d : ℕ} (a : RingModel.Data d) (t : ℕ) (ht : 0 < t)
    (H : Finset V) (high : H → Bool) (hashes : List (SparseRow V (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal V)) :
    fixedHighCount (a.rho t ht) H high (liftedHashes a t hashes) marked clause =
      ternaryFixedHighCount H high hashes marked clause := by
  classical
  unfold fixedHighCount ternaryFixedHighCount
  simp only [accepted_lifted_iff]

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The target uses the actual binary Newton coefficient array. Its constant
and degree statements do not replace it by a separate coefficient algorithm. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open Polynomial
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram PerturbationAssembly

variable {r Q d n : ℕ}

theorem binaryDigits_eq_code (p : SourceBank.Parameters r Q d)
    (M : SubexpPreparedQuartic.Modulus 3 p.t) (cache : RingProgram.ScalarCache 3 p.t)
    (half : RingProgram.ScalarCode 3 p.t)
    (ctx : IdempotentApplyProgram.Steps.Context 3 p.t n d) :
    binaryDigits p M cache half = NodeSemantics.codeDigits ctx (p.model.base p.t)
      (IdempotentProgram.binaryLiftWords p.t M cache half) := by
  rfl

theorem binaryTarget_count (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (M : SubexpPreparedQuartic.Modulus 3 p.t) (cache : RingProgram.ScalarCache 3 p.t)
    (half : RingProgram.ScalarCode 3 p.t) (hhalf : 2*wordValue 3 p.t half=1)
    (H : Finset (Fin n)) (high : H → Bool)
    (hashes : List (SparseRow (Fin n) (ZMod 3))) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) :
    (binaryTarget p ps P M cache half H high hashes marked clause).eval 0 =
      (NodeSemantics.ternaryFixedHighCount H high hashes marked clause : p.model.O p.t) := by
  classical
  rw [← NodeSemantics.fixedHighCount_lifted p.model p.t p.ht H high hashes marked clause]
  simp only [binaryTarget,NodeSemantics.target,Polynomial.eval_finsetSum,
    NodeSemantics.fixedHighCount,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro x _
  apply NodeSemantics.queryPolynomial_origin (p.model.rho p.t p.ht) 3 p.t
    (p.model.prime_power_zero p.t)
    (fun y hy => (p.model.rho_eq_zero_iff p.t p.ht y).mp hy)
  · exact NodeSemantics.branchPath_origin H high (completedRows p ps P H)
      (completedRows_origin p ps P H) x
  · intro i
    exact NodeSemantics.liftedHashes_residue p.model p.t p.ht hashes
      (HighIncidence.glue H high x) i
  · intro i
    simpa only [binaryDigits,Polynomial.eval_map] using
      IdempotentProgram.binaryLiftWords_indicator p.t M cache half hhalf
        (p.model.base p.t) (p.model.rho p.t p.ht) 3 (p.model.prime_power_zero p.t)
        (fun y hy => (p.model.rho_eq_zero_iff p.t p.ht y).mp hy)
        (NodeSemantics.sourceHash (NodeSemantics.liftedHashes p.model p.t hashes)
          (HighIncidence.glue H high x) i)
        (NodeSemantics.liftedHashes_residue p.model p.t p.ht hashes
          (HighIncidence.glue H high x) i)

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteSpecTarget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One source target is attached to the concrete factor specification. It
retains raw term multiplicity, optional marked violation, and shared U order. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open Polynomial
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native

variable {r Q d n : ℕ}

theorem decodedHashes_lifted (q : Factor.Spec r Q n d) :
    decodedHashes q=NodeSemantics.liftedHashes q.p.model q.p.t (sourceHashes q) := by
  unfold decodedHashes AssignmentConcrete.weightedHashes NodeSemantics.liftedHashes sourceHashes
  simp only [List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro terms _
  have h := HashInputProgram.Expansion.weightedRow_decode q.p.t d q.p.ht q.p.hd
    q.p.model q.p.modulus q.p.cache q.source terms
  simpa only [NativeSemantics.sourceTerms,List.map_map,Function.comp_def,
    LayoutProgram.SourceBank.Parameters.ops] using h

theorem specTarget_binary (q : Factor.Spec r Q n d)
    (M : SubexpPreparedQuartic.Modulus 3 q.p.t) (cache : RingProgram.ScalarCache 3 q.p.t)
    (half : RingProgram.ScalarCode 3 q.p.t)
    (hcode : q.code=IdempotentProgram.binaryLiftWords q.p.t M cache half)
    (H : Finset (Fin n)) (high : H → Bool) :
    specTarget q H high=binaryTarget q.p q.ps q.packing M cache half H high
      (sourceHashes q) q.marked q.markedClause := by
  unfold specTarget binaryTarget
  rw [hcode,decodedHashes_lifted,←binaryDigits_eq_code q.p M cache half q.ctx]

theorem specTarget_count (q : Factor.Spec r Q n d)
    (M : SubexpPreparedQuartic.Modulus 3 q.p.t) (cache : RingProgram.ScalarCache 3 q.p.t)
    (half : RingProgram.ScalarCode 3 q.p.t)
    (hcode : q.code=IdempotentProgram.binaryLiftWords q.p.t M cache half)
    (hhalf : 2*wordValue 3 q.p.t half=1)
    (H : Finset (Fin n)) (high : H → Bool) :
    (specTarget q H high).eval 0=
      (NodeSemantics.ternaryFixedHighCount H high (sourceHashes q) q.marked q.markedClause : q.p.model.O q.p.t) := by
  rw [specTarget_binary q M cache half hcode H high]
  exact binaryTarget_count q.p q.ps q.packing M cache half hhalf H high _ _ _

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTargetMetadata
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The polynomial reconstructed by the native query is the target of its
actual generated ternary ring and idempotent code. Its constant term is the
exact marked or unmarked count; the executed parameter bank supplies both
the interpolation budget and sufficient precision. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata

open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog LeafParametersProgram LeafProgram
open LeafProgram.PreparedSource LeafProgram.NodeConcrete

attribute [local irreducible] Execute.guardedModel

section Native

variable (s : LeafHeadSetupProgram.Native.Inputs)
    (m : Circuit.Model) (ht : 0 < (m).val 33) (hd : 0 < (m).val 34)
    (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect (s).height
      (LeafHeadSetupProgram.unary (s).R) (s).width words)
    (M : SubexpPreparedQuartic.Modulus 3 ((m).val 33))
    (cache : RingProgram.ScalarCache 3 ((m).val 33))
    (half : RingProgram.ScalarCode 3 ((m).val 33))
    (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : (s).Q < 3 ^ ((m).val 34))
    (q : LeafQueryFrontend.Query) (hv : q.Valid) (J : ℕ) (hJ : 0 < J)
    (source : List (List (SAT.Literal (Fin (s).n))))
    (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source)

local notation "spec" => nativeSpecOfInputs s m ht hd words hc M cache half e hp
  hfield q hv J hJ source hsource

/-- The actual producer's inverse of two makes the generated idempotent
readout an exact count in the represented ring. -/
theorem native_count_oai (H : Finset (Fin (s).n)) (high : H → Bool) :
    (specTarget spec H high).eval 0 =
      (NodeSemantics.ternaryFixedHighCount H high (sourceHashes spec)
        (spec).marked (spec).markedClause : (spec).p.model.O (spec).p.t) :=
  specTarget_count spec (generatedCode hp).modulus (generatedCode hp).cache
    (generatedCode hp).half rfl (generatedCode hp).inverse H high

end Native

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.native_count_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.native_count_oai
