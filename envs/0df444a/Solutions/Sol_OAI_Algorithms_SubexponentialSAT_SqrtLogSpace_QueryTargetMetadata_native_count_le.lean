-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.native_count_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:30:04.399597+00:00
-- url     : https://prove2.me/submissions/1763d59d-e5fd-4e71-99c3-5a4979c1877d

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S181

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact fixed-high query count for the code-derived shared-order target. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
noncomputable section
attribute [local instance] Classical.propDecidable

variable {R K : Type*} [CommRing R] [CommRing K] [DecidableEq K]
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq K] in
theorem fixedHighCount_le (rho : R →+* K) (H : Finset V) (high : H → Bool)
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V)) :
    fixedHighCount rho H high hashes marked clause ≤ 2^Fintype.card (ResidualEmbedding.Free H) := by
  unfold fixedHighCount
  calc
    _ ≤ ∑ _x : ResidualEmbedding.Free H → Bool, 1 := by
      apply Finset.sum_le_sum
      intro x _
      split <;> omega
    _ = _ := by simp

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

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

omit [Fintype V] [DecidableEq V] in
theorem rowValue_map_coeff {C D S : Type*} [CommRing S]
    (lift : C → D) (decode : D → S) (value : V → S) (ws : SparseRow V C) :
    rowValue (ringAlgebra S) decode value (ws.map (fun w => (lift w.1,w.2))) =
      rowValue (ringAlgebra S) (decode ∘ lift) value ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [List.map_cons,rowValue,ih]; rfl

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Public source-specific facts for the native node/count join. The target,
its degree, and its exact constant count all refer to the same polynomial. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
noncomputable section

/-- The generic count reader's ambient bound follows from summing only free
assignments. The multiplicity m is the outer query allowance. -/
theorem model_count_bound {V : Type*} [Fintype V] [DecidableEq V]
    {d : ℕ} (a : RingModel.Data d) (t : ℕ) (ht : 0 < t)
    (H : Finset V) (high : H → Bool) (hashes : List (SparseRow V (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal V)) (m : ℕ) (hm : 1 ≤ m) :
    fixedHighCount (a.rho t ht) H high (liftedHashes a t hashes) marked clause ≤
      m*2^Fintype.card V := by
  classical
  apply (fixedHighCount_le (a.rho t ht) H high _ marked clause).trans
  have hc : Fintype.card (ResidualEmbedding.Free H) ≤ Fintype.card V :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  calc
    2^Fintype.card (ResidualEmbedding.Free H) ≤ 2^Fintype.card V := Nat.pow_le_pow_right (by decide) hc
    _ ≤ m*2^Fintype.card V := by simpa using Nat.mul_le_mul_right (2^Fintype.card V) hm

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteSpecBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open Polynomial
noncomputable section

variable {r Q n d : ℕ}

theorem specTarget_count_bound (q : Factor.Spec r Q n d)
    (H : Finset (Fin n)) (high : H → Bool) (m : ℕ) (hm : 1 ≤ m) :
    NodeSemantics.ternaryFixedHighCount H high (sourceHashes q) q.marked q.markedClause ≤ m*2^n := by
  rw [←NodeSemantics.fixedHighCount_lifted q.p.model q.p.t q.p.ht]
  simpa using NodeSemantics.model_count_bound q.p.model q.p.t q.p.ht H high
    (sourceHashes q) q.marked q.markedClause m hm

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

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

/-- A single marked query also counts a subset of the ambient assignments.
No clause multiplicity or positivity assumption is needed for this bound. -/
theorem native_count_le_oai (H : Finset (Fin (s).n)) (high : H → Bool) :
    NodeSemantics.ternaryFixedHighCount H high (sourceHashes spec)
      (spec).marked (spec).markedClause ≤ 2 ^ (s).n := by
  simpa only [one_mul] using specTarget_count_bound spec H high 1 le_rfl

end Native

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.native_count_le_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.native_count_le_oai
