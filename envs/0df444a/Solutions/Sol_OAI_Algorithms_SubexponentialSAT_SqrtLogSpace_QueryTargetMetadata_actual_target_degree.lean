-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.actual_target_degree
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:16:46.974643+00:00
-- url     : https://prove2.me/submissions/e7f5a77e-84f8-49d9-a6b9-288f52c6053e

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186
import Definitions.Def_OAIQ081S188
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_NodeSemantics_branch_target_degree

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact runtime parameter semantics. Every definition below uses natural
arithmetic; the executable refinements are separate from these specifications.
The original ambient dimension is retained through high-incidence branching. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram

/-- Division plus one gives strictly more Hermite conditions than the degree. -/
theorem guard_hermite (x : Input) (h : Guard x) :
    x.width * (produce x).R * (2 * x.factors + 3 * ((produce x).t - 1) + 1) <
      (produce x).Q * (produce x).J := by
  have hq : 0 < (produce x).Q := by have := h.2.2.2.2.2.2.1; omega
  exact Nat.lt_mul_div_succ _ hq

end SubexponentialSAT.SqrtLog.LeafParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramOutput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A R K : Type*} [CommRing A] [CommRing R] [CommRing K]

theorem digitPolynomial_degree (ops : RepresentedRing C A) {t : ℕ}
    (v : Fin (3*t) → C) (s : Fin t) :
    (digitPolynomial ops v s).natDegree < 3 := by
  have h : (digitPolynomial ops v s).natDegree ≤ 2 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro a _
    exact (Polynomial.natDegree_monomial_le _).trans (by have := a.isLt; omega)
  omega

end SubexponentialSAT.SqrtLog.IdempotentProgram

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramNativeSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact scopes of the physically stored sparse raw rows and optional original
marked clause. These definitions are shared by the machine and resource proofs. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram
namespace Complete

theorem scopes_length (t d : ℕ) {clauses : List (List Bool)} (codes : Fin clauses.length → List ℕ)
    (rows : RawTable.Rows clauses.length) (mark : Option (Fin clauses.length)) :
    (scopes (clauses := clauses) t d codes rows mark).length=rows.length+mark.isSome.toNat := by
  cases mark <;> simp [scopes]

end Complete
end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The exact polynomial computed by the native owner-fiber traversal. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT
open scoped BigOperators

variable {A : Type*}

section Polynomial
variable [CommRing A]

theorem list_sum_degree (ps : List (Polynomial A)) (R : ℕ)
    (h : ∀ p∈ps, p.natDegree ≤ R) : ps.sum.natDegree ≤ R := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      have hp := h p (by simp)
      have ht := ih (by intro q hq; exact h q (by simp [hq]))
      exact (Polynomial.natDegree_add_le p ps.sum).trans (max_le hp ht)

theorem ownerSum_degree (ps : List (ℕ × ℕ)) (owner : ℕ) (value : ℕ → Polynomial A) (R : ℕ)
    (h : ∀ i∈LayoutOwnerFiberProgram.fiberIndices owner 0 ps, (value i).natDegree ≤ R) :
    (ownerSum ps owner value).natDegree ≤ R := by
  apply list_sum_degree
  intro p hp
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
  exact h i hi

end Polynomial
end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramFamily
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Total original-coordinate source family computed by the native controller.
The missing-incidence branch is zero; required factor-scope incidences use
the exact packed row selected by the actual plan lookup. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

theorem sourceRowFamily_degree {A : Type*} [CommRing A] (ps : List (ℕ × ℕ))
    (ambient factor literal : ℕ) (source : ℕ → ℕ → Polynomial A) (owner R : ℕ)
    (h : ∀ row col, (source row col).natDegree ≤ R) :
    (sourceRowFamily ps ambient factor literal source owner).natDegree ≤ R := by
  unfold sourceRowFamily
  split_ifs
  · exact ownerSum_degree ps owner _ R (fun i _ => h _ i)
  · simp

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramSourceMeaning
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram

theorem packedSourceValue_degree {r Q d D : ℕ} (p : SourceBank.Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (row : Fin D) (i : ℕ) :
    (packedSourceValue p P row i).natDegree ≤ p.R := by
  unfold packedSourceValue
  split_ifs with hi
  · unfold packedValue
    split
    · split_ifs <;> simp
    · split
      · simp
      · split_ifs
        · exact LayoutScaledMatrices.sourceRow_degree _ _ _ _ _ _ _
        · simp
  · simp

theorem totalPackedSource_degree {r Q d D : ℕ} (p : SourceBank.Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (row col : ℕ) :
    (totalPackedSource p P row col).natDegree ≤ p.R := by
  unfold totalPackedSource
  split_ifs
  · exact packedSourceValue_degree p P _ col
  · simp

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramPreparedSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The source parameter object is derived from the executed query's numeric
bank, ring setup, and native head cache. Source order and jet order remain distinct. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram
open HashCircuitProgram HashCircuitProgram.Native NativeSemantics
noncomputable section

theorem numeric_t (q : LeafQueryFrontend.Query) (k : ℕ) (l : Fin 8 → ℕ)
    (hg : Guard (q.input k)) : (numeric q k l).val 33=(produce (q.input k)).t :=
  Execute.guardedModel_precision _ _ (Nat.ne_of_gt hg.2.2.1)

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The source rows used by the native factor callback retain their concrete
origin, degree, and original-coordinate support after incidence pullback. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram LayoutSourceRowsProgram PerturbationAssembly

variable {r Q d : ℕ}

theorem fixedSourceRow_degree (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (n f j : ℕ) (v : Fin n) :
    (fixedSourceRow p ps P n f j v).natDegree ≤ p.R :=
  sourceRowFamily_degree ps n f j _ v.val p.R (totalPackedSource_degree p P)

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The code-dependent expressions emitted by the actual assignment fold
are connected to the scalar U-expansion, without evaluating U at one. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open IdempotentApplyProgram.Steps (Context)
open AssignmentSemantics
noncomputable section

variable {p t n d : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]

theorem codeDigits_degree (ctx : Context p t n d) (scalar : ZMod (p^t) →+* R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t)) (s : Fin t) :
    (codeDigits ctx scalar code s).natDegree ≤ 2 := by
  apply Polynomial.natDegree_map_le.trans
  have := IdempotentProgram.digitPolynomial_degree
    (RingProgram.scalarRing p t ctx.modulus ctx.cache) code s
  omega

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

/-- The sparse source width bound survives coefficient lifting verbatim. -/
theorem liftedHashes_width {V : Type*} [Fintype V] [DecidableEq V]
    {d : ℕ} (a : RingModel.Data d) (t k : ℕ) (hashes : List (SparseRow V (ZMod 3)))
    (hw : ∀ ws∈hashes,∀ w∈ws,w.2.length ≤ k) :
    ∀ ws∈liftedHashes a t hashes,∀ w∈ws,w.2.length ≤ k := by
  intro ws hws w hw'
  obtain ⟨ls,hls,rfl⟩ := List.mem_map.mp hws
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw'
  exact hw ls hls v hv

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteTarget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A total source target with the original variable IDs. Missing incidences
are filled by identity rows only in this mathematical totalization; scoped
factor evaluation never reads those rows. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram PerturbationAssembly

variable {r Q d n : ℕ}

theorem completedRows_degree (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (H : Finset (Fin n)) (f : ℕ) (j : Fin n) (v : ResidualEmbedding.Free H) :
    (completedRows p ps P H f j v).natDegree ≤ p.R := by
  by_cases hj : (j.val,n+f)∈ps
  · simpa only [completedRows,ite_eq_left hj] using fixedSourceRow_degree p ps P n f j.val v.val
  · simp only [completedRows,ite_eq_right hj,Polynomial.natDegree_C,Nat.zero_le]

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

theorem sourceHashes_width (q : Factor.Spec r Q n d) (k : ℕ)
    (hwidth : ∀ clause∈q.source,clause.length ≤ k) :
    ∀ ws∈sourceHashes q,∀ w∈ws,w.2.length ≤ k := by
  intro ws hws w hw
  obtain ⟨terms,ht,rfl⟩ := List.mem_map.mp hws
  obtain ⟨term,hterm,rfl⟩ := List.mem_map.mp hw
  apply hwidth
  exact List.getElem_mem _

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteSpecBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open Polynomial
noncomputable section

variable {r Q n d : ℕ}

theorem specTarget_degree_le (q : Factor.Spec r Q n d)
    (H : Finset (Fin n)) (high : H → Bool) (k factors : ℕ)
    (hwidth : ∀ clause∈q.source,clause.length ≤ k) (hfactors : q.rows.length ≤ factors) :
    (specTarget q H high).natDegree ≤ k*q.p.R*(2*factors+3*(q.p.t-1)+1) := by
  unfold specTarget
  rw [decodedHashes_lifted]
  have hm : q.markedClause.length ≤ k := by
    unfold Factor.Spec.markedClause
    by_cases h : q.mark < q.source.length
    · rw [List.getElem?_eq_getElem h,Option.getD_some]
      exact hwidth _ (List.getElem_mem h)
    · rw [List.getElem?_eq_none (by omega)]
      simp
  have h := NodeSemantics.branch_target_degree H high (completedRows q.p q.ps q.packing H)
    q.p.t k q.p.R (completedRows_degree q.p q.ps q.packing H) _
    (NodeSemantics.codeDigits_degree q.ctx (q.p.model.base q.p.t) q.code)
    (NodeSemantics.liftedHashes q.p.model q.p.t (sourceHashes q)) q.marked q.markedClause
    (NodeSemantics.liftedHashes_width q.p.model q.p.t k _ (sourceHashes_width q k hwidth)) hm
  apply h.trans
  unfold Reconstruction.markedDegreeBound
  simp only [NodeSemantics.liftedHashes,List.length_map,sourceHashes_length]
  gcongr

theorem specTarget_degree_of_budget (q : Factor.Spec r Q n d)
    (H : Finset (Fin n)) (high : H → Bool) (k factors : ℕ)
    (hwidth : ∀ clause∈q.source,clause.length ≤ k) (hfactors : q.rows.length ≤ factors)
    (hbudget : k*q.p.R*(2*factors+3*(q.p.t-1)+1) < Q*q.J) :
    (specTarget q H high).natDegree < Q*q.J :=
  (specTarget_degree_le q H high k factors hwidth hfactors).trans_lt hbudget

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

/-- This local degree adapter uses the original source rows without changing
their multiplicity. The actual frontend discharges its budget below. -/
theorem native_degree_of_budget (H : Finset (Fin (s).n)) (high : H → Bool)
    (k factors : ℕ) (hwidth : ∀ c ∈ source, c.length ≤ k)
    (hfactors : q.rows.length ≤ factors)
    (hbudget : k * (s).R * (2 * factors + 3 * ((m).val 33 - 1) + 1) < (s).Q * J) :
    (specTarget spec H high).natDegree < (s).Q * J := by
  apply specTarget_degree_of_budget spec H high k factors hwidth
  · change (castRows (congrArg List.length hsource) q.rows).length ≤ factors
    rw [castRows_length]
    exact hfactors
  · exact hbudget

end Native

/-- The actual frontend includes every original row and any marked or neutral
factor in its measured factor budget. -/
theorem rows_le_input_factors (q : LeafQueryFrontend.Query) (k : ℕ) :
    q.rows.length ≤ (q.input k).factors := by
  change q.rows.length ≤ q.scopeRows.length +
    (LeafQueryFrontend.totals q.scopeRows q.forward).uncovered
  rw [LeafQueryFrontend.Query.scopeRows, HashScopeProgram.Complete.scopes_length]
  omega

section Addressed

variable (q : LeafQueryFrontend.Query) (hv : q.Valid) (k : ℕ)
    (hg : Guard (q.input k))
    (first : MulticolorTypes.Word (Query.packingProblem q k hg).r
      (Query.packingProblem q k hg).Q)
    (tail : List (MulticolorTypes.Word (Query.packingProblem q k hg).r
      (Query.packingProblem q k hg).Q))
    (node : Fin (Query.packingProblem q k hg).Q) (lengths : Fin 8 → ℕ)

local notation "s" => heads q k hg first tail node
local notation "m" => numeric q k lengths
local notation "ht" => Query.ring_precision_pos (q.input k) lengths hg
local notation "hd" => Query.ring_degree_pos (q.input k) lengths hg

/-- The executed jet order is strictly large enough for the actual target's
source width, full factor budget, and ambient precision. -/
theorem actual_degree_budget :
    k * (s).R * (2 * (q.input k).factors + 3 * ((m).val 33 - 1) + 1) <
      (s).Q * (m).val 42 := by
  rw [numeric_t q k lengths hg, numeric_J q k lengths hg]
  exact guard_hermite (q.input k) hg

variable (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect (heads q k hg first tail node).height
      (LeafHeadSetupProgram.unary (heads q k hg first tail node).R)
      (heads q k hg first tail node).width words)
    (M : SubexpPreparedQuartic.Modulus 3 ((numeric q k lengths).val 33))
    (cache : RingProgram.ScalarCache 3 ((numeric q k lengths).val 33))
    (half : RingProgram.ScalarCode 3 ((numeric q k lengths).val 33))
    (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced (numeric q k lengths)
      (Query.ring_degree_pos (q.input k) lengths hg) M cache half e)
    (source : List (List (SAT.Literal (Fin (heads q k hg first tail node).n))))
    (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source)

local notation "spec" => nativeSpecOfInputs s m ht hd words hc M cache half e hp
  (numeric_field q k lengths hg) q hv (Circuit.Model.val m 42)
  (numeric_order_pos q k lengths hg) source hsource

theorem actual_target_degree_oai (hwidth : ∀ c ∈ source, c.length ≤ k)
    (H : Finset (Fin (s).n)) (high : H → Bool) :
    (specTarget spec H high).natDegree < (s).Q * (m).val 42 :=
  native_degree_of_budget s m ht hd words hc M cache half e hp
    (numeric_field q k lengths hg) q hv ((m).val 42)
    (numeric_order_pos q k lengths hg) source hsource H high k (q.input k).factors
    hwidth (rows_le_input_factors q k)
    (actual_degree_budget q k hg first tail node lengths)

end Addressed

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.actual_target_degree_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.actual_target_degree_oai
