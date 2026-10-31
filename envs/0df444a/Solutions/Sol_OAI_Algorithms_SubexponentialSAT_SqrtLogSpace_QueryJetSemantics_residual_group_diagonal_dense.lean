-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics.residual_group_diagonal_dense
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:21:09.129897+00:00
-- url     : https://prove2.me/submissions/5fc77a87-f9e0-4b39-a418-298ae22350aa

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S181

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsSparse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Executable support extraction for the normalized sparse squarefree jets.
Projection erases X after extracting one requested support, leaving U and Z.
All operations preserve the same bounded sparse representation. -/

namespace SubexponentialSAT.SqrtLog.Moments

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

theorem ringScalar_eq_atom (c : R) :
    ringScalar (V := V) c = Sparse.atom Index.origin c := by
  simp [ringScalar, Sparse.atom, Index.origin]

end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramHash
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Sparse clause-circuit evaluation for one hash row

The input is a list of supplied nonzero coefficients and width-k clause lists.
The evaluator visits those lists directly; it never builds a truth table on the
union of the clause scopes. Counters include measured variable lookup and ring
callbacks. Their primitive realization is a separate obligation, not inferred
from these counters. `Algebra` also admits canonical truncated operations, whose
decoder need not be a homomorphism into the untruncated polynomial ring.
-/

namespace SubexponentialSAT.SqrtLog.LeafProgram

open SubexponentialSAT.SubexpSymbolicCost

variable {V C A : Type*}

section PolynomialSemantics

variable {R : Type*} [CommRing R]

theorem clauseValue_eq_eval (value : V → R) (ls : List (SAT.Literal V)) :
    clauseValue (ringAlgebra R) value ls = MvPolynomial.eval value (clausePolynomial ls) := by
  induction ls with
  | nil => simp [clauseValue, clausePolynomial, ringAlgebra]
  | cons l ls ih =>
      change literalValue (ringAlgebra R) value l * clauseValue (ringAlgebra R) value ls = _
      simp only [clausePolynomial, List.map_cons, List.prod_cons, map_mul]
      rw [ih]
      congr 1
      cases hp : l.positive <;>
        simp [literalValue, ringAlgebra, HashInput.falsifyingLiteral, hp, sub_eq_add_neg]

theorem rowValue_eq_eval (decode : C → R) (value : V → R) (terms : SparseRow V C) :
    rowValue (ringAlgebra R) decode value terms =
      MvPolynomial.eval value (rowPolynomial decode terms) := by
  induction terms with
  | nil => simp [rowValue, rowPolynomial, ringAlgebra]
  | cons term terms ih =>
      rcases term with ⟨c, ls⟩
      change decode c * clauseValue (ringAlgebra R) value ls +
        rowValue (ringAlgebra R) decode value terms = _
      rw [clauseValue_eq_eval, ih]
      simp [rowPolynomial]

end PolynomialSemantics
end SubexponentialSAT.SqrtLog.LeafProgram

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

end SubexponentialSAT.SqrtLog.LeafProgram

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

theorem variableZ_eval (x : V → R) (hx : ∀ v, x v * x v = x v)
    (v : V) (p : Polynomial R) :
    (variableZ v p).map (Squarefree.evalHom x hx) = p * Polynomial.C (x v) := by
  ext j
  simp [variableZ_coeff, Polynomial.coeff_mul_C, Squarefree.weight]

theorem incidenceZ_eval [Fintype V] (x : V → R) (hx : ∀ v, x v * x v = x v)
    (row : V → Polynomial R) (theta beta : R) :
    (incidenceZ row theta beta).map (Squarefree.evalHom x hx) =
      Polynomial.C beta + ∑ v, rowDelta (row v) theta * Polynomial.C (x v) := by
  simp only [incidenceZ, Polynomial.map_add, Polynomial.map_C, eval_scalar, Polynomial.map_sum]
  simp_rw [variableZ_eval]


/-- Restoring the node value gives exactly the common shifted incidence row. -/
theorem incidenceZ_eval_row [Fintype V] (x : V → R) (hx : ∀ v, x v * x v = x v)
    (row : V → Polynomial R) (theta beta : R)
    (hbeta : beta = ∑ v, (row v).eval theta * x v) :
    (incidenceZ row theta beta).map (Squarefree.evalHom x hx) =
      ∑ v, (row v).comp (Polynomial.X + Polynomial.C theta) * Polynomial.C (x v) := by
  rw [incidenceZ_eval, hbeta, map_sum]
  simp only [rowDelta, sub_mul, ← Polynomial.C_mul]
  rw [Finset.sum_sub_distrib]
  ring

end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsFactors
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial naturality for the actual H-adic indicator expression. U
remains formal throughout; only its final retained coefficient sum is read. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
noncomputable section

variable {R : Type*} [CommRing R] {V : Type*} [DecidableEq V]

theorem jetEval_ringScalar (x : V → R) (hx : ∀ v, x v*x v=x v) (c : R) :
    Moments.jetEval x hx (Moments.ringScalar c) = Polynomial.C (Polynomial.C c) := by
  simp [Moments.jetEval,Moments.ringScalar,Squarefree.weight]

theorem polynomial_eval₂_C (P L : R[X]) :
    P.eval₂ (Polynomial.C.comp Polynomial.C) (Polynomial.C L) =
      Polynomial.C (P.comp L) := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => simp only [Polynomial.eval₂_add,Polynomial.add_comp,hp,hq,map_add]
  | monomial n c => simp [Polynomial.eval₂_monomial,Polynomial.monomial_comp]

theorem row_eq_fin (t : ℕ) (digits : Fin t → R[X]) (L : R[X]) :
    TotalOrder.row t (digitAt digits L) (IdempotentProgram.hValue L) =
      ∑ s : Fin t, Polynomial.monomial s.val
        ((digits s).comp L * IdempotentProgram.hValue L^s.val) := by
  unfold TotalOrder.row
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [digitAt,dite_eq_left (Fin.isLt _)]

theorem indicatorJet_eval (t : ℕ) (digits : Fin t → R[X])
    (H : Squarefree.Jet V R) (x : V → R) (hx : ∀ v, x v*x v=x v)
    (L : R[X]) (hH : Moments.jetEval x hx H=Polynomial.C L) :
    Moments.jetEval x hx (indicatorJet t digits H) =
      TotalOrder.row t (digitAt digits L) (IdempotentProgram.hValue L) := by
  unfold indicatorJet
  rw [map_sum,row_eq_fin]
  apply Finset.sum_congr rfl
  intro s _
  have hs : (Moments.jetEval x hx).comp Moments.ringScalar =
      Polynomial.C.comp Polynomial.C := by
    exact RingHom.ext (fun c => jetEval_ringScalar x hx c)
  have he := Polynomial.hom_eval₂ (digits s) Moments.ringScalar (Moments.jetEval x hx) H
  rw [hs,hH,polynomial_eval₂_C] at he
  rw [map_mul,map_mul,map_pow,map_pow,he]
  have hu : Moments.jetEval x hx (Polynomial.X : Squarefree.Jet V R) = Polynomial.X := by
    simp [Moments.jetEval]
  have hh : Moments.jetEval x hx (IdempotentProgram.hValue H) =
      Polynomial.C (IdempotentProgram.hValue L) := by
    simp only [IdempotentProgram.hValue,map_mul,map_sub,map_one,map_ofNat,hH]
  rw [hu,hh,← map_pow]
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul]
  ring

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ResidualEmbeddingSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Original literal identifiers may differ from the residual formal-variable
type. High-variable literals are branch constants, and the sparse row circuit
commutes with padding the remaining formal supports into ambient masks. -/
namespace SubexponentialSAT.SqrtLog.ResidualEmbedding

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree LeafProgram
noncomputable section

variable {I V W R : Type*} [DecidableEq V] [DecidableEq W] [CommRing R]

theorem scalarJet_eq_ringScalar (c : R) :
    scalarJet (V := V) c = Moments.ringScalar c :=
  (Moments.ringScalar_eq_atom c).symm

end
end SubexponentialSAT.SqrtLog.ResidualEmbedding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramAssignmentConcreteScoped
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Literal-scoped evaluation of the actual selected expression.  Missing
incidences impose no value condition: only literals read by that factor occur
in the hypotheses.  U remains a polynomial variable throughout. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

open Polynomial
open SubexponentialSAT SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps (Context)
open NodeSemantics
open scoped BigOperators

theorem clauseValue_congr {A V : Type*} (alg : Algebra A) (x y : V → A)
    (ls : List (SAT.Literal V)) (h : ∀ l ∈ ls, x l.variable=y l.variable) :
    clauseValue alg x ls=clauseValue alg y ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    have hl : literalValue alg x l=literalValue alg y l := by
      simp only [literalValue,h l (by simp)]
    simp only [clauseValue,hl]
    rw [ih (fun a ha => h a (by simp [ha]))]

theorem rowValue_congr {A V C : Type*} (alg : Algebra A) (decode : C → A)
    (x y : V → A) (ws : SparseRow V C)
    (h : ∀ w ∈ ws, ∀ l ∈ w.2, x l.variable=y l.variable) :
    rowValue alg decode x ws=rowValue alg decode y ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rcases w with ⟨c,ls⟩
    simp only [rowValue]
    rw [clauseValue_congr alg x y ls (h (c,ls) (by simp)),
      ih (fun a ha => h a (by simp [ha]))]

variable {R : Type*} [CommRing R] {n : ℕ}

theorem eval_source_clause_scoped {V : Type*} [DecidableEq V]
    (jet : Fin n → Squarefree.Jet V R) (path : Fin n → R[X])
    (x : V → R) (hx : ∀ v, x v*x v=x v)
    (clause : List (SAT.Literal (Fin n)))
    (hjet : ∀ l ∈ clause,
      Moments.jetEval x hx (jet l.variable)=Polynomial.C (path l.variable)) :
    Moments.jetEval x hx
      (MvPolynomial.eval jet (clausePolynomial (R:=Squarefree.Jet V R) clause)) =
      Polynomial.C (clauseValue (ringAlgebra R[X]) path clause) := by
  rw [← clauseValue_eq_eval (R:=Squarefree.Jet V R) jet clause,
    map_clauseValue (Moments.jetEval x hx) jet clause]
  rw [clauseValue_congr _ (fun v => Moments.jetEval x hx (jet v))
    (fun v => Polynomial.C (path v)) clause hjet]
  exact (map_clauseValue Polynomial.C path clause).symm

theorem eval_source_row_scoped {V : Type*} [DecidableEq V]
    (jet : Fin n → Squarefree.Jet V R) (path : Fin n → R[X])
    (x : V → R) (hx : ∀ v, x v*x v=x v) (ws : SparseRow (Fin n) R)
    (hjet : ∀ w ∈ ws, ∀ l ∈ w.2,
      Moments.jetEval x hx (jet l.variable)=Polynomial.C (path l.variable)) :
    Moments.jetEval x hx
      (MvPolynomial.eval jet (rowPolynomial (R:=Squarefree.Jet V R)
        (scalarJet (V:=V)) ws)) =
      Polynomial.C (rowValue (ringAlgebra R[X]) Polynomial.C path ws) := by
  rw [← rowValue_eq_eval (R:=Squarefree.Jet V R) (scalarJet (V:=V)) jet ws,
    map_rowValue (Moments.jetEval x hx) (scalarJet (V:=V)) jet ws]
  simp only [ResidualEmbedding.scalarJet_eq_ringScalar,jetEval_ringScalar]
  rw [rowValue_congr _ _ (fun v => Moments.jetEval x hx (jet v))
    (fun v => Polynomial.C (path v)) ws hjet]
  exact (map_rowValue Polynomial.C Polynomial.C path ws).symm

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ResidualEmbeddingIncidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Residual incidence rows may be stored at original ambient indices by
padding high coordinates with zero. Their jet and evaluation are unchanged. -/
namespace SubexponentialSAT.SqrtLog.ResidualEmbedding

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators
noncomputable section

variable {V A R : Type*} [Fintype V] [DecidableEq V]

theorem sum_padZero [AddCommMonoid A] (H : Finset V) (f : Free H → A) :
    (∑ v, padZero H f v) = ∑ v, f v := by
  calc
    _ = ∑ v ∈ (Finset.univ : Finset (Free H)).map (inclusion H), padZero H f v := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro v hv hn
      have hH : v ∈ H := by
        by_contra h
        exact hn (Finset.mem_map.mpr ⟨⟨v, h⟩, Finset.mem_univ _, rfl⟩)
      exact padZero_high H f v hH
    _ = _ := by
      rw [Finset.sum_map]
      simp only [inclusion_apply, padZero_low]

end
end SubexponentialSAT.SqrtLog.ResidualEmbedding

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

theorem completedRows_present (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (H : Finset (Fin n)) (f : ℕ) (j : Fin n) (v : ResidualEmbedding.Free H)
    (hj : (j.val,n+f)∈ps) :
    completedRows p ps P H f j v = fixedSourceRow p ps P n f j.val v.val := by
  simp only [completedRows,ite_eq_left hj]

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteResidual
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source jets live in the free-coordinate squarefree algebra even though
the runtime stores every key at its original ambient ID. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open DensePolynomialProgram LayoutProgram PerturbationAssembly Polynomial

variable {r Q d n : ℕ}


theorem residualJet_eval (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (H : Finset (Fin n)) (high : H → Bool)
    (theta : Coeff (baseWidth 3 p.t) d) (s : Fin 768 → List Bool)
    (x : ResidualEmbedding.Free H → Bool) (f : ℕ) (j : Fin n)
    (hpresent : (j.val,n+f)∈ps)
    (hbase : j∉H → baseline (n:=n) p ps P theta s f j.val =
      ∑ v : ResidualEmbedding.Free H,
        (fixedSourceRow p ps P n f j.val v.val).eval (p.ops.decode theta)*HashInput.boolValue (x v)) :
    Moments.jetEval (Squarefree.boolValue x) (Squarefree.boolValue_idempotent x)
      (residualJet p ps P H high theta s f j) =
    C ((NodeSemantics.branchPath H high (completedRows p ps P H) x f j).comp
      (X + C (p.ops.decode theta))) := by
  by_cases hj : j∈H
  · simp only [residualJet,dite_eq_left hj,NodeSemantics.jetEval_ringScalar,
      NodeSemantics.branchPath,Polynomial.C_comp]
  · simp only [residualJet,dite_eq_right hj,NodeSemantics.branchPath]
    simp_rw [completedRows_present p ps P H f j _ hpresent]
    have he := Moments.incidenceZ_eval_row (Squarefree.boolValue x)
      (Squarefree.boolValue_idempotent x)
      (fun v : ResidualEmbedding.Free H => fixedSourceRow p ps P n f j.val v.val)
      (p.ops.decode theta) _ (hbase hj)
    simp only [Moments.incidenceJet,Moments.jetEval,Polynomial.coe_mapRingHom,Polynomial.map_C]
    rw [he]
    congr 1
    simp only [Polynomial.sum_comp,Polynomial.mul_comp,Polynomial.C_comp,Squarefree.boolValue,HashInput.boolValue]

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteBaseline
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact integer bucket signatures restore the baseline used in a native
factor jet to the value of the shared fixed-high source path. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open DensePolynomialProgram SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open LayoutProgram PerturbationAssembly

variable {r Q d n : ℕ}

theorem sum_free_rows (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (H : Finset (Fin n)) (high : H → Bool) (a : ResidualEmbedding.Free H → Bool)
    (f j : ℕ) (theta : p.model.O p.t)
    (hzero : ∀ v∈H,fixedSourceRow p ps P n f j v=0) :
    (∑ v,(fixedSourceRow p ps P n f j v).eval theta *
      HashInput.boolValue (HighIncidence.glue H high a v)) =
    ∑ v : ResidualEmbedding.Free H,(fixedSourceRow p ps P n f j v.val).eval theta *
      HashInput.boolValue (a v) := by
  rw [← ResidualEmbedding.sum_padZero H]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v∈H
  · rw [hzero v hv,ResidualEmbedding.padZero_high H _ v hv]
    simp
  · simp only [ResidualEmbedding.padZero,not_false_eq_true,hv,dite_eq_left,HighIncidence.glue,dite_eq_right]

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryJetSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact source jets and decoded native coefficient words for reconstruction.
The optional marked factor is a violation query, and all free assignments remain. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics

open scoped BigOperators
open Polynomial OAI OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open LeafProgram LeafProgram.NodeSemantics
open IdempotentApplyProgram.Steps (Context)

section ResidualFactors

variable {V R : Type*} [DecidableEq V] [CommRing R]
  {p t n d : ℕ} [Fact p.Prime]

/-- Evaluation is required only at literals actually read by the selected ID.
The formal variable type may be the complement of the fixed high coordinates. -/
theorem residualValue_eval_scoped (ctx : Context p t n d)
    (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3 * t))
    (jet : ℕ → Fin n → Squarefree.Jet V R)
    (path : ℕ → Fin n → R[X]) (x : V → R) (hx : ∀ v, x v * x v = x v)
    (hashes : List (List (HashCircuitProgram.Native.Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (id : ℕ)
    (hhash : ∀ (hi : id < hashes.length), ∀ w ∈ hashes[id], ∀ l ∈ w.literals,
      Moments.jetEval x hx (jet id l.variable) = C (path id l.variable))
    (hmark : marked = true → id = hashes.length → ∀ l ∈ clause,
      Moments.jetEval x hx (jet id l.variable) = C (path id l.variable)) :
    Moments.jetEval x hx
      (AssignmentConcrete.residualValue ctx scalar basis code jet hashes marked clause id) =
      selectedExpression t (codeDigits ctx scalar code)
        (hashes.map (NativeSemantics.sourceTerms
          (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis)))
        marked clause path id := by
  unfold AssignmentConcrete.residualValue selectedExpression
  simp only [List.length_map]
  by_cases hi : id < hashes.length
  · simp only [dite_eq_left hi]
    apply indicatorJet_eval _ _ _ x hx
    simp only [hashPath, Fin.getElem_fin, List.getElem_map]
    apply AssignmentConcrete.eval_source_row_scoped (jet id) (path id) x hx
    intro term ht l hl
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht
    exact hhash hi w hw l hl
  · simp only [dite_eq_right hi]
    by_cases hm : (marked && decide (id = hashes.length)) = true
    · simp only [ite_eq_left hm]
      have hp : marked = true ∧ id = hashes.length := by simpa using hm
      exact AssignmentConcrete.eval_source_clause_scoped
        (jet id) (path id) x hx clause (hmark hp.1 hp.2)
    · simp only [ite_eq_right hm, map_one]

/-- The original canonical residual-factor product specializes to the actual
selected source expressions, with the same shared marker and Taylor cutoffs. -/
theorem residualProduct_specializeDense (ctx : Context p t n d)
    (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3 * t))
    (jet : ℕ → Fin n → Squarefree.Jet V R)
    (path : ℕ → Fin n → R[X]) (x : V → Bool)
    (hashes : List (List (HashCircuitProgram.Native.Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (ids : List ℕ) (J : ℕ)
    (hhash : ∀ id ∈ ids, ∀ (hi : id < hashes.length), ∀ w ∈ hashes[id], ∀ l ∈ w.literals,
      Moments.jetEval (Squarefree.boolValue x) (Squarefree.boolValue_idempotent x)
        (jet id l.variable) = C (path id l.variable))
    (hmark : marked = true → ∀ id ∈ ids, id = hashes.length → ∀ l ∈ clause,
      Moments.jetEval (Squarefree.boolValue x) (Squarefree.boolValue_idempotent x)
        (jet id l.variable) = C (path id l.variable)) :
    QueryEvaluation.specializeDense t J x (Squarefree.canonical t J
      ((ids.map (AssignmentConcrete.residualValue ctx scalar basis code
        jet hashes marked clause)).prod)) =
      Dense.ofPolynomial t J ((ids.map (selectedExpression t (codeDigits ctx scalar code)
        (hashes.map (NativeSemantics.sourceTerms
          (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis)))
        marked clause path)).prod) := by
  rw [specializeDense_canonical]
  change Dense.ofPolynomial t J (Moments.jetEval (Squarefree.boolValue x)
    (Squarefree.boolValue_idempotent x) _) = _
  rw [map_list_prod]
  apply congrArg (Dense.ofPolynomial t J)
  apply congrArg List.prod
  rw [List.map_map]
  apply List.map_congr_left
  intro id hid
  exact residualValue_eval_scoped ctx scalar basis code jet path
    (Squarefree.boolValue x) (Squarefree.boolValue_idempotent x) hashes marked clause id
    (hhash id hid) (fun hm he => hmark hm id hid he)

end ResidualFactors



section NativeReadout

open NodeConcrete MomentsProgram

variable {r Q n d : ℕ} {G : Type*} [Fintype G] [DecidableEq G]

/-- At the actual complete assignment, the stored baseline is the free-row
sum. Only low literal incidences require a source entry; high literals retain
their fixed bit. No supplied jet-evaluation service is used. -/
theorem residualJet_eval_diagonal (q : Factor.Spec r Q n d)
    (H : Finset (Fin n)) (high : H → Bool) (state : Fin 768 → List Bool)
    (x : ResidualEmbedding.Free H → Bool)
    (hstate : ∀ v : Fin n, (state 145).getD v.val false = HighIncidence.glue H high x v)
    (id : ℕ) (v : Fin n)
    (hpresent : v ∉ H → (v.val, n + id) ∈ q.ps)
    (hzero : ∀ w ∈ H, PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id v.val w = 0) :
    Moments.jetEval (Squarefree.boolValue x) (Squarefree.boolValue_idempotent x)
      (residualJet q.p q.ps q.packing H high q.theta state id v) =
      C (shift (q.p.ops.decode q.theta)
        (branchPath H high (completedRows q.p q.ps q.packing H) x id v)) := by
  by_cases hv : v ∈ H
  · simp only [residualJet, jetEval_ringScalar, branchPath, dite_eq_left hv, shift_C]
  · apply residualJet_eval q.p q.ps q.packing H high q.theta state x id v (hpresent hv)
    intro _
    change (∑ w : Fin n,
      (PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id v.val w).eval
        (q.p.ops.decode q.theta) * HashInput.boolValue ((state 145).getD w.val false)) = _
    simp only [hstate]
    exact sum_free_rows q.p q.ps q.packing H high x id v.val (q.p.ops.decode q.theta) hzero

/-- Diagonal specialization of the actual retained source factor product.
The premises are the physical assignment word and the actual literal scopes,
not evaluator outputs. The native lifting cutoff equals the fixed precision. -/
theorem residual_group_diagonal_dense_oai (q : Factor.Spec r Q n d) (hu : q.u = q.p.t)
    (H : Finset (Fin n)) (high : H → Bool) (state : Fin 768 → List Bool)
    (x : ResidualEmbedding.Free H → Bool)
    (hstate : ∀ v : Fin n, (state 145).getD v.val false = HighIncidence.glue H high x v)
    (ids : List ℕ)
    (hzero : ∀ id j (v : Fin n), v ∈ H →
      PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id j v = 0)
    (hhash : ∀ id ∈ ids, ∀ hi : id < (AssignmentConcrete.weightedHashes q).length,
      ∀ w ∈ (AssignmentConcrete.weightedHashes q)[id], ∀ l ∈ w.literals,
        l.variable ∉ H → (l.variable.val, n + id) ∈ q.ps)
    (hmark : q.marked = true → (AssignmentConcrete.weightedHashes q).length ∈ ids →
      ∀ l ∈ q.markedClause, l.variable ∉ H →
        (l.variable.val, n + (AssignmentConcrete.weightedHashes q).length) ∈ q.ps) :
    QueryEvaluation.specializeDense q.p.t q.J x
      (Squarefree.canonical q.u q.J ((ids.map
        (AssignmentConcrete.residualValue q.ctx (q.p.model.base q.p.t)
          (RingBasis.basis (q.p.model.F q.p.t)) q.code
          (residualJet q.p q.ps q.packing H high q.theta state)
          (AssignmentConcrete.weightedHashes q) q.marked q.markedClause)).prod)) =
      Dense.ofPolynomial q.p.t q.J ((ids.map
        (selectedExpression q.p.t (codeDigits q.ctx (q.p.model.base q.p.t) q.code)
          (decodedHashes q) q.marked q.markedClause
          (fun id v => shift (q.p.ops.decode q.theta)
            (branchPath H high (completedRows q.p q.ps q.packing H) x id v)))).prod) := by
  rw [hu]
  apply residualProduct_specializeDense q.ctx (q.p.model.base q.p.t)
    (RingBasis.basis (q.p.model.F q.p.t)) q.code
  · intro id hid hi w hw l hl
    exact residualJet_eval_diagonal q H high state x hstate id l.variable
      (hhash id hid hi w hw l hl) (hzero id l.variable.val)
  · intro hm id hid he l hl
    subst id
    exact residualJet_eval_diagonal q H high state x hstate _ l.variable
      (hmark hm hid l hl) (hzero _ l.variable.val)

end NativeReadout

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics.residual_group_diagonal_dense_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics.residual_group_diagonal_dense_oai
