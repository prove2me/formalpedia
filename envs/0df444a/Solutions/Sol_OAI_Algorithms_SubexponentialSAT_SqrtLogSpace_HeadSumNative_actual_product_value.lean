-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative.actual_product_value
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:07:45.004768+00:00
-- url     : https://prove2.me/submissions/382d8b88-1697-4d84-bacc-1defcc5d2eec

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Sparse squarefree polynomials. The index monoid multiplies by support union,
so the coefficient algebra imposes X_v^2 = X_v without enumerating all supports. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

variable {V R : Type*}

noncomputable section

variable [DecidableEq V] [CommSemiring R]

theorem eval_eq_sum (x : V → R) (hx : ∀ v, x v * x v = x v) (f : Poly V R) :
    evalHom x hx f = f.coeff.sum (fun s c => c * weight x s.vars) := by
  calc
    evalHom x hx f = evalHom x hx (f.coeff.sum MonoidAlgebra.single) := by
      rw [MonoidAlgebra.sum_coeff_single]
    _ = f.coeff.sum (fun s c => c * weight x s.vars) := by
      rw [map_finsuppSum]
      apply Finsupp.sum_congr
      intro a ha
      exact eval_monomial x hx a.vars (f.coeff a)

end
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ResidualEmbedding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Injective padding of residual squarefree variables into their original
ambient coordinate universe. This is a semantic map, not runtime renumbering. -/
namespace SubexponentialSAT.SqrtLog.ResidualEmbedding

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators
noncomputable section

variable {V W R : Type*} [DecidableEq V] [DecidableEq W] [CommSemiring R]

theorem supportMap_injective (e : V ↪ W) : Function.Injective (supportMap e) := by
  intro a b h
  apply Support.ext
  exact Finset.map_injective e (congrArg Support.vars h)

@[simp] theorem coeff_poly (e : V ↪ W) (s : Finset V) (f : Poly V R) :
    coeff (s.map e) (poly e f) = coeff s f :=
  Finsupp.mapDomain_apply (supportMap_injective e) f.coeff
    (⟨s⟩ : Support V)

theorem eval_poly (e : V ↪ W) (x : W → R) (hx : ∀ w, x w * x w = x w)
    (f : Poly V R) :
    evalHom x hx (poly e f) =
      evalHom (fun v => x (e v)) (fun v => hx (e v)) f := by
  rw [eval_eq_sum, eval_eq_sum]
  change (Finsupp.mapDomain (supportMap e) f.coeff).sum
      (fun s c => c * weight x s.vars) =
    f.coeff.sum (fun s c => c * weight (fun v => x (e v)) s.vars)
  rw [Finsupp.sum_mapDomain_index_inj (supportMap_injective e)]
  apply Finsupp.sum_congr
  intro a _
  change f.coeff a * weight x (a.vars.map e) =
    f.coeff a * weight (fun v => x (e v)) a.vars
  rw [weight_map]

@[simp] theorem jetCoeff_jet (e : V ↪ W) (s : Finset V) (f : Jet V R) :
    Moments.jetCoeff ⟨s.map e⟩ (jet e f) = Moments.jetCoeff ⟨s⟩ f := by
  apply Polynomial.ext
  intro u
  apply Polynomial.ext
  intro z
  simp

theorem eval_jet (e : V ↪ W) (x : W → R) (hx : ∀ w, x w * x w = x w)
    (f : Jet V R) :
    Moments.jetEval x hx (jet e f) =
      Moments.jetEval (fun v => x (e v)) (fun v => hx (e v)) f := by
  apply Polynomial.ext
  intro u
  apply Polynomial.ext
  intro z
  simp only [Moments.jetEval_coeff, jet_coeff]
  exact eval_poly e x hx _

end
end SubexponentialSAT.SqrtLog.ResidualEmbedding

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

end SubexponentialSAT.SqrtLog.Moments

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

theorem row_source_jet (e : V ↪ W) (value : I → Jet V R) (terms : SparseRow I R) :
    MvPolynomial.eval (fun i => jet e (value i))
      (rowPolynomial (R := Jet W R) scalarJet terms) =
    jet e (MvPolynomial.eval value (rowPolynomial (R := Jet V R) scalarJet terms)) := by
  have h := map_rowValue (V := I) (C := R) (R := Jet V R) (S := Jet W R)
    (jet e) (scalarJet (V := V) (R := R)) value terms
  simp only [jet_scalarJet, rowValue_eq_eval] at h
  exact h.symm

end
end SubexponentialSAT.SqrtLog.ResidualEmbedding

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

theorem indicatorPolynomial_eq (ctx : Context p t n d) (scalar : ZMod (p^t) →+* R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    (H : Squarefree.Jet (Fin n) R) :
    AssignmentSemantics.indicatorPolynomial ctx scalar code H =
      indicatorJet t (codeDigits ctx scalar code) H := by
  have hu : Squarefree.Sparse.atom (IdempotentApplyProgram.Multiplier.uKey n) (1:R) =
      (Polynomial.X : Squarefree.Jet (Fin n) R) := by
    simp [Squarefree.Sparse.atom,IdempotentApplyProgram.Multiplier.uKey,
      show Squarefree.monomial (V:=Fin n) ∅ (1:R) = 1 from rfl,
      ← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [AssignmentSemantics.indicatorPolynomial,indicatorJet,hu,codeDigits,
    Polynomial.eval₂_map]

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramAssignmentConcreteEmbedding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Selected factors may have ambient literal IDs but free formal variables.
Embedding is performed on the polynomial itself, never through a chosen
stored representation. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

open Polynomial _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree NodeSemantics
open SubexponentialSAT SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps (Context)
open scoped BigOperators

variable {V W I R : Type*} [DecidableEq V] [DecidableEq W] [CommRing R]

theorem indicatorJet_embedding (e : V ↪ W) (t : ℕ) (digits : Fin t → R[X])
    (F : Jet V R) :
    ResidualEmbedding.jet e (indicatorJet t digits F) =
      indicatorJet t digits (ResidualEmbedding.jet e F) := by
  unfold indicatorJet
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hc : (ResidualEmbedding.jet (R:=R) e).comp Moments.ringScalar =
      Moments.ringScalar := by
    apply RingHom.ext
    intro c
    exact ResidualEmbedding.jet_ringScalar e c
  have he := Polynomial.hom_eval₂ (digits s) Moments.ringScalar (ResidualEmbedding.jet e) F
  rw [hc] at he
  have hu : ResidualEmbedding.jet e (Polynomial.X : Jet V R) = Polynomial.X := by
    simp [ResidualEmbedding.jet]
  have hh : ResidualEmbedding.jet e (IdempotentProgram.hValue F) =
      IdempotentProgram.hValue (ResidualEmbedding.jet e F) := by
    simp only [IdempotentProgram.hValue,map_mul,map_sub,map_one,map_ofNat]
  simp only [map_mul,map_pow,hu,he,hh]

theorem clause_source_embedding (e : V ↪ W) (value : I → Jet V R)
    (ls : List (SAT.Literal I)) :
    MvPolynomial.eval (fun i => ResidualEmbedding.jet e (value i))
      (clausePolynomial (R:=Jet W R) ls) =
    ResidualEmbedding.jet e (MvPolynomial.eval value (clausePolynomial (R:=Jet V R) ls)) := by
  have h := map_clauseValue (V:=I) (R:=Jet V R) (S:=Jet W R) (ResidualEmbedding.jet e) value ls
  simpa only [clauseValue_eq_eval] using h.symm

variable {p t n d : ℕ} [Fact p.Prime]

theorem selectedValue_embedding (e : V ↪ Fin n) (ctx : Context p t n d)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    (jfree : ℕ → Fin n → Jet V R) (jamb : ℕ → Fin n → Jet (Fin n) R)
    (hj : ∀ id v, jamb id v=ResidualEmbedding.jet e (jfree id v))
    (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (id : ℕ) :
    AssignmentSemantics.selectedValue ctx scalar basis code jamb hashes marked clause id =
      ResidualEmbedding.jet e (residualValue ctx scalar basis code jfree hashes marked clause id) := by
  have he : jamb = fun id v => ResidualEmbedding.jet e (jfree id v) := by
    funext id v
    exact hj id v
  rw [he]
  unfold AssignmentSemantics.selectedValue residualValue
  by_cases h : id < hashes.length
  · simp only [dite_eq_left h]
    rw [indicatorPolynomial_eq,ResidualEmbedding.row_source_jet,← indicatorJet_embedding]
  · simp only [dite_eq_right h]
    split
    · exact clause_source_embedding e (jfree id) clause
    · exact (map_one (ResidualEmbedding.jet e)).symm

theorem canonical_product_embedding (e : V ↪ Fin n) (ctx : Context p t n d)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    (jfree : ℕ → Fin n → Jet V R) (jamb : ℕ → Fin n → Jet (Fin n) R)
    (hj : ∀ id v, jamb id v=ResidualEmbedding.jet e (jfree id v))
    (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (ids : List ℕ) :
    canonical ctx.u ctx.J
      ((ids.map (AssignmentSemantics.selectedValue ctx scalar basis code jamb hashes marked clause)).prod) =
    ResidualEmbedding.jet e (canonical ctx.u ctx.J
      ((ids.map (residualValue ctx scalar basis code jfree hashes marked clause)).prod)) := by
  rw [ResidualEmbedding.jet_canonical]
  congr 1
  rw [map_list_prod (ResidualEmbedding.jet e)]
  apply congrArg List.prod
  rw [List.map_map]
  apply List.map_congr_left
  intro id hi
  exact selectedValue_embedding e ctx scalar basis code jfree jamb hj hashes marked clause id

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

variable [CommRing R]

/-- This version is polymorphic in both variable universes. -/
theorem map_variableZ {U W : Type*} [DecidableEq U] [DecidableEq W]
    (e : U ↪ W) (v : U) (p : Polynomial R) :
    (Moments.variableZ v p).map (poly e) = Moments.variableZ (e v) p := by
  ext j
  simp [Moments.variableZ_coeff]

theorem incidenceZ_pad (H : Finset V) (row : Free H → Polynomial R) (theta beta : R) :
    (Moments.incidenceZ row theta beta).map (poly (inclusion H)) =
      Moments.incidenceZ (padZero H row) theta beta := by
  have hscalar : poly (inclusion H) (Squarefree.scalar beta) = Squarefree.scalar beta := by
    change poly (inclusion H) (monomial ∅ beta) = monomial ∅ beta
    simp
  simp only [Moments.incidenceZ, Polynomial.map_add, Polynomial.map_C,
    hscalar, Polynomial.map_sum, map_variableZ]
  congr 1
  symm
  have h : (fun v => Moments.variableZ v (Moments.rowDelta (padZero H row v) theta)) =
      padZero H (fun v => Moments.variableZ v.val (Moments.rowDelta (row v) theta)) := by
    funext v
    by_cases hv : v ∉ H
    · simp [padZero, hv]
    · simp [padZero, hv, Moments.rowDelta, Moments.variableZ]
  rw [h, sum_padZero]
  simp only [inclusion_apply]

theorem incidenceJet_pad (H : Finset V) (row : Free H → Polynomial R) (theta beta : R) :
    jet (inclusion H) (Moments.incidenceJet row theta beta) =
      Moments.incidenceJet (padZero H row) theta beta := by
  simp [jet, Moments.incidenceJet, incidenceZ_pad]

end
end SubexponentialSAT.SqrtLog.ResidualEmbedding

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

theorem fixedSourceRow_pad (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (H : Finset (Fin n)) (f j : ℕ)
    (hzero : ∀ v∈H, fixedSourceRow p ps P n f j v=0) :
    ResidualEmbedding.padZero H
      (fun v : ResidualEmbedding.Free H => fixedSourceRow p ps P n f j v.val) =
      fixedSourceRow p ps P n f j := by
  funext v
  by_cases hv : v∈H
  · rw [ResidualEmbedding.padZero_high H _ v hv,hzero v hv]
  · exact ResidualEmbedding.padZero_low H _ ⟨v,hv⟩

theorem factorJet_embedding (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (H : Finset (Fin n)) (high : H → Bool)
    (theta : Coeff (baseWidth 3 p.t) d) (s : Fin 768 → List Bool)
    (f : ℕ) (j : Fin n)
    (hmask : (s 702).getD j.val false = decide (j∈H))
    (hhigh : ∀ hj:j∈H,(s 703).getD j.val false=high ⟨j,hj⟩)
    (hzero : ∀ v∈H,fixedSourceRow p ps P n f j.val v=0) :
    Factor.factorJet p ps P n f j.val theta s =
      ResidualEmbedding.jet (ResidualEmbedding.inclusion H)
        (residualJet p ps P H high theta s f j) := by
  unfold Factor.factorJet sourceIncidenceJet
  simp only [Factor.choiceStore,show (574:Fin 768)≠546 by decide,
    show (575:Fin 768)≠546 by decide,show (575:Fin 768)≠574 by decide,
    ite_false,ite_true, if_true,hmask]
  by_cases hj : j∈H
  · simp only [residualJet,dite_eq_left hj]
    simp only [hj,decide_true,ite_true, if_true,hhigh hj]
    rw [ResidualEmbedding.jet_ringScalar]
    exact (Moments.ringScalar_eq_atom _).symm
  · simp only [residualJet,dite_eq_right hj]
    simp only [hj,decide_false,Bool.false_eq_true,ite_false]
    rw [ResidualEmbedding.incidenceJet_pad,fixedSourceRow_pad p ps P H f j.val hzero]
    rfl


end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramAssignmentConcrete
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The relational, actually executed assignment fold has the same value as
the selected-factor expression used by the node proof.  This bridge chooses
no raw representative and retains the shared U and T truncations. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

open SubexponentialSAT SubexpLiftRing SubexpQuarticRing MomentsProgram MomentsAssembly
open HashCircuitProgram HashCircuitProgram.Native
open scoped BigOperators

variable {r Q n d : ℕ}

/-- Dispatch agrees also on the marked ID and on every neutral ID.  Raw
tuple multiplicity is preserved in weightedHashes. -/
theorem value_eq_selectedValue (q : Factor.Spec r Q n d)
    (s : Fin 768 → List Bool) (id : ℕ) :
    q.value s id = AssignmentSemantics.selectedValue q.ctx
      (LiftRing.of (q.p.model.F q.p.t)) (RingBasis.basis (q.p.model.F q.p.t))
      q.code (sourceJets q s) (weightedHashes q) q.marked q.markedClause id := by
  unfold Factor.Spec.value AssignmentSemantics.selectedValue weightedHashes
  simp only [List.length_map]
  by_cases h : id < q.rows.length
  · simp only [dite_eq_left h, List.getElem_map]
    rfl
  · simp only [dite_eq_right h]
    split <;> rfl

theorem value_function (q : Factor.Spec r Q n d) (s : Fin 768 → List Bool) :
    q.value s = AssignmentSemantics.selectedValue q.ctx
      (LiftRing.of (q.p.model.F q.p.t)) (RingBasis.basis (q.p.model.F q.p.t))
      q.code (sourceJets q s) (weightedHashes q) q.marked q.markedClause := by
  funext id
  exact value_eq_selectedValue q s id

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSourceLocality
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete source locality for the streamed head evaluation.
The source correspondence is `NodeConcrete.fixedSourceRow_baseline_eq` in
LeafProgramNodeConcretePlan, the actual residualJet in
LeafProgramNodeConcreteResidual, and residualProduct in
LeafProgramNodeConcreteResidualProduct. Fixed-high bits cancel in the full
integer signatures; every correction specialization uses one common U. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog



open OAI SubexpLiftRing SubexpQuarticRing
open MulticolorTypes Subexp.ConstructivePacking
open LeafProgram LeafProgram.NodeConcrete
open LayoutProgram PerturbationAssembly Polynomial

noncomputable section

variable {r Q d n : ℕ}

/-- Source factor semantics read only the actual ambient assignment word;
all caches and physical scratch stacks are irrelevant to the polynomial. -/
theorem sourceProduct_assignment_word (q : Factor.Spec r Q n d)
    (H : Finset (Fin n)) (high : H → Bool)
    (a b : Fin 768 → List Bool) (h145 : a 145=b 145) (ids : List ℕ) :
    sourceProduct q H high a ids=sourceProduct q H high b ids := by
  have he : residualJet q.p q.ps q.packing H high q.theta a =
      residualJet q.p q.ps q.packing H high q.theta b := by
    funext f j
    unfold residualJet
    split
    · rfl
    · apply congrArg (Moments.incidenceJet _ (q.p.ops.decode q.theta))
      simp only [baseline,h145]
  unfold sourceProduct
  rw [he]

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryJetSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

omit [Fact p.Prime] in
/-- Specializing an embedded free-variable jet only reads the correction bits
on the image. In particular, the chosen high-coordinate correction bits cannot
change the dense value. -/
theorem specializeDense_jet_embedding {W : Type*} [DecidableEq W]
    (e : V ↪ W) (t J : ℕ) (ambient : W → Bool) (free : V → Bool)
    (hfree : ∀ v, ambient (e v) = free v) (f : Squarefree.Jet V R) :
    QueryEvaluation.specializeDense t J ambient (ResidualEmbedding.jet e f) =
      QueryEvaluation.specializeDense t J free f := by
  change Dense.ofPolynomial t J (Moments.jetEval (Squarefree.boolValue ambient)
    (Squarefree.boolValue_idempotent ambient) (ResidualEmbedding.jet e f)) =
      Dense.ofPolynomial t J (Moments.jetEval (Squarefree.boolValue free)
        (Squarefree.boolValue_idempotent free) f)
  apply congrArg (Dense.ofPolynomial t J)
  rw [ResidualEmbedding.eval_jet]
  have hv : (fun v => (Squarefree.boolValue ambient (e v) : R)) = Squarefree.boolValue free := by
    funext v
    simp only [Squarefree.boolValue, hfree]
  simp only [hv]

end ResidualFactors



section NativeReadout

open NodeConcrete MomentsProgram

variable {r Q n d : ℕ} {G : Type*} [Fintype G] [DecidableEq G]

/-- The actual arbitrary-state factor product specializes to its free-variable
source product. The native state supplies the high mask and bits directly;
no legacy assignment context or chosen raw representative is introduced. -/
theorem actualProduct_specializeDense (q : Factor.Spec r Q n d)
    (H : Finset (Fin n)) (high : H → Bool) (state : Fin 768 → List Bool)
    (hmask : ∀ v : Fin n, (state 702).getD v.val false = decide (v ∈ H))
    (hbits : ∀ v : H, (state 703).getD v.val.val false = high v)
    (hzero : ∀ id j (v : Fin n), v ∈ H →
      PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id j v = 0)
    (ids : List ℕ) (ambientU : Fin n → Bool) (U : ResidualEmbedding.Free H → Bool)
    (hU : ∀ v, ambientU v.val = U v) :
    QueryEvaluation.specializeDense q.u q.J ambientU
      (Squarefree.canonical q.u q.J ((ids.map (q.value state)).prod)) =
      QueryEvaluation.specializeDense q.u q.J U
        (Squarefree.canonical q.u q.J ((ids.map
          (AssignmentConcrete.residualValue q.ctx (q.p.model.base q.p.t)
            (RingBasis.basis (q.p.model.F q.p.t)) q.code
            (residualJet q.p q.ps q.packing H high q.theta state)
            (AssignmentConcrete.weightedHashes q) q.marked q.markedClause)).prod)) := by
  have hj (id : ℕ) (v : Fin n) :
      AssignmentConcrete.sourceJets q state id v =
        ResidualEmbedding.jet (ResidualEmbedding.inclusion H)
          (residualJet q.p q.ps q.packing H high q.theta state id v) :=
    factorJet_embedding q.p q.ps q.packing H high q.theta state id v
      (hmask v) (fun hv => hbits ⟨v, hv⟩) (hzero id v.val)
  have he := AssignmentConcrete.canonical_product_embedding (ResidualEmbedding.inclusion H)
    q.ctx (q.p.model.base q.p.t) (RingBasis.basis (q.p.model.F q.p.t)) q.code
    (residualJet q.p q.ps q.packing H high q.theta state)
    (AssignmentConcrete.sourceJets q state) hj
    (AssignmentConcrete.weightedHashes q) q.marked q.markedClause ids
  rw [AssignmentConcrete.value_function]
  exact (congrArg (QueryEvaluation.specializeDense q.u q.J ambientU) he).trans
    (specializeDense_jet_embedding (ResidualEmbedding.inclusion H)
      q.u q.J ambientU U hU _)

end NativeReadout

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Correctness of the fixed head rescan. The invariant retains the current
normalized dictionary and the actual immutable source words. Its compact
boundary is reused after every candidate; no execution service is assumed. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative
open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram SqrtLog.MomentsProgram
open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadSumProgram
open HeadIdentifierProgram BucketTupleProgram.Concrete
open QueryTupleState (masterPorts QueryMasterFrame QueryReady)
open scoped BigOperators

noncomputable section

/-- Exact physical high/mask words and the actual ambient overlay identify the
whole assignment product with the original free-variable source expression. -/
theorem actual_product_value_oai {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (H : Finset (Fin n)) (high : H → Bool) (U : Finset (Fin n))
    (x : ResidualEmbedding.Free H → Bool) (a : HeadSumProgram.Data) (ids : List ℕ)
    (hmask : a.stacks 702 = List.ofFn (fun v : Fin n => decide (v ∈ H)))
    (hbits : a.stacks 703 = List.ofFn (fun v : Fin n => if h : v ∈ H then high ⟨v,h⟩ else false))
    (hU : a.stacks 857 = List.ofFn (fun v : Fin n => decide (v ∈ U)))
    (h145 : a.stacks 145 = List.ofFn (HighIncidence.glue H high x))
    (hzero : ∀ id j (v : Fin n), v ∈ H →
      PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id j v = 0) :
    QueryEvaluation.specializeDense q.u q.J
      (fun v => decide (v ∈ Squarefree.decodeMask n (a.stacks 857)))
      (Squarefree.canonical q.u q.J
        ((ids.map (q.value (a.stacks ∘ FactorAssignmentProgram.lowStack))).prod)) =
    QueryEvaluation.specializeDense q.u q.J
      (fun v : ResidualEmbedding.Free H => decide (v.val ∈ U))
      (HeadSourceLocality.sourceProduct q H high (HeadSourceLocality.stateFor H high x) ids) := by
  have hm (v : Fin n) : ((a.stacks ∘ FactorAssignmentProgram.lowStack) 702).getD v.val false =
      decide (v ∈ H) := by
    change (a.stacks 702).getD v.val false = _
    simp [hmask, List.getD_eq_getElem?_getD, v.isLt]
  have hb (v : H) : ((a.stacks ∘ FactorAssignmentProgram.lowStack) 703).getD v.val.val false = high v := by
    change (a.stacks 703).getD v.val.val false = _
    simp [hbits, List.getD_eq_getElem?_getD, v.val.isLt, v.property]
  have hd : Squarefree.decodeMask n (a.stacks 857) = U := by
    rw [hU]
    exact Squarefree.decodeMask_encodeMask U
  rw [hd,QueryJetSemantics.actualProduct_specializeDense q H high _ hm hb hzero ids
    (fun v => decide (v ∈ U)) (fun v : ResidualEmbedding.Free H => decide (v.val ∈ U))
    (fun _ => rfl)]
  exact congrArg (QueryEvaluation.specializeDense q.u q.J
    (fun v : ResidualEmbedding.Free H => decide (v.val ∈ U)))
    (HeadSourceLocality.sourceProduct_assignment_word q H high _
      (HeadSourceLocality.stateFor H high x) h145 ids)

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative.actual_product_value_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative.actual_product_value_oai
