-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality.colored_source_admissible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:08:32.763962+00:00
-- url     : https://prove2.me/submissions/4515b9a3-3840-448a-8b12-23c6abe82530

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

theorem bounded_zero (d : ℕ) : Bounded d (0 : Poly V R) := by simp [Bounded]

omit [DecidableEq V] in
theorem bounded_monomial (s : Finset V) (c : R) {d : ℕ} (h : s.card ≤ d) :
    Bounded d (monomial s c) := by
  intro a ha
  have : a = Support.mk s := Finset.mem_singleton.mp (Finsupp.support_single_subset ha)
  subst a
  exact h

theorem bounded_one : Bounded 0 (1 : Poly V R) := bounded_monomial ∅ 1 (by simp)

theorem Bounded.add {d : ℕ} {f g : Poly V R} (hf : Bounded d f) (hg : Bounded d g) :
    Bounded d (f + g) := by
  intro a ha
  rcases Finset.mem_union.mp (Finsupp.support_add ha) with h | h
  · exact hf a h
  · exact hg a h

theorem Bounded.mul {d e : ℕ} {f g : Poly V R} (hf : Bounded d f) (hg : Bounded e g) :
    Bounded (d + e) (f * g) := by
  intro a ha
  have hmem := MonoidAlgebra.support_coeff_mul_subset f g ha
  obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_image₂.mp hmem
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add (hf b hb) (hg c hc))

theorem bounded_sum {ι : Type*} (s : Finset ι) (f : ι → Poly V R) (d : ℕ)
    (h : ∀ i ∈ s, Bounded d (f i)) : Bounded d (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bounded_zero (V := V) (R := R) d
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self _ _)).add
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeJet
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! U is the outer polynomial variable, Z the inner one. Support cardinality
is charged only to Z degree; no formal X support is charged to U. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

noncomputable section

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

theorem zAdmissible_zero : ZAdmissible (0 : ZJet V R) := by
  intro j; simpa using bounded_zero (V := V) (R := R) j

theorem zAdmissible_one : ZAdmissible (1 : ZJet V R) := by
  intro j
  by_cases hj : j = 0
  · subst j; simpa using bounded_one (V := V) (R := R)
  · simpa [Polynomial.coeff_one, hj] using bounded_zero (V := V) (R := R) j

theorem ZAdmissible.add {f g : ZJet V R} (hf : ZAdmissible f) (hg : ZAdmissible g) :
    ZAdmissible (f + g) := by
  intro j
  simpa using (hf j).add (hg j)

theorem zAdmissible_sum {ι : Type*} (s : Finset ι) (f : ι → ZJet V R)
    (h : ∀ i ∈ s, ZAdmissible (f i)) : ZAdmissible (∑ i ∈ s, f i) := by
  intro j
  simp only [Polynomial.finsetSum_coeff]
  exact bounded_sum s (fun i => (f i).coeff j) j (fun i hi => h i hi j)

theorem ZAdmissible.mul {f g : ZJet V R} (hf : ZAdmissible f) (hg : ZAdmissible g) :
    ZAdmissible (f * g) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply bounded_sum
  intro ab hab
  have hsum : ab.1 + ab.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  simpa [hsum] using (hf ab.1).mul (hg ab.2)

theorem zAdmissible_monomial (j : ℕ) (f : Poly V R) (hf : Bounded j f) :
    ZAdmissible (Polynomial.monomial j f) := by
  intro l
  by_cases h : j = l
  · subst l; simpa using hf
  · simpa [Polynomial.coeff_monomial, h] using bounded_zero (V := V) (R := R) l

theorem admissible_zero : Admissible (0 : Jet V R) := by
  intro u; simpa using zAdmissible_zero (V := V) (R := R)

theorem admissible_one : Admissible (1 : Jet V R) := by
  intro u
  by_cases h : u = 0
  · subst u; simpa using zAdmissible_one (V := V) (R := R)
  · simpa [Polynomial.coeff_one, h] using zAdmissible_zero (V := V) (R := R)

theorem Admissible.add {f g : Jet V R} (hf : Admissible f) (hg : Admissible g) :
    Admissible (f + g) := by
  intro u; simpa using (hf u).add (hg u)

theorem admissible_sum {ι : Type*} (s : Finset ι) (f : ι → Jet V R)
    (h : ∀ i ∈ s, Admissible (f i)) : Admissible (∑ i ∈ s, f i) := by
  intro u
  simp only [Polynomial.finsetSum_coeff]
  exact zAdmissible_sum s (fun i => (f i).coeff u) (fun i hi => h i hi u)

theorem Admissible.mul {f g : Jet V R} (hf : Admissible f) (hg : Admissible g) :
    Admissible (f * g) := by
  intro u
  rw [Polynomial.coeff_mul]
  apply zAdmissible_sum
  intro ab _
  exact (hf ab.1).mul (hg ab.2)

theorem admissible_monomial (u : ℕ) (f : ZJet V R) (hf : ZAdmissible f) :
    Admissible (Polynomial.monomial u f) := by
  intro l
  by_cases h : u = l
  · subst l; simpa using hf
  · simpa [Polynomial.coeff_monomial, h] using zAdmissible_zero (V := V) (R := R)

theorem Admissible.pow {f : Jet V R} (hf : Admissible f) (n : ℕ) :
    Admissible (f ^ n) := by
  induction n with
  | zero => simpa using admissible_one (V := V) (R := R)
  | succ n ih => simpa [pow_succ] using ih.mul hf

theorem admissible_prod {ι : Type*} (s : Finset ι) (f : ι → Jet V R)
    (h : ∀ i ∈ s, Admissible (f i)) : Admissible (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using admissible_one (V := V) (R := R)
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (h i (Finset.mem_insert_self _ _)).mul
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem Admissible.canonical {f : Jet V R} (hf : Admissible f) (t J : ℕ) :
    Admissible (canonical t J f) := by
  intro u j
  by_cases h : u < t ∧ j < J
  · simpa [h] using hf u j
  · simpa [h] using bounded_zero (V := V) (R := R) j

end
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparseProduct
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

namespace Sparse

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

theorem atom_admissible (a : Index V) (c : R) (ha : a.Valid) : Admissible (atom a c) :=
  admissible_monomial _ _ (zAdmissible_monomial _ _ (bounded_monomial _ _ ha))

end Sparse
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

theorem variableZ_admissible (v : V) (p : Polynomial R) (hp : p.coeff 0 = 0) :
    ZAdmissible (variableZ v p) := by
  intro j
  rw [variableZ_coeff]
  by_cases hj : j = 0
  · subst j
    simp only [hp]
    simpa [Squarefree.monomial] using (bounded_zero (V := V) (R := R) 0)
  · apply bounded_monomial
    simp only [Finset.card_singleton]
    omega

theorem incidenceZ_admissible [Fintype V] (row : V → Polynomial R) (theta beta : R) :
    ZAdmissible (incidenceZ row theta beta) := by
  apply ZAdmissible.add
  · apply zAdmissible_monomial 0
    exact bounded_monomial ∅ beta (by simp)
  · apply zAdmissible_sum
    intro v hv
    exact variableZ_admissible v _ (rowDelta_coeff_zero (row v) theta)

theorem incidenceJet_admissible [Fintype V] (row : V → Polynomial R) (theta beta : R) :
    Admissible (incidenceJet row theta beta) :=
  admissible_monomial 0 _ (incidenceZ_admissible row theta beta)

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

theorem scalarJet_eq_ringScalar (c : R) :
    scalarJet (V := V) c = Moments.ringScalar c :=
  (Moments.ringScalar_eq_atom c).symm

end
end SubexponentialSAT.SqrtLog.ResidualEmbedding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramAssignmentConcreteAdmissible
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Admissibility closure for source expressions whose original literal
identifiers need not equal their free formal-variable type. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

open Polynomial _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree NodeSemantics
open scoped BigOperators

variable {V I R : Type*} [DecidableEq V] [CommRing R]

theorem admissible_ringScalar (c : R) : Admissible (Moments.ringScalar (V:=V) c) := by
  rw [Moments.ringScalar_eq_atom]
  exact Sparse.atom_admissible _ _ (by simp [Index.Valid,Index.origin])

theorem admissible_neg {F : Jet V R} (hF : Admissible F) : Admissible (-F) := by
  intro u z
  rw [Polynomial.coeff_neg, Polynomial.coeff_neg]
  intro s hs
  exact hF u z s (by simpa using hs)

theorem admissible_sub {F G : Jet V R} (hF : Admissible F) (hG : Admissible G) :
    Admissible (F-G) := by
  change Admissible (F + -G)
  exact hF.add (admissible_neg hG)

theorem admissible_X : Admissible (Polynomial.X : Jet V R) := by
  simpa only [Polynomial.monomial_one_one_eq_X] using
    admissible_monomial 1 (1 : ZJet V R) zAdmissible_one

theorem admissible_eval₂ (P : R[X]) {F : Jet V R} (hF : Admissible F) :
    Admissible (P.eval₂ Moments.ringScalar F) := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => simpa only [Polynomial.eval₂_add] using hp.add hq
  | monomial i c =>
    simpa only [Polynomial.eval₂_monomial] using (admissible_ringScalar c).mul (hF.pow i)

theorem admissible_literal (value : I → Jet V R) (hv : ∀ i, Admissible (value i))
    (l : SAT.Literal I) : Admissible (literalValue (ringAlgebra (Jet V R)) value l) := by
  cases hp : l.positive
  · simpa [literalValue,hp] using hv l.variable
  · simpa [literalValue,hp,ringAlgebra] using
      (admissible_one (V:=V) (R:=R)).add (admissible_neg (hv l.variable))

theorem admissible_clause (value : I → Jet V R) (hv : ∀ i, Admissible (value i))
    (ls : List (SAT.Literal I)) :
    Admissible (clauseValue (ringAlgebra (Jet V R)) value ls) := by
  induction ls with
  | nil => exact admissible_one
  | cons l ls ih => exact (admissible_literal value hv l).mul ih

theorem admissible_row (value : I → Jet V R) (hv : ∀ i, Admissible (value i))
    (ws : SparseRow I R) :
    Admissible (rowValue (ringAlgebra (Jet V R)) (scalarJet (V:=V)) value ws) := by
  induction ws with
  | nil => exact admissible_zero
  | cons w ws ih =>
    have hc : Admissible (scalarJet (V:=V) w.1) := by
      rw [ResidualEmbedding.scalarJet_eq_ringScalar]
      exact admissible_ringScalar w.1
    exact (hc.mul (admissible_clause value hv w.2)).add ih

theorem admissible_indicatorJet (t : ℕ) (digits : Fin t → R[X])
    {F : Jet V R} (hF : Admissible F) : Admissible (indicatorJet t digits F) := by
  apply admissible_sum
  intro s hs
  have h1 : Admissible (1 : Jet V R) := admissible_one
  have h2 : Admissible (2 : Jet V R) := by
    simpa only [one_add_one_eq_two] using h1.add h1
  have hh : Admissible (IdempotentProgram.hValue F) :=
    (hF.mul (admissible_sub hF h1)).mul (admissible_sub hF h2)
  exact ((admissible_X.pow s.val).mul (admissible_eval₂ (digits s) hF)).mul (hh.pow s.val)

theorem admissible_list_prod {A : Type*} (xs : List A) (F : A → Jet V R)
    (hF : ∀ a ∈ xs, Admissible (F a)) : Admissible ((xs.map F).prod) := by
  induction xs with
  | nil => exact admissible_one
  | cons a xs ih =>
    exact (hF a (by simp)).mul (ih (fun b hb => hF b (by simp [hb])))

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

end

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

variable {p t n d : ℕ} [Fact p.Prime]

theorem residualValue_admissible (ctx : Context p t n d)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    (jfree : ℕ → Fin n → Jet V R) (hj : ∀ id v, Admissible (jfree id v))
    (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (id : ℕ) :
    Admissible (residualValue ctx scalar basis code jfree hashes marked clause id) := by
  unfold residualValue
  split
  · apply admissible_indicatorJet
    rw [← rowValue_eq_eval (R:=Jet V R) (scalarJet (V:=V)) (jfree id)]
    exact admissible_row (jfree id) (hj id) _
  · split
    · rw [← clauseValue_eq_eval (R:=Jet V R) (jfree id) clause]
      exact admissible_clause (jfree id) (hj id) clause
    · exact admissible_one

theorem residual_product_admissible (ctx : Context p t n d)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    (jfree : ℕ → Fin n → Jet V R) (hj : ∀ id v, Admissible (jfree id v))
    (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (ids : List ℕ) :
    Admissible (canonical ctx.u ctx.J
      ((ids.map (residualValue ctx scalar basis code jfree hashes marked clause)).prod)) := by
  apply Admissible.canonical
  apply admissible_list_prod
  intro id hi
  exact residualValue_admissible ctx scalar basis code jfree hj hashes marked clause id

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteResidualProduct
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual head polynomials live in the free-variable algebra. Each factor
and multiplication retains the same U and T cutoffs as the native program. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsAssembly _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

variable {r Q n d : ℕ}

theorem residualJet_admissible (q : Factor.Spec r Q n d) (H : Finset (Fin n)) (high : H → Bool)
    (state : Fin 768 → List Bool) (id : ℕ) (v : Fin n) :
    Admissible (residualJet q.p q.ps q.packing H high q.theta state id v) := by
  unfold residualJet
  split
  · exact AssignmentConcrete.admissible_ringScalar _
  · exact Moments.incidenceJet_admissible _ _ _

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

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

/-- The actual retained source product has Boolean degree at most its Taylor
index, including the neutral-factor and empty-group cases. -/
theorem sourceProduct_admissible (q : Factor.Spec r Q n d)
    (H : Finset (Fin n)) (high : H → Bool)
    (state : Fin 768 → List Bool) (ids : List ℕ) :
    Squarefree.Admissible (sourceProduct q H high state ids) :=
  AssignmentConcrete.residual_product_admissible q.ctx (q.p.model.base q.p.t)
    (RingBasis.basis (q.p.model.F q.p.t)) q.code
    (residualJet q.p q.ps q.packing H high q.theta state)
    (residualJet_admissible q H high state) (AssignmentConcrete.weightedHashes q)
    q.marked q.markedClause ids

/-- Admissibility of the actual product over all colored factor groups,
required by the grouped finite-difference query. -/
theorem colored_source_admissible_oai (q : Factor.Spec r Q n d)
    (H : Finset (Fin n)) (high : H → Bool)
    (state : Fin 768 → List Bool) (ids : List ℕ) (color : ℕ → Fin r) :
    Squarefree.Admissible
      (∏ g : Fin r, sourceProduct q H high state (ids.filter (fun f => color f = g))) := by
  apply Squarefree.admissible_prod
  intro g _
  exact sourceProduct_admissible q H high state _

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality.colored_source_admissible_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality.colored_source_admissible_oai
