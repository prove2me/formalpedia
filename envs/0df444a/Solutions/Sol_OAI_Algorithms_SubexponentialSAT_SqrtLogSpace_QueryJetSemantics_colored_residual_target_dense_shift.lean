-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics.colored_residual_target_dense_shift
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:20:19.377776+00:00
-- url     : https://prove2.me/submissions/35b7ee6e-5997-4bb7-b894-11b0252547a7

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S181
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryJetSemantics_residual_group_diagonal_dense

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_TotalOrderBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Shared total-order truncation of nilpotent expansions

The outer variable is a formal marker U. `output` evaluates the canonical
representative after truncation at U = 1. This is an additive operation on
polynomials, not a homomorphism out of the quotient by U^t.
-/
namespace SubexponentialSAT.SqrtLog.TotalOrder

noncomputable section

open scoped BigOperators
open SubexponentialSAT.Truncation SubexponentialSAT.NilpotentDefect

variable {R S α : Type*} [CommSemiring R] [CommSemiring S]

theorem trunc_eq_sum (t : ℕ) (P : Polynomial R) :
    trunc t P = ∑ j ∈ Finset.range t, Polynomial.monomial j (P.coeff j) := by
  classical
  ext j
  simp [ Polynomial.coeff_monomial]

theorem eval_one_trunc (t : ℕ) (P : Polynomial R) :
    (trunc t P).eval 1 = ∑ j ∈ Finset.range t, P.coeff j := by
  rw [trunc_eq_sum]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, one_pow, mul_one]

theorem output_eq_sum_coeff (s : Finset α) (t : ℕ)
    (e : α → ℕ → R) (h : α → R) :
    output s t e h = ∑ j ∈ Finset.range t, (fullProduct s t e h).coeff j :=
  eval_one_trunc t _

theorem map_output (f : R →+* S) (s : Finset α) (t : ℕ)
    (e : α → ℕ → R) (h : α → R) :
    f (output s t e h) =
      output s t (fun i j => f (e i j)) (fun i => f (h i)) := by
  simp only [output_eq_sum_coeff, map_sum]
  congr 1
  funext j
  simpa only [Polynomial.coeff_map] using
    congrArg (fun P : Polynomial S => P.coeff j) (map_fullProduct f s t e h)

end

end SubexponentialSAT.SqrtLog.TotalOrder

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsJets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual dense readout and attained-bucket sum supply jets of the one
specified source target. The local bucket identity is kept explicit, so a
native parser or assignment service is never assumed to be correct. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
noncomputable section

variable {R : Type*} [CommRing R]

theorem queryExpansion_readout {V : Type*} (t : ℕ) (digits : Fin t → R[X])
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
    (path : ℕ → V → R[X]) :
    Moments.sumUCoeff t (queryExpansion t digits hashes marked clause path) =
      queryPolynomial t digits hashes marked clause path := by
  unfold queryExpansion queryPolynomial
  rw [TotalOrder.output_eq_sum_coeff,Finset.sum_mul]
  simp only [Moments.sumUCoeff,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Polynomial.coeff_mul_C]

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsGroups
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact assembly of all colored factor lists, including optional marking
and neutral IDs. Neither list order nor neutral padding changes the target. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
noncomputable section

variable {A : Type*} [CommMonoid A]

theorem prod_colored_lists {G : Type*} [Fintype G] [DecidableEq G]
    (ids : List ℕ) (hn : ids.Nodup) (color : ℕ → G) (f : ℕ → A) :
    (∏ g, ((ids.filter (fun i => color i = g)).map f).prod) = (ids.map f).prod := by
  rw [← List.prod_toFinset f hn]
  have he (g : G) : ((ids.filter (fun i => color i=g)).map f).prod =
      ∏ i ∈ ids.toFinset.filter (fun i => color i=g), f i := by
    rw [← List.prod_toFinset f (hn.filter _)]
    congr 1
    ext i
    simp
  simp_rw [he]
  exact Finset.prod_fiberwise ids.toFinset color f

theorem prod_ids_split (q : ℕ) (marked : Bool) (ids : List ℕ) (hn : ids.Nodup)
    (hhash : ∀ i < q, i∈ids) (hmark : marked=true → q∈ids) (f : ℕ → A)
    (hother : ∀ i, i ∈ ids → q ≤ i → (¬ (marked = true ∧ i = q)) → f i = 1) :
    (ids.map f).prod = (∏ i : Fin q, f i.val) * (if marked then f q else 1) := by
  rw [← List.prod_toFinset f hn,Fin.prod_univ_eq_prod_range]
  cases hm : marked
  · simp only [Bool.false_eq_true,ite_false,mul_one]
    symm
    apply Finset.prod_subset
    · intro i hi
      exact List.mem_toFinset.mpr (hhash i (Finset.mem_range.mp hi))
    · intro i hi hnq
      exact hother i (List.mem_toFinset.mp hi) (by simpa using hnq) (by simp [hm])
  · simp only [ite_true, if_true]
    rw [← Finset.prod_range_succ]
    symm
    apply Finset.prod_subset
    · intro i hi
      have hh := Finset.mem_range.mp hi
      exact List.mem_toFinset.mpr (if h : i < q then hhash i h else by
        have he : i=q := by omega
        rw [he]
        exact hmark hm)
    · intro i hi hnq
      have hh : q < i := by simpa using hnq
      exact hother i (List.mem_toFinset.mp hi) (by omega) (by omega)

variable {R : Type*} [CommRing R] {n : ℕ}

theorem selectedExpression_product (u : ℕ) (digits : Fin u → R[X])
    (hashes : List (SparseRow (Fin n) R)) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) (path : ℕ → Fin n → R[X])
    (ids : List ℕ) (hn : ids.Nodup) (hh : ∀ i < hashes.length, i∈ids)
    (hm : marked=true → hashes.length∈ids) :
    (ids.map (selectedExpression u digits hashes marked clause path)).prod =
      queryExpansion u digits hashes marked clause path := by
  rw [prod_ids_split hashes.length marked ids hn hh hm]
  · unfold queryExpansion TotalOrder.fullProduct
    congr 1
    · apply Finset.prod_congr rfl
      intro i _
      simp only [selectedExpression,dite_eq_left i.isLt]
    · cases hb : marked <;> simp [selectedExpression,markedPath]
  · intro i hi hq hm'
    simp only [selectedExpression,dite_eq_right (by omega : ¬i < hashes.length)]
    have he : ¬(marked && decide (i=hashes.length))=true := by simpa using hm'
    simp only [ite_eq_right he]

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsShift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The local variable Z is a shift of the common global path T. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
noncomputable section

variable {R : Type*} [CommRing R] {V : Type*}

theorem hashPath_shift (hashes : List (SparseRow V R)) (path : ℕ → V → R[X])
    (theta : R) (i : Fin hashes.length) :
    hashPath hashes (fun j v => shift theta (path j v)) i =
      shift theta (hashPath hashes path i) := by
  unfold hashPath
  simpa only [shift_C] using
    (map_rowValue (shift theta) Polynomial.C (path i.val) hashes[i]).symm

theorem markedPath_shift (hashes : List (SparseRow V R)) (marked : Bool)
    (clause : List (SAT.Literal V)) (path : ℕ → V → R[X]) (theta : R) :
    markedPath hashes marked clause (fun j v => shift theta (path j v)) =
      shift theta (markedPath hashes marked clause path) := by
  cases hm : marked
  · simp [markedPath]
  · simp only [markedPath,ite_true, if_true]
    exact (map_clauseValue (shift theta) (path hashes.length) clause).symm

theorem queryPolynomial_shift (t : ℕ) (digits : Fin t → R[X])
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
    (path : ℕ → V → R[X]) (theta : R) :
    queryPolynomial t digits hashes marked clause (fun j v => shift theta (path j v)) =
      shift theta (queryPolynomial t digits hashes marked clause path) := by
  unfold queryPolynomial
  rw [map_mul,TotalOrder.map_output,markedPath_shift]
  congr 2
  · funext i j
    unfold digitAt
    split
    · rw [hashPath_shift]
      simp only [shift_apply,Polynomial.comp_assoc]
    · simp
  · funext i
    rw [hashPath_shift]
    simp only [IdempotentProgram.hValue,map_mul,map_sub,map_one,map_ofNat]

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryEvaluation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact natural-valued query semantics. These identities preserve the ambient
assignment type, including coordinates absent from every clause. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEvaluation

open OAI.Algorithms.SubexponentialSAT.SqrtLog
open scoped BigOperators

section SourceReadout

open Polynomial LeafProgram LeafProgram.NodeSemantics
variable {R : Type*} [CommRing R]

/-- The new bounded array readout is exactly the original shared-marker
coefficient sum, with the same Taylor truncation. -/
theorem dense_readout_source (t J : ℕ) (P : Polynomial (Polynomial R)) :
    Dense.readout (Dense.ofPolynomial t J P) =
      Truncated.ofPolynomial J (Moments.sumUCoeff t P) := by
  ext z
  rw [Dense.coeff_readout, Truncated.coeff_ofPolynomial, Moments.sumUCoeff_coeff]
  simp only [Dense.coeff_ofPolynomial]
  exact Fin.sum_univ_eq_sum_range (fun u => (P.coeff u).coeff z.val) t

/-- Every actual colored factor, including neutral padding and the optional
marked clause, contributes to the one original query polynomial. -/
theorem colored_selected_dense_readout {n : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (t J : ℕ) (digits : Fin t → R[X])
    (hashes : List (SparseRow (Fin n) R)) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) (path : ℕ → Fin n → R[X])
    (ids : List ℕ) (hn : ids.Nodup) (hh : ∀ i < hashes.length, i ∈ ids)
    (hm : marked = true → hashes.length ∈ ids) (color : ℕ → G) :
    Dense.readout (∏ g,
      Dense.ofPolynomial t J (((ids.filter (fun i => color i = g)).map
        (selectedExpression t digits hashes marked clause path)).prod)) =
      Truncated.ofPolynomial J (queryPolynomial t digits hashes marked clause path) := by
  rw [← map_prod, prod_colored_lists ids hn color,
    dense_readout_source, selectedExpression_product t digits hashes marked clause path ids hn hh hm,
    queryExpansion_readout]

/-- Shifting at a reconstruction node retains the same source target. -/
theorem colored_selected_dense_shift {n : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (t J : ℕ) (digits : Fin t → R[X])
    (hashes : List (SparseRow (Fin n) R)) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) (path : ℕ → Fin n → R[X]) (theta : R)
    (ids : List ℕ) (hn : ids.Nodup) (hh : ∀ i < hashes.length, i ∈ ids)
    (hm : marked = true → hashes.length ∈ ids) (color : ℕ → G) :
    Dense.readout (∏ g,
      Dense.ofPolynomial t J (((ids.filter (fun i => color i = g)).map
        (selectedExpression t digits hashes marked clause
          (fun j v => shift theta (path j v)))).prod)) =
      Truncated.ofPolynomial J ((queryPolynomial t digits hashes marked clause path).comp
        (Polynomial.X + Polynomial.C theta)) := by
  rw [colored_selected_dense_readout t J digits hashes marked clause _ ids hn hh hm color,
    queryPolynomial_shift, shift_apply]

end SourceReadout

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEvaluation
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



section SourceJets

variable {R G : Type*} [CommRing R] [Fintype G] [DecidableEq G] {n : ℕ}

/-- Summing the actual shifted colored expressions produces every retained
coefficient of the original fixed-high source target. -/
theorem colored_target_dense_shift (H : Finset (Fin n)) (t J : ℕ)
    (digits : Fin t → R[X]) (hashes : List (SparseRow (Fin n) R))
    (marked : Bool) (clause : List (SAT.Literal (Fin n)))
    (path : (ResidualEmbedding.Free H → Bool) → ℕ → Fin n → R[X]) (theta : R)
    (ids : List ℕ) (hn : ids.Nodup) (hh : ∀ i < hashes.length, i ∈ ids)
    (hm : marked = true → hashes.length ∈ ids) (color : ℕ → G) :
    Dense.readout (∑ x : ResidualEmbedding.Free H → Bool, ∏ g,
      Dense.ofPolynomial t J (((ids.filter (fun i => color i = g)).map
        (selectedExpression t digits hashes marked clause
          (fun j v => shift theta (path x j v)))).prod)) =
      Truncated.ofPolynomial J ((target H t digits hashes marked clause path).comp
        (X + C theta)) := by
  rw [map_sum]
  simp_rw [QueryEvaluation.colored_selected_dense_shift t J digits hashes marked clause
    _ theta ids hn hh hm color]
  rw [target, Polynomial.sum_comp]
  exact (map_sum (Truncated.ofPolynomialHom J) _ _).symm

end SourceJets

section NativeReadout

open NodeConcrete MomentsProgram

variable {r Q n d : ℕ} {G : Type*} [Fintype G] [DecidableEq G]

/-- The actual colored residual products, evaluated at all free assignments,
produce the shifted fixed-high target. Empty groups retain their neutral one,
and additive readout occurs after the complete group product. -/
theorem colored_residual_target_dense_shift_oai (q : Factor.Spec r Q n d)
    (hu : q.u = q.p.t) (H : Finset (Fin n)) (high : H → Bool)
    (state : (ResidualEmbedding.Free H → Bool) → Fin 768 → List Bool)
    (hstate : ∀ x (v : Fin n), (state x 145).getD v.val false = HighIncidence.glue H high x v)
    (ids : List ℕ) (hn : ids.Nodup)
    (hh : ∀ id < (AssignmentConcrete.weightedHashes q).length, id ∈ ids)
    (hm : q.marked = true → (AssignmentConcrete.weightedHashes q).length ∈ ids)
    (color : ℕ → G)
    (hzero : ∀ id j (v : Fin n), v ∈ H →
      PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id j v = 0)
    (hhash : ∀ id ∈ ids, ∀ hi : id < (AssignmentConcrete.weightedHashes q).length,
      ∀ w ∈ (AssignmentConcrete.weightedHashes q)[id], ∀ l ∈ w.literals,
        l.variable ∉ H → (l.variable.val, n + id) ∈ q.ps)
    (hmark : q.marked = true → (AssignmentConcrete.weightedHashes q).length ∈ ids →
      ∀ l ∈ q.markedClause, l.variable ∉ H →
        (l.variable.val, n + (AssignmentConcrete.weightedHashes q).length) ∈ q.ps) :
    Dense.readout (∑ x : ResidualEmbedding.Free H → Bool, ∏ g,
      QueryEvaluation.specializeDense q.p.t q.J x
        (Squarefree.canonical q.u q.J (((ids.filter (fun id => color id = g)).map
          (AssignmentConcrete.residualValue q.ctx (q.p.model.base q.p.t)
            (RingBasis.basis (q.p.model.F q.p.t)) q.code
            (residualJet q.p q.ps q.packing H high q.theta (state x))
            (AssignmentConcrete.weightedHashes q) q.marked q.markedClause)).prod))) =
      Truncated.ofPolynomial q.J ((specTarget q H high).comp
        (X + C (q.p.ops.decode q.theta))) := by
  have he (x : ResidualEmbedding.Free H → Bool) (g : G) :=
    residual_group_diagonal_dense q hu H high (state x) x (hstate x)
      (ids.filter (fun id => color id = g)) hzero
      (fun id hid => hhash id (List.mem_filter.mp hid).1)
      (fun hmarked hid => hmark hmarked (List.mem_filter.mp hid).1)
  simp_rw [he]
  exact colored_target_dense_shift H q.p.t q.J
    (codeDigits q.ctx (q.p.model.base q.p.t) q.code) (decodedHashes q)
    q.marked q.markedClause (branchPath H high (completedRows q.p q.ps q.packing H))
    (q.p.ops.decode q.theta) ids hn
    (by simpa only [decodedHashes, List.length_map] using hh)
    (by simpa only [decodedHashes, List.length_map] using hm) color

end NativeReadout

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics.colored_residual_target_dense_shift_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics.colored_residual_target_dense_shift_oai.{u_1}
