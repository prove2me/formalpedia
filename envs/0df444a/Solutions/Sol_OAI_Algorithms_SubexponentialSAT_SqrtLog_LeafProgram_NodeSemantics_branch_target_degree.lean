-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.branch_target_degree
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:06:51.383026+00:00
-- url     : https://prove2.me/submissions/806495cb-c511-42fd-9997-0384dc0933df

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S020
import Definitions.Def_OAIQ081S076

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

end

end SubexponentialSAT.SqrtLog.TotalOrder

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_TotalOrderPathDegree
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The same additive bound for ordinary polynomial degree, e.g. the CRT path T. -/
namespace SubexponentialSAT.SqrtLog.TotalOrder

noncomputable section
open scoped BigOperators

variable {R α : Type*} [CommSemiring R]

theorem pathDegreeBound_one (b : ℕ) :
    PathDegreeBound 0 b (1 : Polynomial (Polynomial R)) := by
  intro j
  by_cases hj : j = 0 <;> simp [Polynomial.coeff_one, hj]

theorem pathDegreeBound_mul {a c b : ℕ} {P Q : Polynomial (Polynomial R)}
    (hP : PathDegreeBound a b P) (hQ : PathDegreeBound c b Q) :
    PathDegreeBound (a + c) b (P * Q) := by
  classical
  intro j
  rw [Polynomial.coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le _ _
  intro uv huv
  have hj := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
  apply (Polynomial.natDegree_mul_le).trans
  calc
    (P.coeff uv.1).natDegree + (Q.coeff uv.2).natDegree
        ≤ (a + b * uv.1) + (c + b * uv.2) := Nat.add_le_add (hP _) (hQ _)
    _ = a + c + b * j := by rw [← hj]; ring

theorem pathDegreeBound_prod (s : Finset α) (a : α → ℕ) (b : ℕ)
    (P : α → Polynomial (Polynomial R))
    (hP : ∀ i ∈ s, PathDegreeBound (a i) b (P i)) :
    PathDegreeBound (∑ i ∈ s, a i) b (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pathDegreeBound_one (R := R) b
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact pathDegreeBound_mul (hP i (Finset.mem_insert_self i s))
      (ih (fun j hj => hP j (Finset.mem_insert_of_mem hj)))

theorem pathDegreeBound_row (t a b : ℕ) (e : ℕ → Polynomial R)
    (h : Polynomial R) (he : ∀ j < t, (e j).natDegree ≤ a)
    (hh : h.natDegree ≤ b) : PathDegreeBound a b (row t e h) := by
  intro j
  rw [coeff_row]
  split_ifs with hj
  · apply (Polynomial.natDegree_mul_le).trans
    apply Nat.add_le_add (he j hj)
    exact (Polynomial.natDegree_pow_le (p := h) (n := j)).trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left j hh)
  · simp

theorem pathDegreeBound_fullProduct (s : Finset α) (t b : ℕ) (a : α → ℕ)
    (e : α → ℕ → Polynomial R) (h : α → Polynomial R)
    (he : ∀ i ∈ s, ∀ j < t, (e i j).natDegree ≤ a i)
    (hh : ∀ i ∈ s, (h i).natDegree ≤ b) :
    PathDegreeBound (∑ i ∈ s, a i) b (fullProduct s t e h) := by
  apply pathDegreeBound_prod
  intro i hi
  exact pathDegreeBound_row t (a i) b (e i) (h i) (he i hi) (hh i hi)

/-- Only the shared total U-order contributes to the precision degree. -/
theorem output_pathDegree_le (s : Finset α) (t b : ℕ) (a : α → ℕ)
    (e : α → ℕ → Polynomial R) (h : α → Polynomial R)
    (he : ∀ i ∈ s, ∀ j < t, (e i j).natDegree ≤ a i)
    (hh : ∀ i ∈ s, (h i).natDegree ≤ b) :
    (output s t e h).natDegree ≤ (∑ i ∈ s, a i) + b * (t - 1) := by
  classical
  rw [output_eq_sum_coeff]
  apply Polynomial.natDegree_sum_le_of_forall_le _ _
  intro j hj
  apply (pathDegreeBound_fullProduct s t b a e h he hh j).trans
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  have := Finset.mem_range.mp hj
  omega

/-- After substituting degree-k hashes, both contributions scale by k. -/
theorem output_pathDegree_hash_bound (s : Finset α) (t p k : ℕ)
    (e : α → ℕ → Polynomial R) (h : α → Polynomial R)
    (he : ∀ i ∈ s, ∀ j < t, (e i j).natDegree ≤ k * (p - 1))
    (hh : ∀ i ∈ s, (h i).natDegree ≤ k * p) :
    (output s t e h).natDegree ≤ k * (s.card * (p - 1) + p * (t - 1)) := by
  have hbound := output_pathDegree_le s t (k * p) (fun _ => k * (p - 1)) e h he hh
  calc
    _ ≤ (∑ i ∈ s, k * (p - 1)) + k * p * (t - 1) := hbound
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]; ring

end
end SubexponentialSAT.SqrtLog.TotalOrder

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsTarget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The reconstruction target retains one shared total U-order. Its source
rows retain original variable identifiers, and its outer sum is over free
Boolean assignments in one fixed-high branch. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

open scoped BigOperators
open Polynomial
noncomputable section

variable {R : Type*} [CommRing R] {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem literalPath_degree (path : V → R[X]) (l : SAT.Literal V) (r : ℕ)
    (h : (path l.variable).natDegree ≤ r) :
    (literalValue (ringAlgebra R[X]) path l).natDegree ≤ r := by
  cases hp : l.positive
  · simpa [literalValue,ringAlgebra,hp] using h
  · simp only [literalValue,hp,ite_true, if_true,ringAlgebra]
    change (1 + -(path l.variable)).natDegree ≤ r
    exact (Polynomial.natDegree_add_le _ _).trans (by simpa using h)

omit [Fintype V] [DecidableEq V] in
theorem clausePath_degree (path : V → R[X]) (ls : List (SAT.Literal V)) (r : ℕ)
    (h : ∀ l ∈ ls, (path l.variable).natDegree ≤ r) :
    (clauseValue (ringAlgebra R[X]) path ls).natDegree ≤ ls.length*r := by
  induction ls with
  | nil => simp [clauseValue,ringAlgebra]
  | cons l ls ih =>
    change (literalValue (ringAlgebra R[X]) path l *
      clauseValue (ringAlgebra R[X]) path ls).natDegree ≤ (l::ls).length*r
    apply Polynomial.natDegree_mul_le.trans
    have h1 := literalPath_degree path l r (h l (by simp))
    have h2 := ih (fun a ha => h a (by simp [ha]))
    simpa [Nat.add_mul,Nat.add_comm] using Nat.add_le_add h1 h2

omit [Fintype V] [DecidableEq V] in
theorem hashPath_degree (hashes : List (SparseRow V R)) (path : ℕ → V → R[X])
    (i : Fin hashes.length) (k r : ℕ)
    (hwidth : ∀ w ∈ hashes[i], w.2.length ≤ k)
    (hpath : ∀ w ∈ hashes[i], ∀ l ∈ w.2, (path i.val l.variable).natDegree ≤ r) :
    (hashPath hashes path i).natDegree ≤ k*r := by
  unfold hashPath
  generalize hashes[i] = ws at *
  induction ws with
  | nil => simp [rowValue,ringAlgebra]
  | cons w ws ih =>
    change (Polynomial.C w.1 * clauseValue (ringAlgebra R[X]) (path i.val) w.2 +
      rowValue (ringAlgebra R[X]) Polynomial.C (path i.val) ws).natDegree ≤ k*r
    apply Polynomial.natDegree_add_le_of_degree_le
    · apply (Polynomial.natDegree_C_mul_le _ _).trans
      exact (clausePath_degree _ _ r (hpath w (by simp))).trans
        (Nat.mul_le_mul_right r (hwidth w (by simp)))
    · exact ih (fun a ha => hwidth a (by simp [ha]))
        (fun a ha => hpath a (by simp [ha]))

theorem hValue_degree (L : R[X]) (k : ℕ) (hL : L.natDegree ≤ k) :
    (IdempotentProgram.hValue L).natDegree ≤ k*3 := by
  have hs (c : R) : (L - Polynomial.C c).natDegree ≤ k :=
    (Polynomial.natDegree_sub_le _ _).trans (by simpa using hL)
  have h := Nat.add_le_add (Nat.add_le_add hL (hs 1)) (hs 2)
  have hp : (IdempotentProgram.hValue L).natDegree ≤
      L.natDegree + (L-1).natDegree + (L-2).natDegree :=
    Polynomial.natDegree_mul_le.trans (Nat.add_le_add_right Polynomial.natDegree_mul_le _)
  change L.natDegree + (L-1).natDegree + (L-2).natDegree ≤ k+k+k at h
  exact hp.trans (h.trans_eq (by omega))

omit [Fintype V] [DecidableEq V] in
theorem queryPolynomial_degree (t : ℕ) (digits : Fin t → R[X])
    (hdigits : ∀ s, (digits s).natDegree ≤ 2)
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
    (path : ℕ → V → R[X]) (k r : ℕ)
    (hhash : ∀ i, (hashPath hashes path i).natDegree ≤ k*r)
    (hmark : (markedPath hashes marked clause path).natDegree ≤ k*r) :
    (queryPolynomial t digits hashes marked clause path).natDegree ≤
      k*r*(2*hashes.length+3*(t-1)+1) := by
  have he : ∀ i ∈ (Finset.univ : Finset (Fin hashes.length)), ∀ j < t,
      (digitAt digits (hashPath hashes path i) j).natDegree ≤ (k*r)*(3-1) := by
    intro i _ j hj
    simp only [digitAt,dite_eq_left hj]
    exact Polynomial.natDegree_comp_le.trans
      (by simpa [Nat.mul_comm] using Nat.mul_le_mul (hdigits ⟨j,hj⟩) (hhash i))
  have hh : ∀ i ∈ (Finset.univ : Finset (Fin hashes.length)),
      (IdempotentProgram.hValue (hashPath hashes path i)).natDegree ≤ (k*r)*3 :=
    fun i _ => hValue_degree _ _ (hhash i)
  have ho := TotalOrder.output_pathDegree_hash_bound Finset.univ t 3 (k*r) _ _ he hh
  have hb := Polynomial.natDegree_mul_le.trans (Nat.add_le_add ho hmark)
  simpa [queryPolynomial,Finset.card_univ, Nat.mul_add, Nat.mul_comm,Nat.mul_left_comm] using hb

theorem target_degree (H : Finset V) (t : ℕ) (digits : Fin t → R[X])
    (hdigits : ∀ s, (digits s).natDegree ≤ 2)
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
    (path : (ResidualEmbedding.Free H → Bool) → ℕ → V → R[X]) (k r : ℕ)
    (hhash : ∀ x i, (hashPath hashes (path x) i).natDegree ≤ k*r)
    (hmark : ∀ x, (markedPath hashes marked clause (path x)).natDegree ≤ k*r) :
    (target H t digits hashes marked clause path).natDegree ≤
      k*r*(2*hashes.length+3*(t-1)+1) := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro x _
  exact queryPolynomial_degree t digits hdigits hashes marked clause (path x) k r (hhash x) (hmark x)

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

theorem branchPath_degree (H : Finset V) (high : H → Bool)
    (rows : ℕ → V → ResidualEmbedding.Free H → R[X]) (r : ℕ)
    (hrows : ∀ i v w, (rows i v w).natDegree ≤ r)
    (x : ResidualEmbedding.Free H → Bool) (i : ℕ) (v : V) :
    (branchPath H high rows x i v).natDegree ≤ r := by
  unfold branchPath
  split
  · simp
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro w _
    exact (Polynomial.natDegree_mul_C_le _ _).trans (hrows i v w)

/-- The bound is on the actual source target made from these rows. -/
theorem branch_target_degree_oai (H : Finset V) (high : H → Bool)
    (rows : ℕ → V → ResidualEmbedding.Free H → R[X]) (t k r : ℕ)
    (hrows : ∀ i v w, (rows i v w).natDegree ≤ r)
    (digits : Fin t → R[X]) (hdigits : ∀ s, (digits s).natDegree ≤ 2)
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
    (hwidth : ∀ ws ∈ hashes, ∀ w ∈ ws, w.2.length ≤ k) (hclause : clause.length ≤ k) :
    (target H t digits hashes marked clause (branchPath H high rows)).natDegree ≤
      Reconstruction.markedDegreeBound k r hashes.length t := by
  apply target_degree H t digits hdigits hashes marked clause _ k r
  · intro x i
    apply hashPath_degree hashes _ i k r
    · exact hwidth hashes[i] (List.getElem_mem i.isLt)
    · intro w hw l hl
      exact branchPath_degree H high rows r hrows x i.val l.variable
  · intro x
    unfold markedPath
    split
    · exact (clausePath_degree _ clause r (fun l _ =>
        branchPath_degree H high rows r hrows x hashes.length l.variable)).trans
        (Nat.mul_le_mul_right r hclause)
    · simp

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

theorem solution.{u_1, u_2} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.branch_target_degree_oai.{u_1, u_2} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.branch_target_degree_oai.{u_1, u_2}
