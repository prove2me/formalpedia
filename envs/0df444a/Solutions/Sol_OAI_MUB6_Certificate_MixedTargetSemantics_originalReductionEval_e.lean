-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.originalReductionEval_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:07:37.108499+00:00
-- url     : https://prove2.me/submissions/9a38dac3-a900-4151-91b9-2ee1e4ea9899

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E051
import Definitions.Def_OAIQ106E078
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E133
import Definitions.Def_OAIQ106E136
import Definitions.Def_OAIQ106E137
import Definitions.Def_OAIQ106E138
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_reducedMergeEval1436_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_reducedMergeEval1675_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_reducedMergeEval1794_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_reducedMergeEval1912_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_reducedMergeEval957_e

section
-- module Solutions.OAIQ106_MUB.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Definitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mathematical definitions for the exact Fourier companion.

The character normalization is exactly 1/6, not an unnormalized sum.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_ne_zero {z : ℂ} (hz : Complex.normSq z = 1) : z ≠ 0 := by
  intro h
  simp [h] at hz

theorem character_add (x : Coord → ℂ) (hx : ∀ i, x i ≠ 0) (a b : Charge) :
    character x (a + b) = character x a * character x b := by
  simp only [character, Pi.add_apply, zpow_add₀ (hx _), Finset.prod_mul_distrib]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_Superoperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Realignment of a self-adjoint projection

The complement operator in Weiner's argument is an orthogonal projection whose
matrix is invariant under realignment. Its columns therefore form a finite
Kraus family; choosing an orthonormal basis of its range is unnecessary.
-/

namespace MUB6.Weiner

open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma applySuper_one_entry (C : Matrix (n × n) (n × n) ℂ) (i j : n) :
    applySuper C 1 i j = ∑ k, C (i, j) (k, k) := by
  simp [applySuper, Fintype.sum_prod_type, Matrix.one_apply]

/-- A Hermitian idempotent with zero trace is zero. -/
theorem hermitian_idempotent_eq_zero_of_trace_zero {I : Type*} [Fintype I]
    (C : Matrix I I ℂ) (hherm : Cᴴ = C) (hidem : C * C = C)
    (htrace : C.trace = 0) : C = 0 := by
  apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
  rwa [hherm, hidem]

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_Complement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The concrete complement supermatrix

The Hermitian and realignment symmetries are algebraic identities for arbitrary
complex vectors. Orthonormality and mutual unbiasedness are needed for the
separate unitality and idempotence identities.
-/

namespace MUB6.Weiner

open Matrix
open scoped BigOperators

variable {n ι κ : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [Fintype κ]

omit [Fintype n] in
lemma traceMatrix_hermitian : (traceMatrix : Matrix (n × n) (n × n) ℂ)ᴴ = traceMatrix := by
  ext p q
  simp [traceMatrix, Matrix.conjTranspose_apply, and_comm]

omit [Fintype n] [DecidableEq n] in
lemma pinchingMatrix_hermitian (v : κ → n → ℂ) : (pinchingMatrix v)ᴴ = pinchingMatrix v := by
  ext p q
  simp only [Matrix.conjTranspose_apply, pinchingMatrix, star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro a _
  ring

omit [Fintype n] in
lemma complementMatrix_hermitian (v : ι → κ → n → ℂ) :
    (complementMatrix v)ᴴ = complementMatrix v := by
  simp [complementMatrix, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_sum, traceMatrix_hermitian, pinchingMatrix_hermitian]

lemma traceMatrix_trace : (traceMatrix : Matrix (n × n) (n × n) ℂ).trace = Fintype.card n := by
  simp only [Matrix.trace, Matrix.diag, traceMatrix, and_self]
  rw [Fintype.sum_prod_type]
  simp

lemma traceMatrix_square : (traceMatrix : Matrix (n × n) (n × n) ℂ) * traceMatrix =
    (Fintype.card n : ℂ) • traceMatrix := by
  ext p q
  by_cases hp : p.1 = p.2 <;> by_cases hq : q.1 = q.2 <;>
    simp [Matrix.mul_apply, traceMatrix, Fintype.sum_prod_type, hp, hq]

/-- Composing a unital map with the trace map leaves the trace map unchanged. -/
lemma mul_traceMatrix_of_unital (C : Matrix (n × n) (n × n) ℂ)
    (hC : applySuper C 1 = 1) : C * traceMatrix = traceMatrix := by
  ext ⟨i, j⟩ ⟨k, l⟩
  by_cases hkl : k = l
  · subst l
    have h := congrArg (fun X : Matrix n n ℂ => X i j) hC
    rw [applySuper_one_entry] at h
    simpa [Matrix.mul_apply, traceMatrix, Fintype.sum_prod_type, Matrix.one_apply] using h
  · simp [Matrix.mul_apply, traceMatrix, hkl]

/-- Self-adjoint unital maps also leave the trace map unchanged on the other side. -/
lemma traceMatrix_mul_of_hermitian_unital (C : Matrix (n × n) (n × n) ℂ)
    (hherm : Cᴴ = C) (hC : applySuper C 1 = 1) : traceMatrix * C = traceMatrix := by
  have h := congrArg Matrix.conjTranspose (mul_traceMatrix_of_unital C hC)
  simpa only [Matrix.conjTranspose_mul, traceMatrix_hermitian, hherm] using h

/-- A pinching supermatrix is unital when its vectors are unit and complete. -/
lemma pinchingMatrix_unital (v : κ → n → ℂ)
    (hnorm : ∀ a, ∑ i, star (v a i) * v a i = 1)
    (hcomplete : ∀ i j, ∑ a, v a i * star (v a j) = if i = j then 1 else 0) :
    applySuper (pinchingMatrix v) 1 = 1 := by
  ext i j
  rw [applySuper_one_entry]
  change (∑ k, ∑ a, v a i * star (v a j) * star (v a k) * v a k) = _
  rw [Finset.sum_comm]
  have hinner (a : κ) :
      (∑ k, v a i * star (v a j) * star (v a k) * v a k) = v a i * star (v a j) := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, ← Finset.mul_sum, hnorm]
    simp
  simp only [hinner]
  simpa [Matrix.one_apply] using hcomplete i j

omit [DecidableEq n] in
/-- Unit input vectors give the exact trace of a pinching supermatrix. -/
lemma pinchingMatrix_trace (v : κ → n → ℂ)
    (hnorm : ∀ a, ∑ i, star (v a i) * v a i = 1) :
    (pinchingMatrix v).trace = Fintype.card κ := by
  have hexpand : (pinchingMatrix v).trace =
      ∑ a, (∑ i, star (v a i) * v a i) * (∑ j, star (v a j) * v a j) := by
    simp only [Matrix.trace, Matrix.diag, pinchingMatrix]
    rw [Finset.sum_comm]
    simp only [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand]
  simp only [hnorm, one_mul]
  simp

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_Frame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rank-one frame identities used to calculate the complement projection. -/

namespace MUB6.Weiner

open Matrix
open scoped BigOperators

variable {I κ η n : Type*} [Fintype I] [Fintype κ] [Fintype η] [Fintype n]

lemma frameOperator_idempotent [DecidableEq κ] (v : κ → I → ℂ)
    (hv : ∀ a b, star (v a) ⬝ᵥ v b = if a = b then 1 else 0) :
    frameOperator v * frameOperator v = frameOperator v := by
  classical
  simp only [frameOperator, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.vecMulVec_mul_vecMulVec, hv]
  simp [apply_ite]

lemma frameOperator_mul (v : κ → I → ℂ) (w : η → I → ℂ) (c : ℂ)
    (hvw : ∀ a b, star (v a) ⬝ᵥ w b = c) :
    frameOperator v * frameOperator w = c • Matrix.vecMulVec (∑ a, v a) (star (∑ b, w b)) := by
  classical
  simp only [frameOperator, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.vecMulVec_mul_vecMulVec, hvw, Matrix.vecMulVec_smul]
  ext i j
  simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Finset.sum_mul, Finset.mul_sum]

lemma projectorVector_inner (v w : n → ℂ) :
    star (projectorVector v) ⬝ᵥ projectorVector w =
      (star v ⬝ᵥ w) * star (star v ⬝ᵥ w) := by
  simp only [dotProduct, projectorVector, Pi.star_apply, star_sum, star_mul, star_star,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [Fintype n] in
lemma pinchingMatrix_eq_frameOperator [DecidableEq n] (v : κ → n → ℂ) :
    pinchingMatrix v = frameOperator (fun a => projectorVector (v a)) := by
  ext p q
  simp only [pinchingMatrix, frameOperator, Matrix.sum_apply, Matrix.vecMulVec_apply,
    projectorVector, Pi.star_apply, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro a _
  ring

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_ComplementAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Algebra of the missing-basis projection

The six diagonal expectation operators and the trace operator satisfy a small
multiplication table. The proof shows that the resulting complement operator
is idempotent, using ring algebra rather than numerical approximation.
-/

namespace MUB6.Weiner

variable {R : Type*} [Ring R]

open scoped BigOperators

/-- A finite family of idempotents whose off-diagonal products are one common
operator has an explicit square for its sum. -/
theorem sum_pairwise_projection_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → R) (P : R)
    (h : ∀ i j, D i * D j = if i = j then D i else P) :
    (∑ i, D i) * (∑ i, D i) = (∑ i, D i) +
      ((Fintype.card ι : R) ^ 2 - (Fintype.card ι : R)) * P := by
  have h' (i j : ι) : D i * D j = (if i = j then D i - P else 0) + P := by
    rw [h]
    split_ifs <;> simp
  simp_rw [Finset.sum_mul, Finset.mul_sum, h', Finset.sum_add_distrib]
  simp [Finset.sum_sub_distrib, nsmul_eq_mul]
  noncomm_ring

/-- The analogous complement for seven expectations in dimension six is also
idempotent. Together with its zero trace this yields the complete-family moment
identity. -/
theorem complete_complement_idempotent (S W : R)
    (hSS : S * S = S + 7 * W)
    (hSW : S * W = 7 * W) (hWS : W * S = 7 * W)
    (hWW : W * W = 6 * W) :
    (1 + W - S) * (1 + W - S) = 1 + W - S := by
  noncomm_ring [hSS, hSW, hWS, hWW]

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_OrthogonalPinching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact multiplication tables for six and seven unbiased pinching operators. -/

namespace MUB6.Weiner

open Matrix
open scoped BigOperators

lemma seven_projection_sum_square (D : Fin 7 → SuperSix)
    (hpair : ∀ r s, D r * D s = if r = s then D r else (1 / 6 : ℂ) • traceMatrix) :
    (∑ r, D r) * (∑ r, D r) = (∑ r, D r) + 7 * traceMatrix := by
  have h := sum_pairwise_projection_square D ((1 / 6 : ℂ) • traceMatrix) hpair
  norm_num at h
  have hcoeff : (1 / 6 : ℂ) • ((42 : SuperSix) * traceMatrix) = 7 * traceMatrix := by
    ext p q
    norm_num [Matrix.mul_apply, Matrix.ofNat_apply, ite_mul]
    ring
  rwa [hcoeff] at h

lemma projection_sum_mul_traceMatrix {m : ℕ} (D : Fin m → SuperSix)
    (hunital : ∀ r, applySuper (D r) 1 = 1) :
    (∑ r, D r) * traceMatrix = (m : SuperSix) * traceMatrix := by
  simp only [Matrix.sum_mul, mul_traceMatrix_of_unital _ (hunital _), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma traceMatrix_mul_projection_sum {m : ℕ} (D : Fin m → SuperSix)
    (hherm : ∀ r, (D r)ᴴ = D r) (hunital : ∀ r, applySuper (D r) 1 = 1) :
    traceMatrix * (∑ r, D r) = (m : SuperSix) * traceMatrix := by
  simp only [Matrix.mul_sum, traceMatrix_mul_of_hermitian_unital _ (hherm _) (hunital _),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma traceMatrix_six_square : (traceMatrix : SuperSix) * traceMatrix = 6 * traceMatrix := by
  calc
    (traceMatrix : SuperSix) * traceMatrix = (6 : ℂ) • traceMatrix := by
      simpa only [Fintype.card_fin, Nat.cast_ofNat] using (traceMatrix_square (n := Fin 6))
    _ = 6 * traceMatrix := by
      ext p q
      norm_num [Matrix.mul_apply, Matrix.ofNat_apply, ite_mul]

/-- The complete seven-basis complement is idempotent as well. -/
theorem seven_complement_idempotent (D : Fin 7 → SuperSix)
    (hpair : ∀ r s, D r * D s = if r = s then D r else (1 / 6 : ℂ) • traceMatrix)
    (hherm : ∀ r, (D r)ᴴ = D r) (hunital : ∀ r, applySuper (D r) 1 = 1) :
    (1 + traceMatrix - ∑ r, D r) * (1 + traceMatrix - ∑ r, D r) =
      1 + traceMatrix - ∑ r, D r :=
  complete_complement_idempotent _ _ (seven_projection_sum_square D hpair)
    (projection_sum_mul_traceMatrix D hunital)
    (traceMatrix_mul_projection_sum D hherm hunital) traceMatrix_six_square

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Completion_BasisFrame
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rank-one frames associated with actual orthonormal and unbiased bases. -/

namespace MUB6.Weiner

open Matrix
open scoped BigOperators

lemma basisCoordinates_unit (b : MUB6.Basis) (a : Coord) :
    ∑ i, star (basisCoordinates b a i) * basisCoordinates b a i = 1 := by
  simpa only [basisCoordinates, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, mul_comm]
    using b.inner_eq_one a

lemma basisCoordinates_complete (b : MUB6.Basis) (i j : Coord) :
    ∑ a, basisCoordinates b a i * star (basisCoordinates b a j) =
      if i = j then 1 else 0 := by
  have h := (EuclideanSpace.basisFun Coord ℂ).toMatrix_orthonormalBasis_self_mul_conjTranspose b
  have hij := congrArg (fun A : CMatrix => A i j) h
  simpa [basisCoordinates, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Module.Basis.toMatrix_apply, Matrix.one_apply] using hij

lemma basis_projectorVector_sum (b : MUB6.Basis) :
    (∑ a, projectorVector (basisCoordinates b a)) = traceVector := by
  funext p
  simpa only [Finset.sum_apply, projectorVector, traceVector] using
    basisCoordinates_complete b p.1 p.2

lemma traceVector_outer : Matrix.vecMulVec traceVector (star traceVector) =
    (traceMatrix : Matrix (Coord × Coord) (Coord × Coord) ℂ) := by
  ext p q
  by_cases hp : p.1 = p.2 <;> by_cases hq : q.1 = q.2 <;>
    simp [Matrix.vecMulVec_apply, traceVector, traceMatrix, hp, hq]

lemma basis_projector_inner (b c : MUB6.Basis) (a d : Coord) :
    star (projectorVector (basisCoordinates b a)) ⬝ᵥ
      projectorVector (basisCoordinates c d) =
        inner ℂ (b a) (c d) * star (inner ℂ (b a) (c d)) := by
  rw [projectorVector_inner]
  have h : star (basisCoordinates b a) ⬝ᵥ basisCoordinates c d = inner ℂ (b a) (c d) := by
    change star (b a).ofLp ⬝ᵥ (c d).ofLp = inner ℂ (b a) (c d)
    rw [dotProduct_comm]
    exact (EuclideanSpace.inner_eq_star_dotProduct (b a) (c d)).symm
  rw [h]

lemma basis_pinching_idempotent (b : MUB6.Basis) :
    pinchingMatrix (basisCoordinates b) * pinchingMatrix (basisCoordinates b) =
      pinchingMatrix (basisCoordinates b) := by
  simp only [pinchingMatrix_eq_frameOperator]
  apply frameOperator_idempotent
  intro a c
  rw [basis_projector_inner]
  rw [b.inner_eq_ite]
  split_ifs <;> simp

lemma mub_pinching_mul {m : ℕ} (B : Fin m → MUB6.Basis) (hB : IsMUBFamily B)
    (r s : Fin m) (hrs : r ≠ s) :
    pinchingMatrix (basisCoordinates (B r)) * pinchingMatrix (basisCoordinates (B s)) =
      (1 / 6 : ℂ) • (traceMatrix : Matrix (Coord × Coord) (Coord × Coord) ℂ) := by
  rw [pinchingMatrix_eq_frameOperator, pinchingMatrix_eq_frameOperator]
  have hov : ∀ a b, star (projectorVector (basisCoordinates (B r) a)) ⬝ᵥ
      projectorVector (basisCoordinates (B s) b) = (1 / 6 : ℂ) := by
    intro a b
    rw [basis_projector_inner]
    rw [Complex.star_def, Complex.mul_conj, hB r s hrs a b]
    norm_num
  have h := frameOperator_mul
    (fun a => projectorVector (basisCoordinates (B r) a))
    (fun b => projectorVector (basisCoordinates (B s) b)) (1 / 6 : ℂ) hov
  rwa [basis_projectorVector_sum, basis_projectorVector_sum, traceVector_outer] at h

lemma basis_pinching_unital (b : MUB6.Basis) :
    applySuper (pinchingMatrix (basisCoordinates b)) 1 = 1 :=
  pinchingMatrix_unital (basisCoordinates b) (basisCoordinates_unit b) (basisCoordinates_complete b)

lemma basis_pinching_trace (b : MUB6.Basis) :
    (pinchingMatrix (basisCoordinates b)).trace = 6 := by
  simpa using pinchingMatrix_trace (basisCoordinates b) (basisCoordinates_unit b)

lemma basis_pinching_pair {m : ℕ} (B : Fin m → MUB6.Basis) (hB : IsMUBFamily B)
    (r s : Fin m) :
    pinchingMatrix (basisCoordinates (B r)) * pinchingMatrix (basisCoordinates (B s)) =
      if r = s then pinchingMatrix (basisCoordinates (B r))
      else (1 / 6 : ℂ) • traceMatrix := by
  split_ifs with h
  · subst s
    exact basis_pinching_idempotent (B r)
  · exact mub_pinching_mul B hB r s h

/-- The Hilbert--Schmidt complement vanishes for seven unbiased bases. -/
theorem complete_basis_complement_eq_zero (B : Fin 7 → MUB6.Basis) (hB : IsMUBFamily B) :
    complementMatrix (fun r => basisCoordinates (B r)) = 0 := by
  apply hermitian_idempotent_eq_zero_of_trace_zero
  · exact complementMatrix_hermitian _
  · exact seven_complement_idempotent _ (basis_pinching_pair B hB)
      (fun r => pinchingMatrix_hermitian (basisCoordinates (B r)))
      (fun r => basis_pinching_unital (B r))
  · norm_num [complementMatrix, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_sum,
      traceMatrix_trace, basis_pinching_trace]

/-- Entrywise fourth moment of a complete family of seven orthonormal bases. -/
theorem complete_basis_fourth_moment (B : Fin 7 → MUB6.Basis) (hB : IsMUBFamily B)
    (i j k l : Coord) :
    (∑ r, ∑ a, B r a i * star (B r a j) * star (B r a k) * B r a l) =
      (if i = k ∧ j = l then 1 else 0) + (if i = j ∧ k = l then 1 else 0) := by
  have h := congrArg (fun C : SuperSix => C (i, j) (k, l))
    (complete_basis_complement_eq_zero B hB)
  simp only [complementMatrix, Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply,
    Matrix.zero_apply] at h
  simpa only [pinchingMatrix, basisCoordinates, Matrix.one_apply, Prod.mk.injEq,
    traceMatrix] using (sub_eq_zero.mp h).symm

/-- A common unitary change of coordinates preserves mutual unbiasedness. -/
lemma isMUBFamily_map {m : ℕ} (B : Fin m → MUB6.Basis) (hB : IsMUBFamily B)
    (U : Space ≃ₗᵢ[ℂ] Space) : IsMUBFamily (fun r => (B r).map U) := by
  intro r s hrs i j
  simpa only [OrthonormalBasis.map_apply, LinearIsometryEquiv.inner_map_map] using hB r s hrs i j

/-- The complete-family fourth moment in coordinates of any reference basis. -/
theorem complete_basis_fourth_moment_relative (B : Fin 7 → MUB6.Basis) (hB : IsMUBFamily B)
    (ref : MUB6.Basis) (i j k l : Coord) :
    (∑ r, ∑ a, inner ℂ (ref i) (B r a) * star (inner ℂ (ref j) (B r a)) *
      star (inner ℂ (ref k) (B r a)) * inner ℂ (ref l) (B r a)) =
      (if i = k ∧ j = l then 1 else 0) + (if i = j ∧ k = l then 1 else 0) := by
  have h := complete_basis_fourth_moment (fun r => (B r).map ref.repr)
    (isMUBFamily_map B hB ref.repr) i j k l
  simpa only [OrthonormalBasis.map_apply, OrthonormalBasis.repr_apply_apply] using h

end MUB6.Weiner

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Fourier_Characters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_inv_eq_conj {z : ℂ} (hz : Complex.normSq z = 1) : z⁻¹ = conj z := by
  simp [Complex.inv_def, hz]

theorem character_neg (x : Coord → ℂ) (hx : ∀ i, Complex.normSq (x i) = 1)
    (a : Charge) : character x (-a) = conj (character x a) := by
  simp only [character, Pi.neg_apply, zpow_neg, map_prod, map_zpow₀]
  apply Finset.prod_congr rfl
  intro i _
  rw [← unit_inv_eq_conj (hx i), inv_zpow]

theorem g_neg {H : CMatrix} (hH : IsHadamard H) (a : Charge) :
    g H (-a) = conj (g H a) := by
  simp only [g, character_neg _ (fun i => hH.1 i _) a, map_mul, map_sum,
    map_inv₀, map_ofNat]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Hadamard
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix

namespace MUB6

theorem IsHadamard.row_gram {H : CMatrix} (hH : IsHadamard H) :
    H * Hᴴ = (6 : ℂ) • (1 : CMatrix) := by
  have hl : ((6 : ℂ)⁻¹ • Hᴴ) * H = (1 : CMatrix) := by
    rw [smul_mul_assoc, hH.2, smul_smul]
    norm_num
  have hr := mul_eq_one_comm.mp hl
  rw [mul_smul_comm] at hr
  have hs := congrArg (fun M : CMatrix => (6 : ℂ) • M) hr
  simpa only [smul_smul, mul_inv_cancel₀ (by norm_num : (6 : ℂ) ≠ 0), one_smul]
    using hs

theorem IsHadamard.row_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, H i k * conj (H j k) = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.row_gram
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem character_single (x : Coord → ℂ) (i : Coord) (n : ℤ) :
    character x (Pi.single i n) = x i ^ n := by
  classical
  simp [character, Pi.single_apply]

theorem character_difference (x : Coord → ℂ) (hx : ∀ k, Complex.normSq (x k) = 1)
    (i j : Coord) : character x (difference i j) = x i * conj (x j) := by
  rw [difference, sub_eq_add_neg, character_add x (fun k => unit_ne_zero (hx k)),
    character_neg x hx, character_single, character_single]
  simp

theorem g_difference {H : CMatrix} (hH : IsHadamard H) (i j : Coord) :
    g H (difference i j) = if i = j then 1 else 0 := by
  simp only [g, character_difference _ (fun k => hH.1 k _)]
  rw [hH.row_orthogonal]
  split_ifs <;> norm_num

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Bases_Transitions
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem sqrt_six_square : (Real.sqrt 6 : ℂ) ^ 2 = 6 := by
  have h : Real.sqrt 6 ^ 2 = (6 : ℝ) := Real.sq_sqrt (by norm_num)
  exact_mod_cast h

theorem sqrt_six_normSq : Complex.normSq (Real.sqrt 6 : ℂ) = 6 := by
  rw [Complex.normSq_ofReal]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]

theorem transition_column_inner (b c d : Basis) (k l : Coord) :
    (∑ i, conj (transition b c i k) * transition b d i l) =
      6 * inner ℂ (c k) (d l) := by
  have hterm (i : Coord) : conj (transition b c i k) * transition b d i l =
      6 * (inner ℂ (c k) (b i) * inner ℂ (b i) (d l)) := by
    simp only [transition, map_mul, Complex.conj_ofReal, inner_conj_symm]
    calc
      _ = (Real.sqrt 6 : ℂ) ^ 2 *
        (inner ℂ (c k) (b i) * inner ℂ (b i) (d l)) := by ring
      _ = _ := by rw [sqrt_six_square]
  simp_rw [hterm]
  rw [← Finset.mul_sum, b.sum_inner_mul_inner]

theorem transition_isHadamard {m : ℕ} (B : Fin m → Basis) (hB : IsMUBFamily B)
    (r s : Fin m) (hrs : r ≠ s) : IsHadamard (transition (B r) (B s)) := by
  refine ⟨?_, ?_⟩
  · intro i k
    rw [transition, map_mul, sqrt_six_normSq, hB r s hrs i k]
    norm_num
  · ext i j
    change (∑ k, conj (transition (B r) (B s) k i) * transition (B r) (B s) k j) =
      (6 : ℂ) * (if i = j then 1 else 0)
    rw [transition_column_inner, (B s).inner_eq_ite]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Fourier_ChargeDecomposition
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

theorem weightMultiset_card (w : Coord → ℕ) :
    (weightMultiset w).card = ∑ i, w i := by
  have h (s : Finset Coord) : (∑ i ∈ s, Multiset.replicate (w i) i).card = ∑ i ∈ s, w i := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [Finset.sum_insert hi, Multiset.card_add, ih]
  exact h Finset.univ

theorem weightMultiset_count (w : Coord → ℕ) (k : Coord) :
    (weightMultiset w).count k = w k := by
  have h (s : Finset Coord) :
      (∑ i ∈ s, Multiset.replicate (w i) i).count k = ∑ i ∈ s, if i = k then w i else 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [Finset.sum_insert hi, Multiset.count_add, Multiset.count_replicate, ih]
  simpa [weightMultiset] using h Finset.univ

theorem positivePositions_card (a : Charge) : (positivePositions a).card = order a :=
  weightMultiset_card _

theorem negativePositions_card {a : Charge} (ha : Balanced a) :
    (negativePositions a).card = order a := by
  have h : (∑ i, ((a i).toNat : ℤ)) - ∑ i, ((-a i).toNat : ℤ) = 0 := by
    rw [← Finset.sum_sub_distrib]
    simpa only [Int.toNat_sub_toNat_neg] using (show ∑ i, a i = 0 from ha)
  rw [negativePositions, weightMultiset_card, order]
  exact_mod_cast (sub_eq_zero.mp h).symm

theorem charge_eq_counts (a : Charge) (k : Coord) :
    a k = ((positivePositions a).count k : ℤ) - (negativePositions a).count k := by
  rw [positivePositions, negativePositions, weightMultiset_count, weightMultiset_count]
  exact (Int.toNat_sub_toNat_neg _).symm

theorem positive_negative_ne {a : Charge} {i j : Coord}
    (hi : i ∈ positivePositions a) (hj : j ∈ negativePositions a) : i ≠ j := by
  intro h
  subst j
  rw [← Multiset.count_pos, positivePositions, weightMultiset_count] at hi
  rw [← Multiset.count_pos, negativePositions, weightMultiset_count] at hj
  have hp := Int.pos_iff_toNat_pos.mpr hi
  have hn := Int.pos_iff_toNat_pos.mpr hj
  omega

/-- A balanced charge of order one is one positive and one negative coordinate. -/
theorem order_one_decomposition {a : Charge} (ha : Balanced a) (ho : order a = 1) :
    ∃ i j, i ≠ j ∧ a = difference i j := by
  obtain ⟨i, hi⟩ := Multiset.card_eq_one.mp ((positivePositions_card a).trans ho)
  obtain ⟨j, hj⟩ := Multiset.card_eq_one.mp ((negativePositions_card ha).trans ho)
  refine ⟨i, j, positive_negative_ne (a := a) (by simp [hi]) (by simp [hj]), ?_⟩
  funext k
  rw [charge_eq_counts a k, hi, hj]
  simp [difference, Pi.single_apply, Multiset.count_singleton, eq_comm]

/-- An order-two charge has two positive and two negative positions, allowing
repetitions on either side but no cancellation between the sides. -/
theorem order_two_decomposition {a : Charge} (ha : Balanced a) (ho : order a = 2) :
    ∃ i l j k, i ≠ j ∧ i ≠ k ∧ l ≠ j ∧ l ≠ k ∧
      a = difference i j + difference l k := by
  obtain ⟨i, l, hi⟩ := Multiset.card_eq_two.mp ((positivePositions_card a).trans ho)
  obtain ⟨j, k, hj⟩ := Multiset.card_eq_two.mp ((negativePositions_card ha).trans ho)
  have hip : i ∈ positivePositions a := by simp [hi]
  have hlp : l ∈ positivePositions a := by simp [hi]
  have hjn : j ∈ negativePositions a := by simp [hj]
  have hkn : k ∈ negativePositions a := by simp [hj]
  refine ⟨i, l, j, k, positive_negative_ne hip hjn, positive_negative_ne hip hkn,
    positive_negative_ne hlp hjn, positive_negative_ne hlp hkn, ?_⟩
  funext t
  rw [charge_eq_counts a t, hi, hj]
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton,
    Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Pi.add_apply,
    difference, Pi.sub_apply, Pi.single_apply]
  split_ifs <;> omega

theorem g_order_one {H : CMatrix} (hH : IsHadamard H) {a : Charge}
    (ha : Balanced a) (ho : order a = 1) : g H a = 0 := by
  obtain ⟨i, j, hij, rfl⟩ := order_one_decomposition ha ho
  simp [g_difference hH, hij]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Bases_CompleteFamily
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem relativeMatrix_isHadamard (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (s : Coord) : IsHadamard (relativeMatrix B r s) :=
  transition_isHadamard B hB r (r.succAbove s) (r.ne_succAbove s)

theorem relativeMatrix_order_two_expansion (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (s i j k l : Coord) :
    g (relativeMatrix B r s) (difference i j + difference l k) =
      6 * ∑ a, fourthProduct (B r) (B (r.succAbove s)) i j k l a := by
  have hH := relativeMatrix_isHadamard B hB r s
  have ht (a : Coord) :
      (relativeMatrix B r s i a * conj (relativeMatrix B r s j a)) *
        (relativeMatrix B r s l a * conj (relativeMatrix B r s k a)) =
      36 * fourthProduct (B r) (B (r.succAbove s)) i j k l a := by
    simp only [relativeMatrix, transition, map_mul, Complex.conj_ofReal,
      fourthProduct, Complex.star_def]
    calc
      _ = ((Real.sqrt 6 : ℂ) ^ 2) ^ 2 *
          (inner ℂ (B r i) (B (r.succAbove s) a) *
            conj (inner ℂ (B r j) (B (r.succAbove s) a)) *
            conj (inner ℂ (B r k) (B (r.succAbove s) a)) *
            inner ℂ (B r l) (B (r.succAbove s) a)) := by ring
      _ = _ := by rw [sqrt_six_square]; ring
  simp only [g, character_add _ (fun i => unit_ne_zero (hH.1 i _)),
    character_difference _ (fun i => hH.1 i _)]
  simp_rw [ht]
  rw [← Finset.mul_sum]
  ring

theorem fourthProduct_self_zero (b : Basis) (i j k l : Coord) (hij : i ≠ j) :
    ∑ a, fourthProduct b b i j k l a = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  have hz : inner ℂ (b i) (b a) * star (inner ℂ (b j) (b a)) = 0 := by
    rw [b.inner_eq_ite, b.inner_eq_ite]
    split_ifs <;> simp_all
  simp only [fourthProduct, hz, zero_mul]

/-- The order-two Fourier sum identity of a complete mutually unbiased family. -/
theorem complete_family_order_two (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) {a : Charge} (ha : Balanced a) (ho : order a = 2) :
    ∑ s, g (relativeMatrix B r s) a = 0 := by
  obtain ⟨i, l, j, k, hij, hik, _, _, rfl⟩ := order_two_decomposition ha ho
  have h := Weiner.complete_basis_fourth_moment_relative B hB (B r) i j k l
  change (∑ s, ∑ t, fourthProduct (B r) (B s) i j k l t) = _ at h
  rw [ite_eq_right (by simp [hik]), ite_eq_right (by simp [hij]), add_zero,
    Fin.sum_univ_succAbove _ r, fourthProduct_self_zero _ _ _ _ _ hij, zero_add] at h
  simp_rw [relativeMatrix_order_two_expansion B hB]
  rw [← Finset.mul_sum, h, mul_zero]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_CompareMerge
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse collection needs only a computable comparison, not order axioms.
The comparison changes the representation but never its real evaluation. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*} [DecidableEq ι]

theorem eval_mergeByFuel (less : ι → ι → Bool) (fuel : ℕ)
    (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeByFuel less fuel a b) x = eval a x + eval b x := by
  induction fuel generalizing a b with
  | zero => simp [mergeByFuel]
  | succ fuel ih =>
    cases a with
    | nil => simp [mergeByFuel]
    | cons a as =>
      cases b with
      | nil => simp [mergeByFuel]
      | cons b bs =>
        simp only [mergeByFuel]
        split_ifs with hlt heq hz
        · simp only [eval_cons, ih]
          ring
        · simp only [ih, eval_cons]
          have hc : (a.2 : ℝ) + (b.2 : ℝ) = 0 := by exact_mod_cast hz
          have hcx := congrArg (fun z : ℝ => z * x b.1) hc
          simp only [add_mul, zero_mul] at hcx
          rw [heq]
          linarith
        · simp only [eval_cons, ih, Int.cast_add]
          rw [heq]
          ring
        · simp only [eval_cons, ih]
          ring

@[simp] theorem eval_mergeBy (less : ι → ι → Bool) (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeBy less a b) x = eval a x + eval b x := eval_mergeByFuel _ _ _ _ _

omit [DecidableEq ι] in
theorem eval_flatten (vs : List (Sparse ι)) (x : ι → ℝ) :
    eval vs.flatten x = (vs.map (fun v => eval v x)).sum := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [ih]

theorem eval_mergePairs (less : ι → ι → Bool) (vs : List (Sparse ι)) (x : ι → ℝ) :
    ((mergePairs less vs).map (fun v => eval v x)).sum =
      (vs.map (fun v => eval v x)).sum := by
  induction vs using mergePairs.induct with
  | case1 => rfl
  | case2 a => rfl
  | case3 a b rest ih => simp [mergePairs, ih, add_assoc]

theorem eval_collectLevels (less : ι → ι → Bool) (fuel : ℕ)
    (vs : List (Sparse ι)) (x : ι → ℝ) :
    eval (collectLevels less fuel vs) x = (vs.map (fun v => eval v x)).sum := by
  induction fuel generalizing vs with
  | zero => exact eval_flatten vs x
  | succ fuel ih =>
    cases vs with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => simp [collectLevels]
      | cons b rest =>
        rw [collectLevels, ih, eval_mergePairs]

@[simp] theorem eval_collectBalanced (less : ι → ι → Bool) (v : Sparse ι) (x : ι → ℝ) :
    eval (collectBalanced less v) x = eval v x := by
  rw [collectBalanced, eval_collectLevels]
  simp [eval, Function.comp_def]

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Averages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MUB6

theorem average_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (f : κ → ℝ) : average (f ∘ e) = average f := by
  simp only [average, Fintype.card_congr e, Function.comp_apply, e.sum_comp]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_AverageAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem average_congr {f g : ι → ℝ} (h : ∀ i, f i = g i) :
    average f = average g := by
  congr 1
  exact funext h

theorem average_add (f g : ι → ℝ) :
    average (fun i => f i + g i) = average f + average g := by
  simp [average, Finset.sum_add_distrib, mul_add]

theorem average_mul (c : ℝ) (f : ι → ℝ) :
    average (fun i => c * f i) = c * average f := by
  simp only [average, ← Finset.mul_sum]
  ring

theorem average_sum (f : ι → κ → ℝ) :
    average (fun i => ∑ k, f i k) = ∑ k, average (fun i => f i k) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite sampling identities. The splitting theorem below is the counting
step behind contraction of an order-one row; it is independent of the values
of the matrix entries and uses no certificate data. -/

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace MUB6.Sampling

variable {A B V : Type*} [Fintype A] [Fintype B] [AddCommMonoid V]

theorem sum_split_embedding (e : A ↪ B) (f : B → V) :
    (∑ b, f b) = (∑ a, f (e a)) + ∑ b : {b // b ∉ Set.range e}, f b := by
  classical
  let E : A ⊕ {b // b ∉ Set.range e} ≃ B :=
    (e.toEquivRange.sumCongr (Equiv.refl _)).trans (Equiv.sumCompl (· ∈ Set.range e))
  have h := E.sum_comp f
  simpa [E, Fintype.sum_sum_type, Equiv.trans_apply, Equiv.sumCongr_apply] using h.symm

theorem sum_injective_extension {p : ℕ} (f : (Fin p ↪ B) → B → V) :
    (∑ e : Fin (p + 1) ↪ B, f (dropFirst e) (e 0)) =
      ∑ e : Fin p ↪ B, ∑ b : {b // b ∉ Set.range e}, f e b := by
  classical
  have h := (Equiv.embeddingFinSucc p B).sum_comp
    (fun x : Σ e : Fin p ↪ B, {b // b ∉ Set.range e} => f x.1 x.2)
  simpa [dropFirst, Fintype.sum_sigma] using h

theorem sum_samples_split {p : ℕ} (f : (Fin p ↪ B) → B → V) :
    (∑ e : Fin p ↪ B, ∑ b, f e b) =
      (∑ e : Fin p ↪ B, ∑ j, f e (e j)) +
      ∑ e : Fin (p + 1) ↪ B, f (dropFirst e) (e 0) := by
  classical
  calc
    _ = ∑ e : Fin p ↪ B,
        ((∑ j, f e (e j)) + ∑ b : {b // b ∉ Set.range e}, f e b) := by
      apply Finset.sum_congr rfl
      intro e _
      exact sum_split_embedding e (f e)
    _ = _ := by rw [Finset.sum_add_distrib, sum_injective_extension]

theorem sum_contraction {p : ℕ} (f : (Fin p ↪ B) → B → V)
    (h : ∀ e, ∑ b, f e b = 0) :
    (∑ j : Fin p, ∑ e : Fin p ↪ B, f e (e j)) +
      (∑ e : Fin (p + 1) ↪ B, f (dropFirst e) (e 0)) = 0 := by
  classical
  rw [Finset.sum_comm]
  rw [← sum_samples_split]
  simp [h]

end MUB6.Sampling

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_SamplingAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace MUB6.Sampling

theorem unused_card {p n : ℕ} (e : Fin p ↪ Fin n)
    [Fintype {i // i ∉ Set.range e}] :
    Fintype.card {i // i ∉ Set.range e} = n - p := by
  rw [Fintype.card_subtype_compl]
  have hr : Fintype.card {i // i ∈ Set.range e} = p := by
    rw [Fintype.card_range, Fintype.card_fin]
  rw [hr, Fintype.card_fin]

theorem embedding_succ_card (p n : ℕ) :
    Fintype.card (Fin (p + 1) ↪ Fin n) =
      Fintype.card (Fin p ↪ Fin n) * (n - p) := by
  rw [Fintype.card_congr (Equiv.embeddingFinSucc p (Fin n)), Fintype.card_sigma]
  simp only [unused_card, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]

theorem sum_dropFirst {p n : ℕ} (f : (Fin p ↪ Fin n) → ℝ) :
    (∑ e : Fin (p + 1) ↪ Fin n, f (dropFirst e)) =
      (n - p : ℕ) * ∑ e, f e := by
  have hs := sum_injective_extension (fun e (_ : Fin n) => f e)
  rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [Fintype.card_subtype_compl, Fintype.card_range, Fintype.card_fin, Fintype.card_fin]

/-- Deleting a coordinate of a uniform injection leaves a uniform injection. -/
theorem average_dropFirst {p n : ℕ} (hp : p < n) (f : (Fin p ↪ Fin n) → ℝ) :
    average (fun e : Fin (p + 1) ↪ Fin n => f (dropFirst e)) = average f := by
  have hd : ((n - p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt hp)
  unfold average
  rw [embedding_succ_card, Nat.cast_mul, sum_dropFirst, mul_inv_rev]
  calc
    _ = (((n - p : ℕ) : ℝ)⁻¹ * (n - p : ℕ)) *
        ((Fintype.card (Fin p ↪ Fin n) : ℝ)⁻¹ * ∑ e, f e) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hd, one_mul]

/-- The normalized counting identity used for an order-one contraction.
At most n rows are sampled; the saturated boundary case is separate. -/
theorem average_contraction {p n : ℕ} (hp : p < n)
    (f : (Fin p ↪ Fin n) → Fin n → ℝ) (h : ∀ e, ∑ b, f e b = 0) :
    ((n - p : ℕ) : ℝ) *
      average (fun e : Fin (p + 1) ↪ Fin n => f (dropFirst e) (e 0)) +
      (∑ j : Fin p, average (fun e : Fin p ↪ Fin n => f e (e j))) = 0 := by
  have hd : ((n - p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt hp)
  have hc : ((n - p : ℕ) : ℝ) * (Fintype.card (Fin (p + 1) ↪ Fin n) : ℝ)⁻¹ =
      (Fintype.card (Fin p ↪ Fin n) : ℝ)⁻¹ := by
    rw [embedding_succ_card, Nat.cast_mul, mul_inv_rev]
    rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  have hs := sum_contraction f h
  simp only [average]
  rw [← mul_assoc, hc, ← Finset.mul_sum, ← mul_add]
  rw [add_comm] at hs
  rw [hs, mul_zero]

end MUB6.Sampling

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_EmbeddedCharge
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem embedCharge_outside {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) (i : Coord)
    (hi : i ∉ Set.range ρ) : embedCharge ρ a i = 0 :=
  Function.extend_apply' _ _ _ hi

theorem embedCharge_sum {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    ∑ i, embedCharge ρ a i = ∑ i, a i := by
  symm
  exact Fintype.sum_of_injective ρ ρ.injective a (embedCharge ρ a)
    (embedCharge_outside ρ a) (fun i => (embedCharge_apply ρ a i).symm)

theorem embedCharge_order {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    order (embedCharge ρ a) = ∑ i, (a i).toNat := by
  symm
  apply Fintype.sum_of_injective ρ ρ.injective (fun i => (a i).toNat)
    (fun i => (embedCharge ρ a i).toNat)
  · intro i hi
    rw [embedCharge_outside ρ a i hi]
    rfl
  · intro i
    rw [embedCharge_apply]

theorem embedCharge_neg {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    embedCharge ρ (-a) = -embedCharge ρ a := by
  funext i
  by_cases hi : i ∈ Set.range ρ
  · obtain ⟨j, rfl⟩ := hi
    simp
  · simp [Pi.neg_apply, embedCharge_outside ρ _ i hi]

theorem character_embedCharge {p : ℕ} (x : Coord → ℂ) (ρ : Fin p ↪ Coord)
    (a : Fin p → ℤ) : character x (embedCharge ρ a) = ∏ i, x (ρ i) ^ a i := by
  symm
  apply Fintype.prod_of_injective ρ ρ.injective (fun i => x (ρ i) ^ a i)
    (fun i => x i ^ embedCharge ρ a i)
  · intro i hi
    rw [embedCharge_outside ρ a i hi, zpow_zero]
  · intro i
    rw [embedCharge_apply]

theorem rowFourier_eq_g {p : ℕ} (H : CMatrix) (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    rowFourier H ρ a = g H (embedCharge ρ a) := by
  simp only [rowFourier, g, character_embedCharge]

theorem rowFourier_neg {p : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    rowFourier H ρ (-a) = conj (rowFourier H ρ a) := by
  rw [rowFourier_eq_g, embedCharge_neg, g_neg hH, rowFourier_eq_g]

theorem rowFourier_order_one {p : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) (ha : ∑ i, a i = 0)
    (ho : ∑ i, (a i).toNat = 1) : rowFourier H ρ a = 0 := by
  rw [rowFourier_eq_g]
  apply g_order_one hH
  · exact (embedCharge_sum ρ a).trans ha
  · exact (embedCharge_order ρ a).trans ho

theorem complete_family_row_order_two {p : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) (ha : ∑ i, a i = 0)
    (ho : ∑ i, (a i).toNat = 2) : ∑ s, rowFourier (relativeMatrix B r s) ρ a = 0 := by
  simp only [rowFourier_eq_g]
  exact complete_family_order_two B hB r ((embedCharge_sum ρ a).trans ha)
    ((embedCharge_order ρ a).trans ho)

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedMoments
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem mixedMoment_neg {p n l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) :
    mixedMoment B (-A) label = mixedMoment B A label := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  have h : mixedIntegrand B (-A) label r ρ τ = conj (mixedIntegrand B A label r ρ τ) := by
    unfold mixedIntegrand
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro j _
    exact rowFourier_neg (relativeMatrix_isHadamard B hB r _) ρ _
  rw [h, Complex.conj_re]

theorem mixedMoment_factor_permutation {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) (σ : Equiv.Perm (Fin n)) :
    mixedMoment B (fun i j => A i (σ j)) (label ∘ σ) = mixedMoment B A label := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  exact congrArg Complex.re (Equiv.prod_comp σ
    (fun j => rowFourier (relativeMatrix B r (τ (label j))) ρ (fun i => A i j)))

theorem rowFourier_row_permutation {p : ℕ} (H : CMatrix) (a : Fin p → ℤ)
    (σ : Equiv.Perm (Fin p)) (ρ : Fin p ↪ Coord) :
    rowFourier H ρ (a ∘ σ) =
      rowFourier H (Equiv.embeddingCongr σ (Equiv.refl Coord) ρ) a := by
  unfold rowFourier
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simpa only [Equiv.embeddingCongr_apply, Function.Embedding.congr_apply,
    Function.comp_apply, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.refl_apply, Equiv.symm_apply_apply] using
    Equiv.prod_comp σ (fun i => H (ρ (σ.symm i)) k ^ a i)

theorem mixedMoment_row_permutation {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) (σ : Equiv.Perm (Fin p)) :
    mixedMoment B (fun i j => A (σ i) j) label = mixedMoment B A label := by
  apply average_congr
  intro r
  have h (ρ : Fin p ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B (fun i j => A (σ i) j) label r ρ τ =
        mixedIntegrand B A label r (Equiv.embeddingCongr σ (Equiv.refl Coord) ρ) τ := by
    apply Finset.prod_congr rfl
    intro j _
    exact rowFourier_row_permutation _ (fun i => A i j) σ ρ
  simp_rw [h]
  exact average_equiv (Equiv.embeddingCongr σ (Equiv.refl Coord))
    (fun ρ : Fin p ↪ Coord => average (fun τ : Fin l ↪ Coord =>
      (mixedIntegrand B A label r ρ τ).re))

theorem mixedMoment_label_permutation {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) (σ : Equiv.Perm (Fin l)) :
    mixedMoment B A (σ ∘ label) = mixedMoment B A label := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  have h (τ : Fin l ↪ Coord) : mixedIntegrand B A (σ ∘ label) r ρ τ =
      mixedIntegrand B A label r ρ (Equiv.embeddingCongr σ.symm (Equiv.refl Coord) τ) := by
    rfl
  simp_rw [h]
  exact average_equiv (Equiv.embeddingCongr σ.symm (Equiv.refl Coord))
    (fun τ : Fin l ↪ Coord => (mixedIntegrand B A label r ρ τ).re)

theorem mixedMoment_order_one {p n l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) (j : Fin n)
    (ha : ∑ i, A i j = 0) (ho : ∑ i, (A i j).toNat = 1) : mixedMoment B A label = 0 := by
  have h (r : Fin 7) (ρ : Fin p ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B A label r ρ τ = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact rowFourier_order_one (relativeMatrix_isHadamard B hB r _) ρ _ ha ho
  simp [mixedMoment, h]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedAlpha
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

theorem rowFourier_alpha_zero {H : CMatrix} (hH : FourierZero H)
    (ρ : Coord ↪ Coord) (σ : Equiv.Perm Coord) :
    rowFourier H ρ (permuteCharge σ alpha) = 0 := by
  rw [permuteCharge, rowFourier_row_permutation]
  let e : Coord ↪ Coord := Equiv.embeddingCongr σ (Equiv.refl Coord) ρ
  let π : Equiv.Perm Coord := Equiv.ofBijective e
    ⟨e.injective, Finite.surjective_of_injective e.injective⟩
  exact hH π

theorem mixedMoment_alpha {n l : ℕ} (B : Fin 7 → Basis) (hB : AllTransitionsFourierZero B)
    (A : Matrix Coord (Fin n) ℤ) (label : Fin n → Fin l) (j : Fin n)
    (σ : Equiv.Perm Coord) (hA : (fun i => A i j) = permuteCharge σ alpha) :
    mixedMoment B A label = 0 := by
  have h (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B A label r ρ τ = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [hA]
    exact rowFourier_alpha_zero (hB r _) ρ σ
  simp [mixedMoment, h]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem mixedMoment_unused_first_label {p n l : ℕ} (hl : l < 6) (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) :
    mixedMoment B A (Fin.succ ∘ label) = mixedMoment B A label := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  change average (fun τ : Fin (l + 1) ↪ Coord =>
    (mixedIntegrand B A label r ρ (Sampling.dropFirst τ)).re) = _
  exact Sampling.average_dropFirst hl
    (fun τ : Fin l ↪ Coord => (mixedIntegrand B A label r ρ τ).re)

/-- The source singleton-label contraction, before dividing by its positive
integer coefficient. The first factor has order two and its own label. -/
theorem mixedMoment_singleton_first {p n l : ℕ} (hl : l < 6)
    (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (A : Matrix (Fin p) (Fin (n + 1)) ℤ) (label : Fin n → Fin l)
    (ha : ∑ i, A i 0 = 0) (ho : ∑ i, (A i 0).toNat = 2) :
    ((6 - l : ℕ) : ℝ) * mixedMoment B A (Fin.cases 0 (Fin.succ ∘ label)) +
      (∑ j : Fin l, mixedMoment B A (Fin.cases j label)) = 0 := by
  let f (r : Fin 7) (ρ : Fin p ↪ Coord) (τ : Fin l ↪ Coord) (s : Coord) : ℝ :=
    (rowFourier (relativeMatrix B r s) ρ (fun i => A i 0) *
      mixedIntegrand B (fun i j => A i j.succ) label r ρ τ).re
  have hs (r : Fin 7) (ρ : Fin p ↪ Coord) (τ : Fin l ↪ Coord) : ∑ s, f r ρ τ s = 0 := by
    simp only [f, ← Complex.re_sum, ← Finset.sum_mul,
      complete_family_row_order_two B hB r ρ (fun i => A i 0) ha ho, zero_mul, Complex.zero_re]
  have hnew (r : Fin 7) (ρ : Fin p ↪ Coord) (τ : Fin (l + 1) ↪ Coord) :
      f r ρ (Sampling.dropFirst τ) (τ 0) =
        (mixedIntegrand B A (Fin.cases 0 (Fin.succ ∘ label)) r ρ τ).re := by
    simp only [f, mixedIntegrand, Fin.prod_univ_succ, Fin.cases_zero, Fin.cases_succ,
      Function.comp_apply, Sampling.dropFirst_apply]
  have hold (r : Fin 7) (ρ : Fin p ↪ Coord) (τ : Fin l ↪ Coord) (j : Fin l) :
      f r ρ τ (τ j) = (mixedIntegrand B A (Fin.cases j label) r ρ τ).re := by
    simp only [f, mixedIntegrand, Fin.prod_univ_succ, Fin.cases_zero, Fin.cases_succ]
  have hc (r : Fin 7) (ρ : Fin p ↪ Coord) :
      ((6 - l : ℕ) : ℝ) * average (fun τ : Fin (l + 1) ↪ Coord =>
        (mixedIntegrand B A (Fin.cases 0 (Fin.succ ∘ label)) r ρ τ).re) +
      (∑ j : Fin l, average (fun τ : Fin l ↪ Coord =>
        (mixedIntegrand B A (Fin.cases j label) r ρ τ).re)) = 0 := by
    have h := Sampling.average_contraction hl (f r ρ) (hs r ρ)
    simpa only [hnew, hold] using h
  calc
    _ = average (fun r : Fin 7 => average (fun ρ : Fin p ↪ Coord =>
      ((6 - l : ℕ) : ℝ) * average (fun τ : Fin (l + 1) ↪ Coord =>
        (mixedIntegrand B A (Fin.cases 0 (Fin.succ ∘ label)) r ρ τ).re) +
      (∑ j : Fin l, average (fun τ : Fin l ↪ Coord =>
        (mixedIntegrand B A (Fin.cases j label) r ρ τ).re)))) := by
      simp only [average_add, average_mul, average_sum, mixedMoment]
    _ = 0 := by simp only [hc, average_zero]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedLabelEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6

/-- Injective renaming, including adding unused labels, preserves the moment. -/
theorem mixedMoment_label_embedding {p n l k : ℕ} (hk : k ≤ 6) (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (e : Fin l ↪ Fin k) (label : Fin n → Fin l) :
    mixedMoment B A (e ∘ label) = mixedMoment B A label := by
  have hcard : l ≤ k := by
    simpa using Fintype.card_le_of_injective e e.injective
  induction k generalizing l with
  | zero =>
      have hl : l = 0 := Nat.eq_zero_of_le_zero hcard
      subst l
      have he : e ∘ label = label := funext fun j => Fin.elim0 (label j)
      rw [he]
  | succ k ih =>
      by_cases hl : l = k + 1
      · subst l
        let σ : Equiv.Perm (Fin (k + 1)) := Equiv.ofBijective e
          ⟨e.injective, Finite.surjective_of_injective e.injective⟩
        exact mixedMoment_label_permutation B A label σ
      · have hlk : l ≤ k := by omega
        let f : Fin l ↪ Fin k := Fin.castLEEmb hlk
        obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
          (fun i => (f i).succ) e (fun _ _ h => f.injective (Fin.succ_inj.mp h)) e.injective
        have he : e ∘ label = σ ∘ (Fin.succ ∘ (f ∘ label)) := by
          funext j
          exact (hσ (label j)).symm
        rw [he, mixedMoment_label_permutation,
          mixedMoment_unused_first_label (show k < 6 by omega)]
        exact ih (by omega) f label hlk

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Rules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Sound rules for mixed certificate normalization

Generated witnesses may only permute rows or factors, negate all charges,
remove zero rows or factors, and injectively rename labels. The equalities
here justify those operations for the actual finite mixed moments.
-/

noncomputable section
open scoped BigOperators

namespace MUB6.Certificate.MixedSemantics

theorem permute {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l)
    (ρ : Equiv.Perm (Fin p)) (σ : Equiv.Perm (Fin n)) :
    mixedMoment B A label = mixedMoment B (fun i j => A (ρ i) (σ j)) (label ∘ σ) := by
  rw [mixedMoment_factor_permutation B (fun i j => A (ρ i) j) label σ,
    mixedMoment_row_permutation]

theorem rename_labels {p n l k : ℕ} (hk : k ≤ 6) (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin k)
    (small : Fin n → Fin l) (e : Fin l ↪ Fin k) (h : label = e ∘ small) :
    mixedMoment B A label = mixedMoment B A small := by
  rw [h]
  exact mixedMoment_label_embedding hk B A e small

theorem singleton_first {p n l : ℕ} (hl : l < 6)
    (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (A : Matrix (Fin p) (Fin (n + 1)) ℤ) (label : Fin n → Fin l)
    (ha : ∑ i, A i 0 = 0) (ho : ∑ i, (A i 0).toNat = 2) :
    mixedMoment B A (Fin.cases 0 (Fin.succ ∘ label)) =
      - (((6 - l : ℕ) : ℝ)⁻¹) * ∑ j : Fin l, mixedMoment B A (Fin.cases j label) := by
  have h := mixedMoment_singleton_first hl B hB A label ha ho
  have hd : ((6 - l : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt hl)
  apply (eq_neg_iff_add_eq_zero).2 at h
  have heq := congrArg (fun x : ℝ => ((6 - l : ℕ) : ℝ)⁻¹ * x) h
  simpa only [← mul_assoc, inv_mul_cancel₀ hd, one_mul, mul_neg, neg_mul] using heq

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2268 raw2268Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw2268 raw2268Labels = mixedMoment B raw2268step0 raw2268step0Labels := by
      have ha : raw2268step0 = (fun i j => raw2268 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2268step0 raw2268; decide +kernel
      have hl : raw2268step0Labels = raw2268Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2268 raw2268Labels permutation152 permutation4
    mixedMoment B raw2268step0 raw2268step0Labels = mixedMoment B raw2268step1 raw2268step1Labels := by
      have ha : raw2268step1 = raw2268step0 := by apply Matrix.ext; unfold raw2268step1 raw2268step0; decide +kernel
      have hl : raw2268step0Labels = labelEmbedding7 ∘ raw2268step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2268step0 raw2268step0Labels raw2268step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical2269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2269 raw2269Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw2269 raw2269Labels = mixedMoment B raw2269step0 raw2269step0Labels := by
      have ha : raw2269step0 = (fun i j => raw2269 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2269step0 raw2269; decide +kernel
      have hl : raw2269step0Labels = raw2269Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2269 raw2269Labels permutation152 permutation4
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical2270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2270 raw2270Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw2270 raw2270Labels = mixedMoment B raw2270step0 raw2270step0Labels := by
      have ha : raw2270step0 = (fun i j => raw2270 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2270step0 raw2270; decide +kernel
      have hl : raw2270step0Labels = raw2270Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2270 raw2270Labels permutation158 permutation6
    mixedMoment B raw2270step0 raw2270step0Labels = mixedMoment B raw2270step1 raw2270step1Labels := by
      have ha : raw2270step1 = -raw2270step0 := by apply Matrix.ext; change ∀ i j, raw2270step1 i j = -(raw2270step0 i j); unfold raw2270step1 raw2270step0; decide +kernel
      have hl : raw2270step1Labels = raw2270step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2270step1 raw2270step1Labels = mixedMoment B raw2270step2 raw2270step2Labels := by
      have ha : raw2270step2 = raw2270step1 := by apply Matrix.ext; unfold raw2270step2 raw2270step1; decide +kernel
      have hl : raw2270step1Labels = labelEmbedding1 ∘ raw2270step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2270step1 raw2270step1Labels raw2270step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

theorem canonical2271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2271 raw2271Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw2271 raw2271Labels = mixedMoment B raw2271step0 raw2271step0Labels := by
      have ha : raw2271step0 = (fun i j => raw2271 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2271step0 raw2271; decide +kernel
      have hl : raw2271step0Labels = raw2271Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2271 raw2271Labels permutation32 permutation4
    mixedMoment B raw2271step0 raw2271step0Labels = mixedMoment B raw2271step1 raw2271step1Labels := by
      have ha : raw2271step1 = raw2271step0 := by apply Matrix.ext; unfold raw2271step1 raw2271step0; decide +kernel
      have hl : raw2271step0Labels = labelEmbedding7 ∘ raw2271step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2271step0 raw2271step0Labels raw2271step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical2272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2272 raw2272Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw2272 raw2272Labels = mixedMoment B raw2272step0 raw2272step0Labels := by
      have ha : raw2272step0 = (fun i j => raw2272 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2272step0 raw2272; decide +kernel
      have hl : raw2272step0Labels = raw2272Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2272 raw2272Labels permutation32 permutation4
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical2273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2273 raw2273Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw2273 raw2273Labels = mixedMoment B raw2273step0 raw2273step0Labels := by
      have ha : raw2273step0 = (fun i j => raw2273 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2273step0 raw2273; decide +kernel
      have hl : raw2273step0Labels = raw2273Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2273 raw2273Labels permutation34 permutation6
    mixedMoment B raw2273step0 raw2273step0Labels = mixedMoment B raw2273step1 raw2273step1Labels := by
      have ha : raw2273step1 = -raw2273step0 := by apply Matrix.ext; change ∀ i j, raw2273step1 i j = -(raw2273step0 i j); unfold raw2273step1 raw2273step0; decide +kernel
      have hl : raw2273step1Labels = raw2273step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2273step1 raw2273step1Labels = mixedMoment B raw2273step2 raw2273step2Labels := by
      have ha : raw2273step2 = raw2273step1 := by apply Matrix.ext; unfold raw2273step2 raw2273step1; decide +kernel
      have hl : raw2273step1Labels = labelEmbedding1 ∘ raw2273step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2273step1 raw2273step1Labels raw2273step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical2274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2274 raw2274Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw2274 raw2274Labels = mixedMoment B raw2274step0 raw2274step0Labels := by
      have ha : raw2274step0 = (fun i j => raw2274 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2274step0 raw2274; decide +kernel
      have hl : raw2274step0Labels = raw2274Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2274 raw2274Labels permutation32 permutation4
    mixedMoment B raw2274step0 raw2274step0Labels = mixedMoment B raw2274step1 raw2274step1Labels := by
      have ha : raw2274step1 = raw2274step0 := by apply Matrix.ext; unfold raw2274step1 raw2274step0; decide +kernel
      have hl : raw2274step0Labels = labelEmbedding7 ∘ raw2274step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2274step0 raw2274step0Labels raw2274step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical2275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2275 raw2275Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw2275 raw2275Labels = mixedMoment B raw2275step0 raw2275step0Labels := by
      have ha : raw2275step0 = (fun i j => raw2275 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2275step0 raw2275; decide +kernel
      have hl : raw2275step0Labels = raw2275Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2275 raw2275Labels permutation32 permutation4
    _ = mixedMoment B node2723 node2723Labels := by rfl

theorem canonical2276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2276 raw2276Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw2276 raw2276Labels = mixedMoment B raw2276step0 raw2276step0Labels := by
      have ha : raw2276step0 = (fun i j => raw2276 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2276step0 raw2276; decide +kernel
      have hl : raw2276step0Labels = raw2276Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2276 raw2276Labels permutation32 permutation6
    mixedMoment B raw2276step0 raw2276step0Labels = mixedMoment B raw2276step1 raw2276step1Labels := by
      have ha : raw2276step1 = -raw2276step0 := by apply Matrix.ext; change ∀ i j, raw2276step1 i j = -(raw2276step0 i j); unfold raw2276step1 raw2276step0; decide +kernel
      have hl : raw2276step1Labels = raw2276step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2276step1 raw2276step1Labels = mixedMoment B raw2276step2 raw2276step2Labels := by
      have ha : raw2276step2 = raw2276step1 := by apply Matrix.ext; unfold raw2276step2 raw2276step1; decide +kernel
      have hl : raw2276step1Labels = labelEmbedding1 ∘ raw2276step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2276step1 raw2276step1Labels raw2276step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

theorem canonical2280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2280 raw2280Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw2280 raw2280Labels = mixedMoment B raw2280step0 raw2280step0Labels := by
      have ha : raw2280step0 = (fun i j => raw2280 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2280step0 raw2280; decide +kernel
      have hl : raw2280step0Labels = raw2280Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2280 raw2280Labels permutation32 permutation4
    mixedMoment B raw2280step0 raw2280step0Labels = mixedMoment B raw2280step1 raw2280step1Labels := by
      have ha : raw2280step1 = raw2280step0 := by apply Matrix.ext; unfold raw2280step1 raw2280step0; decide +kernel
      have hl : raw2280step0Labels = labelEmbedding7 ∘ raw2280step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2280step0 raw2280step0Labels raw2280step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical2281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2281 raw2281Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw2281 raw2281Labels = mixedMoment B raw2281step0 raw2281step0Labels := by
      have ha : raw2281step0 = (fun i j => raw2281 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2281step0 raw2281; decide +kernel
      have hl : raw2281step0Labels = raw2281Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2281 raw2281Labels permutation32 permutation4
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical2282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2282 raw2282Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw2282 raw2282Labels = mixedMoment B raw2282step0 raw2282step0Labels := by
      have ha : raw2282step0 = (fun i j => raw2282 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2282step0 raw2282; decide +kernel
      have hl : raw2282step0Labels = raw2282Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2282 raw2282Labels permutation32 permutation6
    mixedMoment B raw2282step0 raw2282step0Labels = mixedMoment B raw2282step1 raw2282step1Labels := by
      have ha : raw2282step1 = -raw2282step0 := by apply Matrix.ext; change ∀ i j, raw2282step1 i j = -(raw2282step0 i j); unfold raw2282step1 raw2282step0; decide +kernel
      have hl : raw2282step1Labels = raw2282step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2282step1 raw2282step1Labels = mixedMoment B raw2282step2 raw2282step2Labels := by
      have ha : raw2282step2 = raw2282step1 := by apply Matrix.ext; unfold raw2282step2 raw2282step1; decide +kernel
      have hl : raw2282step1Labels = labelEmbedding1 ∘ raw2282step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2282step1 raw2282step1Labels raw2282step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

theorem canonical2283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2283 raw2283Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw2283 raw2283Labels = mixedMoment B raw2283step0 raw2283step0Labels := by
      have ha : raw2283step0 = (fun i j => raw2283 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2283step0 raw2283; decide +kernel
      have hl : raw2283step0Labels = raw2283Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2283 raw2283Labels permutation8 permutation4
    mixedMoment B raw2283step0 raw2283step0Labels = mixedMoment B raw2283step1 raw2283step1Labels := by
      have ha : raw2283step1 = raw2283step0 := by apply Matrix.ext; unfold raw2283step1 raw2283step0; decide +kernel
      have hl : raw2283step0Labels = labelEmbedding7 ∘ raw2283step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2283step0 raw2283step0Labels raw2283step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5272 node5272Labels := by rfl

theorem canonical2284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2284 raw2284Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw2284 raw2284Labels = mixedMoment B raw2284step0 raw2284step0Labels := by
      have ha : raw2284step0 = (fun i j => raw2284 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2284step0 raw2284; decide +kernel
      have hl : raw2284step0Labels = raw2284Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2284 raw2284Labels permutation8 permutation4
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical2285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2285 raw2285Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw2285 raw2285Labels = mixedMoment B raw2285step0 raw2285step0Labels := by
      have ha : raw2285step0 = (fun i j => raw2285 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2285step0 raw2285; decide +kernel
      have hl : raw2285step0Labels = raw2285Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2285 raw2285Labels permutation31 permutation6
    mixedMoment B raw2285step0 raw2285step0Labels = mixedMoment B raw2285step1 raw2285step1Labels := by
      have ha : raw2285step1 = raw2285step0 := by apply Matrix.ext; unfold raw2285step1 raw2285step0; decide +kernel
      have hl : raw2285step0Labels = labelEmbedding1 ∘ raw2285step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2285step0 raw2285step0Labels raw2285step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical2286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2286 raw2286Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw2286 raw2286Labels = mixedMoment B raw2286step0 raw2286step0Labels := by
      have ha : raw2286step0 = (fun i j => raw2286 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2286step0 raw2286; decide +kernel
      have hl : raw2286step0Labels = raw2286Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2286 raw2286Labels permutation8 permutation4
    mixedMoment B raw2286step0 raw2286step0Labels = mixedMoment B raw2286step1 raw2286step1Labels := by
      have ha : raw2286step1 = raw2286step0 := by apply Matrix.ext; unfold raw2286step1 raw2286step0; decide +kernel
      have hl : raw2286step0Labels = labelEmbedding7 ∘ raw2286step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2286step0 raw2286step0Labels raw2286step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

theorem canonical2287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2287 raw2287Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw2287 raw2287Labels = mixedMoment B raw2287step0 raw2287step0Labels := by
      have ha : raw2287step0 = (fun i j => raw2287 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2287step0 raw2287; decide +kernel
      have hl : raw2287step0Labels = raw2287Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2287 raw2287Labels permutation8 permutation4
    _ = mixedMoment B node2743 node2743Labels := by rfl

theorem canonical2288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2288 raw2288Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw2288 raw2288Labels = mixedMoment B raw2288step0 raw2288step0Labels := by
      have ha : raw2288step0 = (fun i j => raw2288 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2288step0 raw2288; decide +kernel
      have hl : raw2288step0Labels = raw2288Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2288 raw2288Labels permutation9 permutation6
    mixedMoment B raw2288step0 raw2288step0Labels = mixedMoment B raw2288step1 raw2288step1Labels := by
      have ha : raw2288step1 = -raw2288step0 := by apply Matrix.ext; change ∀ i j, raw2288step1 i j = -(raw2288step0 i j); unfold raw2288step1 raw2288step0; decide +kernel
      have hl : raw2288step1Labels = raw2288step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2288step1 raw2288step1Labels = mixedMoment B raw2288step2 raw2288step2Labels := by
      have ha : raw2288step2 = raw2288step1 := by apply Matrix.ext; unfold raw2288step2 raw2288step1; decide +kernel
      have hl : raw2288step1Labels = labelEmbedding1 ∘ raw2288step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2288step1 raw2288step1Labels raw2288step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3548 node3548Labels := by rfl

theorem canonical2289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2289 raw2289Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw2289 raw2289Labels = mixedMoment B raw2289step0 raw2289step0Labels := by
      have ha : raw2289step0 = (fun i j => raw2289 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2289step0 raw2289; decide +kernel
      have hl : raw2289step0Labels = raw2289Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2289 raw2289Labels permutation32 permutation5
    mixedMoment B raw2289step0 raw2289step0Labels = mixedMoment B raw2289step1 raw2289step1Labels := by
      have ha : raw2289step1 = raw2289step0 := by apply Matrix.ext; unfold raw2289step1 raw2289step0; decide +kernel
      have hl : raw2289step0Labels = labelEmbedding8 ∘ raw2289step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2289step0 raw2289step0Labels raw2289step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical2290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2290 raw2290Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw2290 raw2290Labels = mixedMoment B raw2290step0 raw2290step0Labels := by
      have ha : raw2290step0 = (fun i j => raw2290 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2290step0 raw2290; decide +kernel
      have hl : raw2290step0Labels = raw2290Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2290 raw2290Labels permutation32 permutation4
    _ = mixedMoment B node3077 node3077Labels := by rfl

theorem canonical2291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2291 raw2291Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw2291 raw2291Labels = mixedMoment B raw2291step0 raw2291step0Labels := by
      have ha : raw2291step0 = (fun i j => raw2291 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2291step0 raw2291; decide +kernel
      have hl : raw2291step0Labels = raw2291Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2291 raw2291Labels permutation48 permutation3
    mixedMoment B raw2291step0 raw2291step0Labels = mixedMoment B raw2291step1 raw2291step1Labels := by
      have ha : raw2291step1 = -raw2291step0 := by apply Matrix.ext; change ∀ i j, raw2291step1 i j = -(raw2291step0 i j); unfold raw2291step1 raw2291step0; decide +kernel
      have hl : raw2291step1Labels = raw2291step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2291step1 raw2291step1Labels = mixedMoment B raw2291step2 raw2291step2Labels := by
      have ha : raw2291step2 = raw2291step1 := by apply Matrix.ext; unfold raw2291step2 raw2291step1; decide +kernel
      have hl : raw2291step1Labels = labelEmbedding1 ∘ raw2291step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2291step1 raw2291step1Labels raw2291step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

theorem canonical2292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2292 raw2292Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw2292 raw2292Labels = mixedMoment B raw2292step0 raw2292step0Labels := by
      have ha : raw2292step0 = (fun i j => raw2292 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2292step0 raw2292; decide +kernel
      have hl : raw2292step0Labels = raw2292Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2292 raw2292Labels permutation32 permutation4
    mixedMoment B raw2292step0 raw2292step0Labels = mixedMoment B raw2292step1 raw2292step1Labels := by
      have ha : raw2292step1 = raw2292step0 := by apply Matrix.ext; unfold raw2292step1 raw2292step0; decide +kernel
      have hl : raw2292step0Labels = labelEmbedding7 ∘ raw2292step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2292step0 raw2292step0Labels raw2292step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical2293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2293 raw2293Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw2293 raw2293Labels = mixedMoment B raw2293step0 raw2293step0Labels := by
      have ha : raw2293step0 = (fun i j => raw2293 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2293step0 raw2293; decide +kernel
      have hl : raw2293step0Labels = raw2293Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2293 raw2293Labels permutation32 permutation4
    _ = mixedMoment B node2764 node2764Labels := by rfl

theorem canonical2294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2294 raw2294Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw2294 raw2294Labels = mixedMoment B raw2294step0 raw2294step0Labels := by
      have ha : raw2294step0 = (fun i j => raw2294 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2294step0 raw2294; decide +kernel
      have hl : raw2294step0Labels = raw2294Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2294 raw2294Labels permutation38 permutation6
    mixedMoment B raw2294step0 raw2294step0Labels = mixedMoment B raw2294step1 raw2294step1Labels := by
      have ha : raw2294step1 = -raw2294step0 := by apply Matrix.ext; change ∀ i j, raw2294step1 i j = -(raw2294step0 i j); unfold raw2294step1 raw2294step0; decide +kernel
      have hl : raw2294step1Labels = raw2294step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2294step1 raw2294step1Labels = mixedMoment B raw2294step2 raw2294step2Labels := by
      have ha : raw2294step2 = raw2294step1 := by apply Matrix.ext; unfold raw2294step2 raw2294step1; decide +kernel
      have hl : raw2294step1Labels = labelEmbedding1 ∘ raw2294step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2294step1 raw2294step1Labels raw2294step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

theorem canonical2295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2295 raw2295Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw2295 raw2295Labels = mixedMoment B raw2295step0 raw2295step0Labels := by
      have ha : raw2295step0 = (fun i j => raw2295 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2295step0 raw2295; decide +kernel
      have hl : raw2295step0Labels = raw2295Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2295 raw2295Labels permutation8 permutation4
    mixedMoment B raw2295step0 raw2295step0Labels = mixedMoment B raw2295step1 raw2295step1Labels := by
      have ha : raw2295step1 = raw2295step0 := by apply Matrix.ext; unfold raw2295step1 raw2295step0; decide +kernel
      have hl : raw2295step0Labels = labelEmbedding7 ∘ raw2295step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2295step0 raw2295step0Labels raw2295step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

theorem canonical2296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2296 raw2296Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw2296 raw2296Labels = mixedMoment B raw2296step0 raw2296step0Labels := by
      have ha : raw2296step0 = (fun i j => raw2296 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2296step0 raw2296; decide +kernel
      have hl : raw2296step0Labels = raw2296Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2296 raw2296Labels permutation8 permutation4
    _ = mixedMoment B node2765 node2765Labels := by rfl

theorem canonical2297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2297 raw2297Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw2297 raw2297Labels = mixedMoment B raw2297step0 raw2297step0Labels := by
      have ha : raw2297step0 = (fun i j => raw2297 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2297step0 raw2297; decide +kernel
      have hl : raw2297step0Labels = raw2297Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2297 raw2297Labels permutation10 permutation6
    mixedMoment B raw2297step0 raw2297step0Labels = mixedMoment B raw2297step1 raw2297step1Labels := by
      have ha : raw2297step1 = -raw2297step0 := by apply Matrix.ext; change ∀ i j, raw2297step1 i j = -(raw2297step0 i j); unfold raw2297step1 raw2297step0; decide +kernel
      have hl : raw2297step1Labels = raw2297step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2297step1 raw2297step1Labels = mixedMoment B raw2297step2 raw2297step2Labels := by
      have ha : raw2297step2 = raw2297step1 := by apply Matrix.ext; unfold raw2297step2 raw2297step1; decide +kernel
      have hl : raw2297step1Labels = labelEmbedding1 ∘ raw2297step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2297step1 raw2297step1Labels raw2297step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3582 node3582Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2310 raw2310Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw2310 raw2310Labels = mixedMoment B raw2310step0 raw2310step0Labels := by
      have ha : raw2310step0 = (fun i j => raw2310 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2310step0 raw2310; decide +kernel
      have hl : raw2310step0Labels = raw2310Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2310 raw2310Labels permutation32 permutation5
    mixedMoment B raw2310step0 raw2310step0Labels = mixedMoment B raw2310step1 raw2310step1Labels := by
      have ha : raw2310step1 = raw2310step0 := by apply Matrix.ext; unfold raw2310step1 raw2310step0; decide +kernel
      have hl : raw2310step0Labels = labelEmbedding8 ∘ raw2310step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2310step0 raw2310step0Labels raw2310step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

theorem canonical2311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2311 raw2311Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw2311 raw2311Labels = mixedMoment B raw2311step0 raw2311step0Labels := by
      have ha : raw2311step0 = (fun i j => raw2311 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2311step0 raw2311; decide +kernel
      have hl : raw2311step0Labels = raw2311Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2311 raw2311Labels permutation32 permutation4
    _ = mixedMoment B node3053 node3053Labels := by rfl

theorem canonical2312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2312 raw2312Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw2312 raw2312Labels = mixedMoment B raw2312step0 raw2312step0Labels := by
      have ha : raw2312step0 = (fun i j => raw2312 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2312step0 raw2312; decide +kernel
      have hl : raw2312step0Labels = raw2312Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2312 raw2312Labels permutation41 permutation3
    mixedMoment B raw2312step0 raw2312step0Labels = mixedMoment B raw2312step1 raw2312step1Labels := by
      have ha : raw2312step1 = -raw2312step0 := by apply Matrix.ext; change ∀ i j, raw2312step1 i j = -(raw2312step0 i j); unfold raw2312step1 raw2312step0; decide +kernel
      have hl : raw2312step1Labels = raw2312step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2312step1 raw2312step1Labels = mixedMoment B raw2312step2 raw2312step2Labels := by
      have ha : raw2312step2 = raw2312step1 := by apply Matrix.ext; unfold raw2312step2 raw2312step1; decide +kernel
      have hl : raw2312step1Labels = labelEmbedding1 ∘ raw2312step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2312step1 raw2312step1Labels raw2312step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3619 node3619Labels := by rfl

theorem canonical2313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2313 raw2313Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw2313 raw2313Labels = mixedMoment B raw2313step0 raw2313step0Labels := by
      have ha : raw2313step0 = (fun i j => raw2313 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2313step0 raw2313; decide +kernel
      have hl : raw2313step0Labels = raw2313Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2313 raw2313Labels permutation8 permutation5
    mixedMoment B raw2313step0 raw2313step0Labels = mixedMoment B raw2313step1 raw2313step1Labels := by
      have ha : raw2313step1 = raw2313step0 := by apply Matrix.ext; unfold raw2313step1 raw2313step0; decide +kernel
      have hl : raw2313step0Labels = labelEmbedding8 ∘ raw2313step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2313step0 raw2313step0Labels raw2313step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

theorem canonical2314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2314 raw2314Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw2314 raw2314Labels = mixedMoment B raw2314step0 raw2314step0Labels := by
      have ha : raw2314step0 = (fun i j => raw2314 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2314step0 raw2314; decide +kernel
      have hl : raw2314step0Labels = raw2314Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2314 raw2314Labels permutation8 permutation4
    _ = mixedMoment B node3054 node3054Labels := by rfl

theorem canonical2315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2315 raw2315Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw2315 raw2315Labels = mixedMoment B raw2315step0 raw2315step0Labels := by
      have ha : raw2315step0 = (fun i j => raw2315 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2315step0 raw2315; decide +kernel
      have hl : raw2315step0Labels = raw2315Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2315 raw2315Labels permutation11 permutation3
    mixedMoment B raw2315step0 raw2315step0Labels = mixedMoment B raw2315step1 raw2315step1Labels := by
      have ha : raw2315step1 = -raw2315step0 := by apply Matrix.ext; change ∀ i j, raw2315step1 i j = -(raw2315step0 i j); unfold raw2315step1 raw2315step0; decide +kernel
      have hl : raw2315step1Labels = raw2315step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2315step1 raw2315step1Labels = mixedMoment B raw2315step2 raw2315step2Labels := by
      have ha : raw2315step2 = raw2315step1 := by apply Matrix.ext; unfold raw2315step2 raw2315step1; decide +kernel
      have hl : raw2315step1Labels = labelEmbedding1 ∘ raw2315step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2315step1 raw2315step1Labels raw2315step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3626 node3626Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5257 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5257 node5257Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2721 node2721Labels + mixedMoment B node3532 node3532Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2268 singletonSmall5257
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5257) = raw2268Labels := by decide +kernel
  rw [hl, canonical2268 B hB] at h
  have hc0 : mixedMoment B raw2268 (Fin.cases (0 : Fin 2) singletonSmall5257) =
      mixedMoment B node2721 node2721Labels := by
    have ha : raw2268 = raw2269 := by apply Matrix.ext; unfold raw2268 raw2269; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5257 = raw2269Labels := by decide +kernel
    rw [ha, hj, canonical2269 B hB]
  have hc1 : mixedMoment B raw2268 (Fin.cases (1 : Fin 2) singletonSmall5257) =
      mixedMoment B node3532 node3532Labels := by
    have ha : raw2268 = raw2270 := by apply Matrix.ext; unfold raw2268 raw2270; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5257 = raw2270Labels := by decide +kernel
    rw [ha, hj, canonical2270 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5258 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5258 node5258Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2722 node2722Labels + mixedMoment B node3533 node3533Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2271 singletonSmall5258
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5258) = raw2271Labels := by decide +kernel
  rw [hl, canonical2271 B hB] at h
  have hc0 : mixedMoment B raw2271 (Fin.cases (0 : Fin 2) singletonSmall5258) =
      mixedMoment B node2722 node2722Labels := by
    have ha : raw2271 = raw2272 := by apply Matrix.ext; unfold raw2271 raw2272; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5258 = raw2272Labels := by decide +kernel
    rw [ha, hj, canonical2272 B hB]
  have hc1 : mixedMoment B raw2271 (Fin.cases (1 : Fin 2) singletonSmall5258) =
      mixedMoment B node3533 node3533Labels := by
    have ha : raw2271 = raw2273 := by apply Matrix.ext; unfold raw2271 raw2273; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5258 = raw2273Labels := by decide +kernel
    rw [ha, hj, canonical2273 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5259 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5259 node5259Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2723 node2723Labels + mixedMoment B node3544 node3544Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2274 singletonSmall5259
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5259) = raw2274Labels := by decide +kernel
  rw [hl, canonical2274 B hB] at h
  have hc0 : mixedMoment B raw2274 (Fin.cases (0 : Fin 2) singletonSmall5259) =
      mixedMoment B node2723 node2723Labels := by
    have ha : raw2274 = raw2275 := by apply Matrix.ext; unfold raw2274 raw2275; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5259 = raw2275Labels := by decide +kernel
    rw [ha, hj, canonical2275 B hB]
  have hc1 : mixedMoment B raw2274 (Fin.cases (1 : Fin 2) singletonSmall5259) =
      mixedMoment B node3544 node3544Labels := by
    have ha : raw2274 = raw2276 := by apply Matrix.ext; unfold raw2274 raw2276; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5259 = raw2276Labels := by decide +kernel
    rw [ha, hj, canonical2276 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5271 node5271Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2739 node2739Labels + mixedMoment B node3534 node3534Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2280 singletonSmall5271
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5271) = raw2280Labels := by decide +kernel
  rw [hl, canonical2280 B hB] at h
  have hc0 : mixedMoment B raw2280 (Fin.cases (0 : Fin 2) singletonSmall5271) =
      mixedMoment B node2739 node2739Labels := by
    have ha : raw2280 = raw2281 := by apply Matrix.ext; unfold raw2280 raw2281; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5271 = raw2281Labels := by decide +kernel
    rw [ha, hj, canonical2281 B hB]
  have hc1 : mixedMoment B raw2280 (Fin.cases (1 : Fin 2) singletonSmall5271) =
      mixedMoment B node3534 node3534Labels := by
    have ha : raw2280 = raw2282 := by apply Matrix.ext; unfold raw2280 raw2282; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5271 = raw2282Labels := by decide +kernel
    rw [ha, hj, canonical2282 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5272 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5272 node5272Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2740 node2740Labels + mixedMoment B node2740 node2740Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2283 singletonSmall5272
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5272) = raw2283Labels := by decide +kernel
  rw [hl, canonical2283 B hB] at h
  have hc0 : mixedMoment B raw2283 (Fin.cases (0 : Fin 2) singletonSmall5272) =
      mixedMoment B node2740 node2740Labels := by
    have ha : raw2283 = raw2284 := by apply Matrix.ext; unfold raw2283 raw2284; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5272 = raw2284Labels := by decide +kernel
    rw [ha, hj, canonical2284 B hB]
  have hc1 : mixedMoment B raw2283 (Fin.cases (1 : Fin 2) singletonSmall5272) =
      mixedMoment B node2740 node2740Labels := by
    have ha : raw2283 = raw2285 := by apply Matrix.ext; unfold raw2283 raw2285; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5272 = raw2285Labels := by decide +kernel
    rw [ha, hj, canonical2285 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5275 node5275Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2743 node2743Labels + mixedMoment B node3548 node3548Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2286 singletonSmall5275
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5275) = raw2286Labels := by decide +kernel
  rw [hl, canonical2286 B hB] at h
  have hc0 : mixedMoment B raw2286 (Fin.cases (0 : Fin 2) singletonSmall5275) =
      mixedMoment B node2743 node2743Labels := by
    have ha : raw2286 = raw2287 := by apply Matrix.ext; unfold raw2286 raw2287; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5275 = raw2287Labels := by decide +kernel
    rw [ha, hj, canonical2287 B hB]
  have hc1 : mixedMoment B raw2286 (Fin.cases (1 : Fin 2) singletonSmall5275) =
      mixedMoment B node3548 node3548Labels := by
    have ha : raw2286 = raw2288 := by apply Matrix.ext; unfold raw2286 raw2288; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5275 = raw2288Labels := by decide +kernel
    rw [ha, hj, canonical2288 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5284 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5284 node5284Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3077 node3077Labels + mixedMoment B node3625 node3625Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2289 singletonSmall5284
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5284) = raw2289Labels := by decide +kernel
  rw [hl, canonical2289 B hB] at h
  have hc0 : mixedMoment B raw2289 (Fin.cases (0 : Fin 2) singletonSmall5284) =
      mixedMoment B node3077 node3077Labels := by
    have ha : raw2289 = raw2290 := by apply Matrix.ext; unfold raw2289 raw2290; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5284 = raw2290Labels := by decide +kernel
    rw [ha, hj, canonical2290 B hB]
  have hc1 : mixedMoment B raw2289 (Fin.cases (1 : Fin 2) singletonSmall5284) =
      mixedMoment B node3625 node3625Labels := by
    have ha : raw2289 = raw2291 := by apply Matrix.ext; unfold raw2289 raw2291; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5284 = raw2291Labels := by decide +kernel
    rw [ha, hj, canonical2291 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5290 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5290 node5290Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2764 node2764Labels + mixedMoment B node3581 node3581Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2292 singletonSmall5290
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5290) = raw2292Labels := by decide +kernel
  rw [hl, canonical2292 B hB] at h
  have hc0 : mixedMoment B raw2292 (Fin.cases (0 : Fin 2) singletonSmall5290) =
      mixedMoment B node2764 node2764Labels := by
    have ha : raw2292 = raw2293 := by apply Matrix.ext; unfold raw2292 raw2293; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5290 = raw2293Labels := by decide +kernel
    rw [ha, hj, canonical2293 B hB]
  have hc1 : mixedMoment B raw2292 (Fin.cases (1 : Fin 2) singletonSmall5290) =
      mixedMoment B node3581 node3581Labels := by
    have ha : raw2292 = raw2294 := by apply Matrix.ext; unfold raw2292 raw2294; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5290 = raw2294Labels := by decide +kernel
    rw [ha, hj, canonical2294 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5291 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5291 node5291Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2765 node2765Labels + mixedMoment B node3582 node3582Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2295 singletonSmall5291
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5291) = raw2295Labels := by decide +kernel
  rw [hl, canonical2295 B hB] at h
  have hc0 : mixedMoment B raw2295 (Fin.cases (0 : Fin 2) singletonSmall5291) =
      mixedMoment B node2765 node2765Labels := by
    have ha : raw2295 = raw2296 := by apply Matrix.ext; unfold raw2295 raw2296; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5291 = raw2296Labels := by decide +kernel
    rw [ha, hj, canonical2296 B hB]
  have hc1 : mixedMoment B raw2295 (Fin.cases (1 : Fin 2) singletonSmall5291) =
      mixedMoment B node3582 node3582Labels := by
    have ha : raw2295 = raw2297 := by apply Matrix.ext; unfold raw2295 raw2297; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5291 = raw2297Labels := by decide +kernel
    rw [ha, hj, canonical2297 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5301 node5301Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3053 node3053Labels + mixedMoment B node3619 node3619Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2310 singletonSmall5301
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5301) = raw2310Labels := by decide +kernel
  rw [hl, canonical2310 B hB] at h
  have hc0 : mixedMoment B raw2310 (Fin.cases (0 : Fin 2) singletonSmall5301) =
      mixedMoment B node3053 node3053Labels := by
    have ha : raw2310 = raw2311 := by apply Matrix.ext; unfold raw2310 raw2311; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5301 = raw2311Labels := by decide +kernel
    rw [ha, hj, canonical2311 B hB]
  have hc1 : mixedMoment B raw2310 (Fin.cases (1 : Fin 2) singletonSmall5301) =
      mixedMoment B node3619 node3619Labels := by
    have ha : raw2310 = raw2312 := by apply Matrix.ext; unfold raw2310 raw2312; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5301 = raw2312Labels := by decide +kernel
    rw [ha, hj, canonical2312 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5302 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5302 node5302Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3054 node3054Labels + mixedMoment B node3626 node3626Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2313 singletonSmall5302
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5302) = raw2313Labels := by decide +kernel
  rw [hl, canonical2313 B hB] at h
  have hc0 : mixedMoment B raw2313 (Fin.cases (0 : Fin 2) singletonSmall5302) =
      mixedMoment B node3054 node3054Labels := by
    have ha : raw2313 = raw2314 := by apply Matrix.ext; unfold raw2313 raw2314; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5302 = raw2314Labels := by decide +kernel
    rw [ha, hj, canonical2314 B hB]
  have hc1 : mixedMoment B raw2313 (Fin.cases (1 : Fin 2) singletonSmall5302) =
      mixedMoment B node3626 node3626Labels := by
    have ha : raw2313 = raw2315 := by apply Matrix.ext; unfold raw2313 raw2315; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5302 = raw2315Labels := by decide +kernel
    rw [ha, hj, canonical2315 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SoundPriority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3054 node3054Labels = Sparse.eval nodeValue3054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3054) = mixedMoment B node3054 node3054Labels := rfl
  simpa [nodeValue3054, Sparse.eval] using hc.symm

theorem sound3626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3626 node3626Labels = Sparse.eval nodeValue3626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3626) = mixedMoment B node3626 node3626Labels := rfl
  simpa [nodeValue3626, Sparse.eval] using hc.symm

theorem sound5302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5302 node5302Labels = Sparse.eval nodeValue5302 (mixedVector B) := by
  have h := singleton5302 B _hB
  rw [sound3054 B _hB _hF, sound3626 B _hB _hF] at h
  norm_num [nodeValue5302, nodeValue3054, nodeValue3626, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2721 node2721Labels = Sparse.eval nodeValue2721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2721) = mixedMoment B node2721 node2721Labels := rfl
  simpa [nodeValue2721, Sparse.eval] using hc.symm

theorem sound2722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2722 node2722Labels = Sparse.eval nodeValue2722 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2722) = mixedMoment B node2722 node2722Labels := rfl
  simpa [nodeValue2722, Sparse.eval] using hc.symm

theorem sound2723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2723 node2723Labels = Sparse.eval nodeValue2723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2723) = mixedMoment B node2723 node2723Labels := rfl
  simpa [nodeValue2723, Sparse.eval] using hc.symm

theorem sound2739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2739 node2739Labels = Sparse.eval nodeValue2739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2739) = mixedMoment B node2739 node2739Labels := rfl
  simpa [nodeValue2739, Sparse.eval] using hc.symm

theorem sound2740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2740 node2740Labels = Sparse.eval nodeValue2740 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2740) = mixedMoment B node2740 node2740Labels := rfl
  simpa [nodeValue2740, Sparse.eval] using hc.symm

theorem sound2743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2743 node2743Labels = Sparse.eval nodeValue2743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2743) = mixedMoment B node2743 node2743Labels := rfl
  simpa [nodeValue2743, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2764 node2764Labels = Sparse.eval nodeValue2764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2764) = mixedMoment B node2764 node2764Labels := rfl
  simpa [nodeValue2764, Sparse.eval] using hc.symm

theorem sound2765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2765 node2765Labels = Sparse.eval nodeValue2765 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2765) = mixedMoment B node2765 node2765Labels := rfl
  simpa [nodeValue2765, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3053 node3053Labels = Sparse.eval nodeValue3053 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3053) = mixedMoment B node3053 node3053Labels := rfl
  simpa [nodeValue3053, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3077 node3077Labels = Sparse.eval nodeValue3077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3077) = mixedMoment B node3077 node3077Labels := rfl
  simpa [nodeValue3077, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3532 node3532Labels = Sparse.eval nodeValue3532 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3532) = mixedMoment B node3532 node3532Labels := rfl
  simpa [nodeValue3532, Sparse.eval] using hc.symm

theorem sound3533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3533 node3533Labels = Sparse.eval nodeValue3533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3533) = mixedMoment B node3533 node3533Labels := rfl
  simpa [nodeValue3533, Sparse.eval] using hc.symm

theorem sound3534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3534 node3534Labels = Sparse.eval nodeValue3534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3534) = mixedMoment B node3534 node3534Labels := rfl
  simpa [nodeValue3534, Sparse.eval] using hc.symm

theorem sound3544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3544 node3544Labels = Sparse.eval nodeValue3544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3544) = mixedMoment B node3544 node3544Labels := rfl
  simpa [nodeValue3544, Sparse.eval] using hc.symm

theorem sound3548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3548 node3548Labels = Sparse.eval nodeValue3548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3548) = mixedMoment B node3548 node3548Labels := rfl
  simpa [nodeValue3548, Sparse.eval] using hc.symm

theorem sound3581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3581 node3581Labels = Sparse.eval nodeValue3581 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3581) = mixedMoment B node3581 node3581Labels := rfl
  simpa [nodeValue3581, Sparse.eval] using hc.symm

theorem sound3582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3582 node3582Labels = Sparse.eval nodeValue3582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3582) = mixedMoment B node3582 node3582Labels := rfl
  simpa [nodeValue3582, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3619 node3619Labels = Sparse.eval nodeValue3619 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3619) = mixedMoment B node3619 node3619Labels := rfl
  simpa [nodeValue3619, Sparse.eval] using hc.symm

theorem sound3625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3625 node3625Labels = Sparse.eval nodeValue3625 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3625) = mixedMoment B node3625 node3625Labels := rfl
  simpa [nodeValue3625, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5206 node5206Labels = Sparse.eval nodeValue5206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5206) = mixedMoment B node5206 node5206Labels := rfl
  simpa [nodeValue5206, Sparse.eval] using hc.symm

theorem sound5215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5215 node5215Labels = Sparse.eval nodeValue5215 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5215) = mixedMoment B node5215 node5215Labels := rfl
  simpa [nodeValue5215, Sparse.eval] using hc.symm

theorem sound5216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5216 node5216Labels = Sparse.eval nodeValue5216 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5216) = mixedMoment B node5216 node5216Labels := rfl
  simpa [nodeValue5216, Sparse.eval] using hc.symm

theorem sound5217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5217 node5217Labels = Sparse.eval nodeValue5217 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5217) = mixedMoment B node5217 node5217Labels := rfl
  simpa [nodeValue5217, Sparse.eval] using hc.symm

theorem sound5219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5219 node5219Labels = Sparse.eval nodeValue5219 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5219) = mixedMoment B node5219 node5219Labels := rfl
  simpa [nodeValue5219, Sparse.eval] using hc.symm

theorem sound5220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5220 node5220Labels = Sparse.eval nodeValue5220 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5220) = mixedMoment B node5220 node5220Labels := rfl
  simpa [nodeValue5220, Sparse.eval] using hc.symm

theorem sound5222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5222 node5222Labels = Sparse.eval nodeValue5222 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5222) = mixedMoment B node5222 node5222Labels := rfl
  simpa [nodeValue5222, Sparse.eval] using hc.symm

theorem sound5226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5226 node5226Labels = Sparse.eval nodeValue5226 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5226) = mixedMoment B node5226 node5226Labels := rfl
  simpa [nodeValue5226, Sparse.eval] using hc.symm

theorem sound5229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5229 node5229Labels = Sparse.eval nodeValue5229 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5229) = mixedMoment B node5229 node5229Labels := rfl
  simpa [nodeValue5229, Sparse.eval] using hc.symm

theorem sound5231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5231 node5231Labels = Sparse.eval nodeValue5231 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5231) = mixedMoment B node5231 node5231Labels := rfl
  simpa [nodeValue5231, Sparse.eval] using hc.symm

theorem sound5232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5232 node5232Labels = Sparse.eval nodeValue5232 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5232) = mixedMoment B node5232 node5232Labels := rfl
  simpa [nodeValue5232, Sparse.eval] using hc.symm

theorem sound5233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5233 node5233Labels = Sparse.eval nodeValue5233 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5233) = mixedMoment B node5233 node5233Labels := rfl
  simpa [nodeValue5233, Sparse.eval] using hc.symm

theorem sound5235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5235 node5235Labels = Sparse.eval nodeValue5235 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5235) = mixedMoment B node5235 node5235Labels := rfl
  simpa [nodeValue5235, Sparse.eval] using hc.symm

theorem sound5236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5236 node5236Labels = Sparse.eval nodeValue5236 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5236) = mixedMoment B node5236 node5236Labels := rfl
  simpa [nodeValue5236, Sparse.eval] using hc.symm

theorem sound5243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5243 node5243Labels = Sparse.eval nodeValue5243 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5243) = mixedMoment B node5243 node5243Labels := rfl
  simpa [nodeValue5243, Sparse.eval] using hc.symm

theorem sound5244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5244 node5244Labels = Sparse.eval nodeValue5244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5244) = mixedMoment B node5244 node5244Labels := rfl
  simpa [nodeValue5244, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5250 node5250Labels = 0 := by
  exact mixedMoment_alpha B hF node5250 node5250Labels 1 permutation200
    (by decide +kernel)

theorem zero5256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5256 node5256Labels = 0 := by
  exact mixedMoment_alpha B hF node5256 node5256Labels 1 permutation203
    (by decide +kernel)

theorem zero5273 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5273 node5273Labels = 0 := by
  exact mixedMoment_order_one B hB node5273 node5273Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5274 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5274 node5274Labels = 0 := by
  exact mixedMoment_order_one B hB node5274 node5274Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5249 node5249Labels = Sparse.eval nodeValue5249 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5249) = mixedMoment B node5249 node5249Labels := rfl
  simpa [nodeValue5249, Sparse.eval] using hc.symm

theorem sound5250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5250 node5250Labels = Sparse.eval nodeValue5250 (mixedVector B) := by
  simpa only [nodeValue5250, Sparse.eval_nil] using zero5250 B _hB _hF

theorem sound5251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5251 node5251Labels = Sparse.eval nodeValue5251 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5251) = mixedMoment B node5251 node5251Labels := rfl
  simpa [nodeValue5251, Sparse.eval] using hc.symm

theorem sound5252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5252 node5252Labels = Sparse.eval nodeValue5252 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5252) = mixedMoment B node5252 node5252Labels := rfl
  simpa [nodeValue5252, Sparse.eval] using hc.symm

theorem sound5254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5254 node5254Labels = Sparse.eval nodeValue5254 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5254) = mixedMoment B node5254 node5254Labels := rfl
  simpa [nodeValue5254, Sparse.eval] using hc.symm

theorem sound5255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5255 node5255Labels = Sparse.eval nodeValue5255 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5255) = mixedMoment B node5255 node5255Labels := rfl
  simpa [nodeValue5255, Sparse.eval] using hc.symm

theorem sound5256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5256 node5256Labels = Sparse.eval nodeValue5256 (mixedVector B) := by
  simpa only [nodeValue5256, Sparse.eval_nil] using zero5256 B _hB _hF

theorem sound5257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5257 node5257Labels = Sparse.eval nodeValue5257 (mixedVector B) := by
  have h := singleton5257 B _hB
  rw [sound2721 B _hB _hF, sound3532 B _hB _hF] at h
  norm_num [nodeValue5257, nodeValue2721, nodeValue3532, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5258 node5258Labels = Sparse.eval nodeValue5258 (mixedVector B) := by
  have h := singleton5258 B _hB
  rw [sound2722 B _hB _hF, sound3533 B _hB _hF] at h
  norm_num [nodeValue5258, nodeValue2722, nodeValue3533, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5259 node5259Labels = Sparse.eval nodeValue5259 (mixedVector B) := by
  have h := singleton5259 B _hB
  rw [sound2723 B _hB _hF, sound3544 B _hB _hF] at h
  norm_num [nodeValue5259, nodeValue2723, nodeValue3544, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5260 node5260Labels = Sparse.eval nodeValue5260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5260) = mixedMoment B node5260 node5260Labels := rfl
  simpa [nodeValue5260, Sparse.eval] using hc.symm

theorem sound5263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5263 node5263Labels = Sparse.eval nodeValue5263 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5263) = mixedMoment B node5263 node5263Labels := rfl
  simpa [nodeValue5263, Sparse.eval] using hc.symm

theorem sound5264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5264 node5264Labels = Sparse.eval nodeValue5264 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5264) = mixedMoment B node5264 node5264Labels := rfl
  simpa [nodeValue5264, Sparse.eval] using hc.symm

theorem sound5265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5265 node5265Labels = Sparse.eval nodeValue5265 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5265) = mixedMoment B node5265 node5265Labels := rfl
  simpa [nodeValue5265, Sparse.eval] using hc.symm

theorem sound5266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5266 node5266Labels = Sparse.eval nodeValue5266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5266) = mixedMoment B node5266 node5266Labels := rfl
  simpa [nodeValue5266, Sparse.eval] using hc.symm

theorem sound5267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5267 node5267Labels = Sparse.eval nodeValue5267 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5267) = mixedMoment B node5267 node5267Labels := rfl
  simpa [nodeValue5267, Sparse.eval] using hc.symm

theorem sound5268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5268 node5268Labels = Sparse.eval nodeValue5268 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5268) = mixedMoment B node5268 node5268Labels := rfl
  simpa [nodeValue5268, Sparse.eval] using hc.symm

theorem sound5269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5269 node5269Labels = Sparse.eval nodeValue5269 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5269) = mixedMoment B node5269 node5269Labels := rfl
  simpa [nodeValue5269, Sparse.eval] using hc.symm

theorem sound5270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5270 node5270Labels = Sparse.eval nodeValue5270 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5270) = mixedMoment B node5270 node5270Labels := rfl
  simpa [nodeValue5270, Sparse.eval] using hc.symm

theorem sound5271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5271 node5271Labels = Sparse.eval nodeValue5271 (mixedVector B) := by
  have h := singleton5271 B _hB
  rw [sound2739 B _hB _hF, sound3534 B _hB _hF] at h
  norm_num [nodeValue5271, nodeValue2739, nodeValue3534, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5272 node5272Labels = Sparse.eval nodeValue5272 (mixedVector B) := by
  have h := singleton5272 B _hB
  rw [sound2740 B _hB _hF] at h
  norm_num [nodeValue5272, nodeValue2740, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5273 node5273Labels = Sparse.eval nodeValue5273 (mixedVector B) := by
  simpa only [nodeValue5273, Sparse.eval_nil] using zero5273 B _hB _hF

theorem sound5274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5274 node5274Labels = Sparse.eval nodeValue5274 (mixedVector B) := by
  simpa only [nodeValue5274, Sparse.eval_nil] using zero5274 B _hB _hF

theorem sound5275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5275 node5275Labels = Sparse.eval nodeValue5275 (mixedVector B) := by
  have h := singleton5275 B _hB
  rw [sound2743 B _hB _hF, sound3548 B _hB _hF] at h
  norm_num [nodeValue5275, nodeValue2743, nodeValue3548, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5276 node5276Labels = Sparse.eval nodeValue5276 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5276) = mixedMoment B node5276 node5276Labels := rfl
  simpa [nodeValue5276, Sparse.eval] using hc.symm

theorem sound5277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5277 node5277Labels = Sparse.eval nodeValue5277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5277) = mixedMoment B node5277 node5277Labels := rfl
  simpa [nodeValue5277, Sparse.eval] using hc.symm

theorem sound5278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5278 node5278Labels = Sparse.eval nodeValue5278 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5278) = mixedMoment B node5278 node5278Labels := rfl
  simpa [nodeValue5278, Sparse.eval] using hc.symm

theorem sound5279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5279 node5279Labels = Sparse.eval nodeValue5279 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5279) = mixedMoment B node5279 node5279Labels := rfl
  simpa [nodeValue5279, Sparse.eval] using hc.symm

theorem sound5281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5281 node5281Labels = Sparse.eval nodeValue5281 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5281) = mixedMoment B node5281 node5281Labels := rfl
  simpa [nodeValue5281, Sparse.eval] using hc.symm

theorem sound5282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5282 node5282Labels = Sparse.eval nodeValue5282 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5282) = mixedMoment B node5282 node5282Labels := rfl
  simpa [nodeValue5282, Sparse.eval] using hc.symm

theorem sound5284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5284 node5284Labels = Sparse.eval nodeValue5284 (mixedVector B) := by
  have h := singleton5284 B _hB
  rw [sound3077 B _hB _hF, sound3625 B _hB _hF] at h
  norm_num [nodeValue5284, nodeValue3077, nodeValue3625, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5286 node5286Labels = Sparse.eval nodeValue5286 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5286) = mixedMoment B node5286 node5286Labels := rfl
  simpa [nodeValue5286, Sparse.eval] using hc.symm

theorem sound5287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5287 node5287Labels = Sparse.eval nodeValue5287 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5287) = mixedMoment B node5287 node5287Labels := rfl
  simpa [nodeValue5287, Sparse.eval] using hc.symm

theorem sound5288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5288 node5288Labels = Sparse.eval nodeValue5288 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5288) = mixedMoment B node5288 node5288Labels := rfl
  simpa [nodeValue5288, Sparse.eval] using hc.symm

theorem sound5289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5289 node5289Labels = Sparse.eval nodeValue5289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5289) = mixedMoment B node5289 node5289Labels := rfl
  simpa [nodeValue5289, Sparse.eval] using hc.symm

theorem sound5290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5290 node5290Labels = Sparse.eval nodeValue5290 (mixedVector B) := by
  have h := singleton5290 B _hB
  rw [sound2764 B _hB _hF, sound3581 B _hB _hF] at h
  norm_num [nodeValue5290, nodeValue2764, nodeValue3581, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5291 node5291Labels = Sparse.eval nodeValue5291 (mixedVector B) := by
  have h := singleton5291 B _hB
  rw [sound2765 B _hB _hF, sound3582 B _hB _hF] at h
  norm_num [nodeValue5291, nodeValue2765, nodeValue3582, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5295 node5295Labels = Sparse.eval nodeValue5295 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5295) = mixedMoment B node5295 node5295Labels := rfl
  simpa [nodeValue5295, Sparse.eval] using hc.symm

theorem sound5297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5297 node5297Labels = Sparse.eval nodeValue5297 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5297) = mixedMoment B node5297 node5297Labels := rfl
  simpa [nodeValue5297, Sparse.eval] using hc.symm

theorem sound5299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5299 node5299Labels = Sparse.eval nodeValue5299 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5299) = mixedMoment B node5299 node5299Labels := rfl
  simpa [nodeValue5299, Sparse.eval] using hc.symm

theorem sound5300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5300 node5300Labels = Sparse.eval nodeValue5300 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5300) = mixedMoment B node5300 node5300Labels := rfl
  simpa [nodeValue5300, Sparse.eval] using hc.symm

theorem sound5301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5301 node5301Labels = Sparse.eval nodeValue5301 (mixedVector B) := by
  have h := singleton5301 B _hB
  rw [sound3053 B _hB _hF, sound3619 B _hB _hF] at h
  norm_num [nodeValue5301, nodeValue3053, nodeValue3619, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5303 node5303Labels = Sparse.eval nodeValue5303 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5303) = mixedMoment B node5303 node5303Labels := rfl
  simpa [nodeValue5303, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1799 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1799 x = (11015478679850975232000 : ℝ) * Sparse.eval nodeValue5206 x := by
  norm_num [reducedTerm1799, nodeValue5206, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1800 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1800 x = (-11601654236794847232000 : ℝ) * Sparse.eval nodeValue5215 x := by
  norm_num [reducedTerm1800, nodeValue5215, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1801 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1801 x = (-238272485558059008000 : ℝ) * Sparse.eval nodeValue5216 x := by
  norm_num [reducedTerm1801, nodeValue5216, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1802 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1802 x = (9806018085126144000000 : ℝ) * Sparse.eval nodeValue5217 x := by
  norm_num [reducedTerm1802, nodeValue5217, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1803 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1803 x = (10171942174410670080000 : ℝ) * Sparse.eval nodeValue5219 x := by
  norm_num [reducedTerm1803, nodeValue5219, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1804 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1804 x = (-381292928484507648000 : ℝ) * Sparse.eval nodeValue5220 x := by
  norm_num [reducedTerm1804, nodeValue5220, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1805 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1805 x = (3552860462980792320000 : ℝ) * Sparse.eval nodeValue5222 x := by
  norm_num [reducedTerm1805, nodeValue5222, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1806 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1806 x = (7805365883397734400000 : ℝ) * Sparse.eval nodeValue5226 x := by
  norm_num [reducedTerm1806, nodeValue5226, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1807 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1807 x = (12678992556746342400000 : ℝ) * Sparse.eval nodeValue5229 x := by
  norm_num [reducedTerm1807, nodeValue5229, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1808 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1808 x = (8788145924144627712000 : ℝ) * Sparse.eval nodeValue5231 x := by
  norm_num [reducedTerm1808, nodeValue5231, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1809 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1809 x = (14640885025087684608000 : ℝ) * Sparse.eval nodeValue5232 x := by
  norm_num [reducedTerm1809, nodeValue5232, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1810 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1810 x = (4998927687537917952000 : ℝ) * Sparse.eval nodeValue5233 x := by
  norm_num [reducedTerm1810, nodeValue5233, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1811 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1811 x = (1313082224189374464000 : ℝ) * Sparse.eval nodeValue5235 x := by
  norm_num [reducedTerm1811, nodeValue5235, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1812 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1812 x = (-9806018085126144000000 : ℝ) * Sparse.eval nodeValue5236 x := by
  norm_num [reducedTerm1812, nodeValue5236, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1813 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1813 x = (2663428588472107008000 : ℝ) * Sparse.eval nodeValue5243 x := by
  norm_num [reducedTerm1813, nodeValue5243, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1814 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1814 x = (-12840196478415667200000 : ℝ) * Sparse.eval nodeValue5244 x := by
  norm_num [reducedTerm1814, nodeValue5244, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1815 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1815 x = (8721406518151348224000 : ℝ) * Sparse.eval nodeValue5249 x := by
  norm_num [reducedTerm1815, nodeValue5249, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1816 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1816 x = (8435298163010568192000 : ℝ) * Sparse.eval nodeValue5250 x := by
  norm_num [reducedTerm1816, nodeValue5250, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1817 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1817 x = (20804483957839626240000 : ℝ) * Sparse.eval nodeValue5251 x := by
  norm_num [reducedTerm1817, nodeValue5251, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1818 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1818 x = (-15787189652894908416000 : ℝ) * Sparse.eval nodeValue5252 x := by
  norm_num [reducedTerm1818, nodeValue5252, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1819 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1819 x = (-18103702594567274496000 : ℝ) * Sparse.eval nodeValue5254 x := by
  norm_num [reducedTerm1819, nodeValue5254, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1820 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1820 x = (10628823676665987072000 : ℝ) * Sparse.eval nodeValue5255 x := by
  norm_num [reducedTerm1820, nodeValue5255, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1821 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1821 x = (-20080805161466068992000 : ℝ) * Sparse.eval nodeValue5256 x := by
  norm_num [reducedTerm1821, nodeValue5256, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1822 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1822 x = (-15245025399602675712000 : ℝ) * Sparse.eval nodeValue5257 x := by
  norm_num [reducedTerm1822, nodeValue5257, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1823 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1823 x = (-22663092721051238400000 : ℝ) * Sparse.eval nodeValue5258 x := by
  norm_num [reducedTerm1823, nodeValue5258, Integer.Sparse.eval, Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1824 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1824 x = (-5675419988165394432000 : ℝ) * Sparse.eval nodeValue5259 x := by
  norm_num [reducedTerm1824, nodeValue5259, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1825 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1825 x = (9126071378630148096000 : ℝ) * Sparse.eval nodeValue5260 x := by
  norm_num [reducedTerm1825, nodeValue5260, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1826 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1826 x = (-16830413886397612032000 : ℝ) * Sparse.eval nodeValue5263 x := by
  norm_num [reducedTerm1826, nodeValue5263, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1827 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1827 x = (642323079345733632000 : ℝ) * Sparse.eval nodeValue5264 x := by
  norm_num [reducedTerm1827, nodeValue5264, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1828 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1828 x = (-25288345262529183744000 : ℝ) * Sparse.eval nodeValue5265 x := by
  norm_num [reducedTerm1828, nodeValue5265, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1829 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1829 x = (-23758552131121446912000 : ℝ) * Sparse.eval nodeValue5266 x := by
  norm_num [reducedTerm1829, nodeValue5266, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1830 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1830 x = (-28266402523973419008000 : ℝ) * Sparse.eval nodeValue5267 x := by
  norm_num [reducedTerm1830, nodeValue5267, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1831 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1831 x = (-30906556284937568256000 : ℝ) * Sparse.eval nodeValue5268 x := by
  norm_num [reducedTerm1831, nodeValue5268, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1832 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1832 x = (19094161853855563776000 : ℝ) * Sparse.eval nodeValue5269 x := by
  norm_num [reducedTerm1832, nodeValue5269, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1833 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1833 x = (23882407552008585216000 : ℝ) * Sparse.eval nodeValue5270 x := by
  norm_num [reducedTerm1833, nodeValue5270, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1834 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1834 x = (39966852963647619072000 : ℝ) * Sparse.eval nodeValue5271 x := by
  norm_num [reducedTerm1834, nodeValue5271, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1835 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1835 x = (14928515917895172096000 : ℝ) * Sparse.eval nodeValue5272 x := by
  norm_num [reducedTerm1835, nodeValue5272, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1836 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1836 x = (30317413650479972352000 : ℝ) * Sparse.eval nodeValue5273 x := by
  norm_num [reducedTerm1836, nodeValue5273, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1837 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1837 x = (42629122980199268352000 : ℝ) * Sparse.eval nodeValue5274 x := by
  norm_num [reducedTerm1837, nodeValue5274, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1838 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1838 x = (8524243055252865024000 : ℝ) * Sparse.eval nodeValue5275 x := by
  norm_num [reducedTerm1838, nodeValue5275, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1839 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1839 x = (-48308943425120501760000 : ℝ) * Sparse.eval nodeValue5276 x := by
  norm_num [reducedTerm1839, nodeValue5276, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1840 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1840 x = (-7408755837351493632000 : ℝ) * Sparse.eval nodeValue5277 x := by
  norm_num [reducedTerm1840, nodeValue5277, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1841 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1841 x = (-5384845512904015872000 : ℝ) * Sparse.eval nodeValue5278 x := by
  norm_num [reducedTerm1841, nodeValue5278, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1842 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1842 x = (-13629983004992471040000 : ℝ) * Sparse.eval nodeValue5279 x := by
  norm_num [reducedTerm1842, nodeValue5279, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1843 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1843 x = (68956627891077513216000 : ℝ) * Sparse.eval nodeValue5281 x := by
  norm_num [reducedTerm1843, nodeValue5281, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1844 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1844 x = (-12260480058351157248000 : ℝ) * Sparse.eval nodeValue5282 x := by
  norm_num [reducedTerm1844, nodeValue5282, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1845 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1845 x = (-2084247660732088320000 : ℝ) * Sparse.eval nodeValue5284 x := by
  norm_num [reducedTerm1845, nodeValue5284, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1846 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1846 x = (-23256277065636249600000 : ℝ) * Sparse.eval nodeValue5286 x := by
  norm_num [reducedTerm1846, nodeValue5286, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1847 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1847 x = (-14631219146636918784000 : ℝ) * Sparse.eval nodeValue5287 x := by
  norm_num [reducedTerm1847, nodeValue5287, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1848 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1848 x = (-1665714719287148544000 : ℝ) * Sparse.eval nodeValue5288 x := by
  norm_num [reducedTerm1848, nodeValue5288, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1849 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1849 x = (-190845340189813112832000 : ℝ) * Sparse.eval nodeValue5289 x := by
  norm_num [reducedTerm1849, nodeValue5289, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1850 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1850 x = (-37872715526115950592000 : ℝ) * Sparse.eval nodeValue5290 x := by
  norm_num [reducedTerm1850, nodeValue5290, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1851 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1851 x = (-10945159428569038848000 : ℝ) * Sparse.eval nodeValue5291 x := by
  norm_num [reducedTerm1851, nodeValue5291, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1852 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1852 x = (-90385457830414516224000 : ℝ) * Sparse.eval nodeValue5295 x := by
  norm_num [reducedTerm1852, nodeValue5295, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1853 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1853 x = (-4322559273236692992000 : ℝ) * Sparse.eval nodeValue5297 x := by
  norm_num [reducedTerm1853, nodeValue5297, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1854 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1854 x = (-9865202604365316096000 : ℝ) * Sparse.eval nodeValue5299 x := by
  norm_num [reducedTerm1854, nodeValue5299, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1855 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1855 x = (-19050929198037467136000 : ℝ) * Sparse.eval nodeValue5300 x := by
  norm_num [reducedTerm1855, nodeValue5300, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1856 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1856 x = (-2253121590734880768000 : ℝ) * Sparse.eval nodeValue5301 x := by
  norm_num [reducedTerm1856, nodeValue5301, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1857 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1857 x = (-14840044105274228736000 : ℝ) * Sparse.eval nodeValue5302 x := by
  norm_num [reducedTerm1857, nodeValue5302, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1858 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1858 x = (4117655551595249664000 : ℝ) * Sparse.eval nodeValue5303 x := by
  norm_num [reducedTerm1858, nodeValue5303, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1795Check : reducedMerge1795 = Integer.Sparse.mergeBy masterLess reducedTerm1800 reducedTerm1801 := by decide +kernel

theorem reducedMerge1796Check : reducedMerge1796 = Integer.Sparse.mergeBy masterLess reducedTerm1799 reducedMerge1795 := by decide +kernel

theorem reducedMerge1797Check : reducedMerge1797 = Integer.Sparse.mergeBy masterLess reducedTerm1802 reducedTerm1803 := by decide +kernel

theorem reducedMerge1798Check : reducedMerge1798 = Integer.Sparse.mergeBy masterLess reducedTerm1804 reducedTerm1805 := by decide +kernel

theorem reducedMerge1799Check : reducedMerge1799 = Integer.Sparse.mergeBy masterLess reducedMerge1797 reducedMerge1798 := by decide +kernel

theorem reducedMerge1800Check : reducedMerge1800 = Integer.Sparse.mergeBy masterLess reducedMerge1796 reducedMerge1799 := by decide +kernel

theorem reducedMerge1801Check : reducedMerge1801 = Integer.Sparse.mergeBy masterLess reducedTerm1806 reducedTerm1807 := by decide +kernel

theorem reducedMerge1802Check : reducedMerge1802 = Integer.Sparse.mergeBy masterLess reducedTerm1808 reducedTerm1809 := by decide +kernel

theorem reducedMerge1803Check : reducedMerge1803 = Integer.Sparse.mergeBy masterLess reducedMerge1801 reducedMerge1802 := by decide +kernel

theorem reducedMerge1804Check : reducedMerge1804 = Integer.Sparse.mergeBy masterLess reducedTerm1810 reducedTerm1811 := by decide +kernel

theorem reducedMerge1805Check : reducedMerge1805 = Integer.Sparse.mergeBy masterLess reducedTerm1812 reducedTerm1813 := by decide +kernel

theorem reducedMerge1806Check : reducedMerge1806 = Integer.Sparse.mergeBy masterLess reducedMerge1804 reducedMerge1805 := by decide +kernel

theorem reducedMerge1807Check : reducedMerge1807 = Integer.Sparse.mergeBy masterLess reducedMerge1803 reducedMerge1806 := by decide +kernel

theorem reducedMerge1808Check : reducedMerge1808 = Integer.Sparse.mergeBy masterLess reducedMerge1800 reducedMerge1807 := by decide +kernel

theorem reducedMerge1809Check : reducedMerge1809 = Integer.Sparse.mergeBy masterLess reducedTerm1815 reducedTerm1816 := by decide +kernel

theorem reducedMerge1810Check : reducedMerge1810 = Integer.Sparse.mergeBy masterLess reducedTerm1814 reducedMerge1809 := by decide +kernel

theorem reducedMerge1811Check : reducedMerge1811 = Integer.Sparse.mergeBy masterLess reducedTerm1817 reducedTerm1818 := by decide +kernel

theorem reducedMerge1812Check : reducedMerge1812 = Integer.Sparse.mergeBy masterLess reducedTerm1819 reducedTerm1820 := by decide +kernel

theorem reducedMerge1813Check : reducedMerge1813 = Integer.Sparse.mergeBy masterLess reducedMerge1811 reducedMerge1812 := by decide +kernel

theorem reducedMerge1814Check : reducedMerge1814 = Integer.Sparse.mergeBy masterLess reducedMerge1810 reducedMerge1813 := by decide +kernel

theorem reducedMerge1815Check : reducedMerge1815 = Integer.Sparse.mergeBy masterLess reducedTerm1821 reducedTerm1822 := by decide +kernel

theorem reducedMerge1816Check : reducedMerge1816 = Integer.Sparse.mergeBy masterLess reducedTerm1823 reducedTerm1824 := by decide +kernel

theorem reducedMerge1817Check : reducedMerge1817 = Integer.Sparse.mergeBy masterLess reducedMerge1815 reducedMerge1816 := by decide +kernel

theorem reducedMerge1818Check : reducedMerge1818 = Integer.Sparse.mergeBy masterLess reducedTerm1825 reducedTerm1826 := by decide +kernel

theorem reducedMerge1819Check : reducedMerge1819 = Integer.Sparse.mergeBy masterLess reducedTerm1827 reducedTerm1828 := by decide +kernel

theorem reducedMerge1820Check : reducedMerge1820 = Integer.Sparse.mergeBy masterLess reducedMerge1818 reducedMerge1819 := by decide +kernel

theorem reducedMerge1821Check : reducedMerge1821 = Integer.Sparse.mergeBy masterLess reducedMerge1817 reducedMerge1820 := by decide +kernel

theorem reducedMerge1822Check : reducedMerge1822 = Integer.Sparse.mergeBy masterLess reducedMerge1814 reducedMerge1821 := by decide +kernel

theorem reducedMerge1823Check : reducedMerge1823 = Integer.Sparse.mergeBy masterLess reducedMerge1808 reducedMerge1822 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1824Check : reducedMerge1824 = Integer.Sparse.mergeBy masterLess reducedTerm1830 reducedTerm1831 := by decide +kernel

theorem reducedMerge1825Check : reducedMerge1825 = Integer.Sparse.mergeBy masterLess reducedTerm1829 reducedMerge1824 := by decide +kernel

theorem reducedMerge1826Check : reducedMerge1826 = Integer.Sparse.mergeBy masterLess reducedTerm1832 reducedTerm1833 := by decide +kernel

theorem reducedMerge1827Check : reducedMerge1827 = Integer.Sparse.mergeBy masterLess reducedTerm1834 reducedTerm1835 := by decide +kernel

theorem reducedMerge1828Check : reducedMerge1828 = Integer.Sparse.mergeBy masterLess reducedMerge1826 reducedMerge1827 := by decide +kernel

theorem reducedMerge1829Check : reducedMerge1829 = Integer.Sparse.mergeBy masterLess reducedMerge1825 reducedMerge1828 := by decide +kernel

theorem reducedMerge1830Check : reducedMerge1830 = Integer.Sparse.mergeBy masterLess reducedTerm1836 reducedTerm1837 := by decide +kernel

theorem reducedMerge1831Check : reducedMerge1831 = Integer.Sparse.mergeBy masterLess reducedTerm1838 reducedTerm1839 := by decide +kernel

theorem reducedMerge1832Check : reducedMerge1832 = Integer.Sparse.mergeBy masterLess reducedMerge1830 reducedMerge1831 := by decide +kernel

theorem reducedMerge1833Check : reducedMerge1833 = Integer.Sparse.mergeBy masterLess reducedTerm1840 reducedTerm1841 := by decide +kernel

theorem reducedMerge1834Check : reducedMerge1834 = Integer.Sparse.mergeBy masterLess reducedTerm1842 reducedTerm1843 := by decide +kernel

theorem reducedMerge1835Check : reducedMerge1835 = Integer.Sparse.mergeBy masterLess reducedMerge1833 reducedMerge1834 := by decide +kernel

theorem reducedMerge1836Check : reducedMerge1836 = Integer.Sparse.mergeBy masterLess reducedMerge1832 reducedMerge1835 := by decide +kernel

theorem reducedMerge1837Check : reducedMerge1837 = Integer.Sparse.mergeBy masterLess reducedMerge1829 reducedMerge1836 := by decide +kernel

theorem reducedMerge1838Check : reducedMerge1838 = Integer.Sparse.mergeBy masterLess reducedTerm1845 reducedTerm1846 := by decide +kernel

theorem reducedMerge1839Check : reducedMerge1839 = Integer.Sparse.mergeBy masterLess reducedTerm1844 reducedMerge1838 := by decide +kernel

theorem reducedMerge1840Check : reducedMerge1840 = Integer.Sparse.mergeBy masterLess reducedTerm1847 reducedTerm1848 := by decide +kernel

theorem reducedMerge1841Check : reducedMerge1841 = Integer.Sparse.mergeBy masterLess reducedTerm1849 reducedTerm1850 := by decide +kernel

theorem reducedMerge1842Check : reducedMerge1842 = Integer.Sparse.mergeBy masterLess reducedMerge1840 reducedMerge1841 := by decide +kernel

theorem reducedMerge1843Check : reducedMerge1843 = Integer.Sparse.mergeBy masterLess reducedMerge1839 reducedMerge1842 := by decide +kernel

theorem reducedMerge1844Check : reducedMerge1844 = Integer.Sparse.mergeBy masterLess reducedTerm1851 reducedTerm1852 := by decide +kernel

theorem reducedMerge1845Check : reducedMerge1845 = Integer.Sparse.mergeBy masterLess reducedTerm1853 reducedTerm1854 := by decide +kernel

theorem reducedMerge1846Check : reducedMerge1846 = Integer.Sparse.mergeBy masterLess reducedMerge1844 reducedMerge1845 := by decide +kernel

theorem reducedMerge1847Check : reducedMerge1847 = Integer.Sparse.mergeBy masterLess reducedTerm1855 reducedTerm1856 := by decide +kernel

theorem reducedMerge1848Check : reducedMerge1848 = Integer.Sparse.mergeBy masterLess reducedTerm1857 reducedTerm1858 := by decide +kernel

theorem reducedMerge1849Check : reducedMerge1849 = Integer.Sparse.mergeBy masterLess reducedMerge1847 reducedMerge1848 := by decide +kernel

theorem reducedMerge1850Check : reducedMerge1850 = Integer.Sparse.mergeBy masterLess reducedMerge1846 reducedMerge1849 := by decide +kernel

theorem reducedMerge1851Check : reducedMerge1851 = Integer.Sparse.mergeBy masterLess reducedMerge1843 reducedMerge1850 := by decide +kernel

theorem reducedMerge1852Check : reducedMerge1852 = Integer.Sparse.mergeBy masterLess reducedMerge1837 reducedMerge1851 := by decide +kernel

theorem reducedMerge1853Check : reducedMerge1853 = Integer.Sparse.mergeBy masterLess reducedMerge1823 reducedMerge1852 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1913Check : reducedMerge1913 = Integer.Sparse.mergeBy masterLess reducedMerge1853 reducedMerge1912 := by decide +kernel

theorem reducedMerge1914Check : reducedMerge1914 = Integer.Sparse.mergeBy masterLess reducedMerge1794 reducedMerge1913 := by decide +kernel

theorem reducedMerge1915Check : reducedMerge1915 = Integer.Sparse.mergeBy masterLess reducedMerge1675 reducedMerge1914 := by decide +kernel

theorem reducedMerge1916Check : reducedMerge1916 = Integer.Sparse.mergeBy masterLess reducedMerge1436 reducedMerge1915 := by decide +kernel

theorem reducedMerge1917Check : reducedMerge1917 = Integer.Sparse.mergeBy masterLess reducedMerge957 reducedMerge1916 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionFinalArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem numericRawPolynomialEval (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval numericRawPolynomial x =
      Integer.Combination.eval MixedData.targetRows x MixedData.rawCombination := by
  simp only [numericRawPolynomial, Integer.Sparse.eval_append, MixedData.rawCombination, Integer.Combination.eval]
  rfl

theorem originalReductionCheck : originalMerge1917 = originalPolynomial := by decide +kernel

theorem numericReductionCheck : reducedMerge1917 =
    Integer.Sparse.collectBalanced masterLess (Integer.Sparse.reindex keyMap numericRawPolynomial) := by decide +kernel

theorem numericReductionEval (B : Fin 7 → Basis) :
    Integer.Sparse.eval reducedMerge1917 (mixedVector B) =
      Integer.Combination.eval MixedData.targetRows (numericVector B) MixedData.rawCombination := by
  rw [numericReductionCheck, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_reindex]
  exact numericRawPolynomialEval _

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1799 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1799 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1799 (originalVector B) := by
  rw [reducedTermArithmetic1799, ← sound5206 B hB hF]
  change (11015478679850975232000 : ℝ) * mixedMoment B node5206 node5206Labels =
    (37623398400 : ℝ) * ((292782660480 : ℝ) * mixedMoment B node5206 node5206Labels + 0)
  ring

theorem reducedTermEval1800 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1800 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1800 (originalVector B) := by
  rw [reducedTermArithmetic1800, ← sound5215 B hB hF]
  change (-11601654236794847232000 : ℝ) * mixedMoment B node5215 node5215Labels =
    (37623398400 : ℝ) * (((-308362740480 : ℤ) : ℝ) * mixedMoment B node5215 node5215Labels + 0)
  ring

theorem reducedTermEval1801 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1801 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1801 (originalVector B) := by
  rw [reducedTermArithmetic1801, ← sound5216 B hB hF]
  change (-238272485558059008000 : ℝ) * mixedMoment B node5216 node5216Labels =
    (37623398400 : ℝ) * (((-6333093120 : ℤ) : ℝ) * mixedMoment B node5216 node5216Labels + 0)
  ring

theorem reducedTermEval1802 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1802 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1802 (originalVector B) := by
  rw [reducedTermArithmetic1802, ← sound5217 B hB hF]
  change (9806018085126144000000 : ℝ) * mixedMoment B node5217 node5217Labels =
    (37623398400 : ℝ) * ((260636160000 : ℝ) * mixedMoment B node5217 node5217Labels + 0)
  ring

theorem reducedTermEval1803 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1803 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1803 (originalVector B) := by
  rw [reducedTermArithmetic1803, ← sound5219 B hB hF]
  change (10171942174410670080000 : ℝ) * mixedMoment B node5219 node5219Labels =
    (37623398400 : ℝ) * ((270362131200 : ℝ) * mixedMoment B node5219 node5219Labels + 0)
  ring

theorem reducedTermEval1804 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1804 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1804 (originalVector B) := by
  rw [reducedTermArithmetic1804, ← sound5220 B hB hF]
  change (-381292928484507648000 : ℝ) * mixedMoment B node5220 node5220Labels =
    (37623398400 : ℝ) * (((-10134462720 : ℤ) : ℝ) * mixedMoment B node5220 node5220Labels + 0)
  ring

theorem reducedTermEval1805 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1805 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1805 (originalVector B) := by
  rw [reducedTermArithmetic1805, ← sound5222 B hB hF]
  change (3552860462980792320000 : ℝ) * mixedMoment B node5222 node5222Labels =
    (37623398400 : ℝ) * ((94432204800 : ℝ) * mixedMoment B node5222 node5222Labels + 0)
  ring

theorem reducedTermEval1806 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1806 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1806 (originalVector B) := by
  rw [reducedTermArithmetic1806, ← sound5226 B hB hF]
  change (7805365883397734400000 : ℝ) * mixedMoment B node5226 node5226Labels =
    (37623398400 : ℝ) * ((207460416000 : ℝ) * mixedMoment B node5226 node5226Labels + 0)
  ring

theorem reducedTermEval1807 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1807 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1807 (originalVector B) := by
  rw [reducedTermArithmetic1807, ← sound5229 B hB hF]
  change (12678992556746342400000 : ℝ) * mixedMoment B node5229 node5229Labels =
    (37623398400 : ℝ) * ((336997536000 : ℝ) * mixedMoment B node5229 node5229Labels + 0)
  ring

theorem reducedTermEval1808 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1808 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1808 (originalVector B) := by
  rw [reducedTermArithmetic1808, ← sound5231 B hB hF]
  change (8788145924144627712000 : ℝ) * mixedMoment B node5231 node5231Labels =
    (37623398400 : ℝ) * ((233581927680 : ℝ) * mixedMoment B node5231 node5231Labels + 0)
  ring

theorem reducedTermEval1809 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1809 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1809 (originalVector B) := by
  rw [reducedTermArithmetic1809, ← sound5232 B hB hF]
  change (14640885025087684608000 : ℝ) * mixedMoment B node5232 node5232Labels =
    (37623398400 : ℝ) * ((389143077120 : ℝ) * mixedMoment B node5232 node5232Labels + 0)
  ring

theorem reducedTermEval1810 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1810 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1810 (originalVector B) := by
  rw [reducedTermArithmetic1810, ← sound5233 B hB hF]
  change (4998927687537917952000 : ℝ) * mixedMoment B node5233 node5233Labels =
    (37623398400 : ℝ) * ((132867521280 : ℝ) * mixedMoment B node5233 node5233Labels + 0)
  ring

theorem reducedTermEval1811 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1811 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1811 (originalVector B) := by
  rw [reducedTermArithmetic1811, ← sound5235 B hB hF]
  change (1313082224189374464000 : ℝ) * mixedMoment B node5235 node5235Labels =
    (37623398400 : ℝ) * ((34900680960 : ℝ) * mixedMoment B node5235 node5235Labels + 0)
  ring

theorem reducedTermEval1812 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1812 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1812 (originalVector B) := by
  rw [reducedTermArithmetic1812, ← sound5236 B hB hF]
  change (-9806018085126144000000 : ℝ) * mixedMoment B node5236 node5236Labels =
    (37623398400 : ℝ) * (((-260636160000 : ℤ) : ℝ) * mixedMoment B node5236 node5236Labels + 0)
  ring

theorem reducedTermEval1813 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1813 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1813 (originalVector B) := by
  rw [reducedTermArithmetic1813, ← sound5243 B hB hF]
  change (2663428588472107008000 : ℝ) * mixedMoment B node5243 node5243Labels =
    (37623398400 : ℝ) * ((70791813120 : ℝ) * mixedMoment B node5243 node5243Labels + 0)
  ring

theorem reducedTermEval1814 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1814 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1814 (originalVector B) := by
  rw [reducedTermArithmetic1814, ← sound5244 B hB hF]
  change (-12840196478415667200000 : ℝ) * mixedMoment B node5244 node5244Labels =
    (37623398400 : ℝ) * (((-341282208000 : ℤ) : ℝ) * mixedMoment B node5244 node5244Labels + 0)
  ring

theorem reducedTermEval1815 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1815 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1815 (originalVector B) := by
  rw [reducedTermArithmetic1815, ← sound5249 B hB hF]
  change (8721406518151348224000 : ℝ) * mixedMoment B node5249 node5249Labels =
    (37623398400 : ℝ) * ((231808047360 : ℝ) * mixedMoment B node5249 node5249Labels + 0)
  ring

theorem reducedTermEval1816 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1816 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1816 (originalVector B) := by
  rw [reducedTermArithmetic1816, ← sound5250 B hB hF]
  change (8435298163010568192000 : ℝ) * mixedMoment B node5250 node5250Labels =
    (37623398400 : ℝ) * ((224203514880 : ℝ) * mixedMoment B node5250 node5250Labels + 0)
  ring

theorem reducedTermEval1817 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1817 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1817 (originalVector B) := by
  rw [reducedTermArithmetic1817, ← sound5251 B hB hF]
  change (20804483957839626240000 : ℝ) * mixedMoment B node5251 node5251Labels =
    (37623398400 : ℝ) * ((552966633600 : ℝ) * mixedMoment B node5251 node5251Labels + 0)
  ring

theorem reducedTermEval1818 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1818 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1818 (originalVector B) := by
  rw [reducedTermArithmetic1818, ← sound5252 B hB hF]
  change (-15787189652894908416000 : ℝ) * mixedMoment B node5252 node5252Labels =
    (37623398400 : ℝ) * (((-419610942240 : ℤ) : ℝ) * mixedMoment B node5252 node5252Labels + 0)
  ring

theorem reducedTermEval1819 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1819 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1819 (originalVector B) := by
  rw [reducedTermArithmetic1819, ← sound5254 B hB hF]
  change (-18103702594567274496000 : ℝ) * mixedMoment B node5254 node5254Labels =
    (37623398400 : ℝ) * (((-481182013440 : ℤ) : ℝ) * mixedMoment B node5254 node5254Labels + 0)
  ring

theorem reducedTermEval1820 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1820 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1820 (originalVector B) := by
  rw [reducedTermArithmetic1820, ← sound5255 B hB hF]
  change (10628823676665987072000 : ℝ) * mixedMoment B node5255 node5255Labels =
    (37623398400 : ℝ) * ((282505678080 : ℝ) * mixedMoment B node5255 node5255Labels + 0)
  ring

theorem reducedTermEval1821 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1821 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1821 (originalVector B) := by
  rw [reducedTermArithmetic1821, ← sound5256 B hB hF]
  change (-20080805161466068992000 : ℝ) * mixedMoment B node5256 node5256Labels =
    (37623398400 : ℝ) * (((-533731826880 : ℤ) : ℝ) * mixedMoment B node5256 node5256Labels + 0)
  ring

theorem reducedTermEval1822 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1822 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1822 (originalVector B) := by
  rw [reducedTermArithmetic1822, ← sound5257 B hB hF]
  change (-15245025399602675712000 : ℝ) * mixedMoment B node5257 node5257Labels =
    (37623398400 : ℝ) * (((-405200647680 : ℤ) : ℝ) * mixedMoment B node5257 node5257Labels + 0)
  ring

theorem reducedTermEval1823 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1823 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1823 (originalVector B) := by
  rw [reducedTermArithmetic1823, ← sound5258 B hB hF]
  change (-22663092721051238400000 : ℝ) * mixedMoment B node5258 node5258Labels =
    (37623398400 : ℝ) * (((-602366976000 : ℤ) : ℝ) * mixedMoment B node5258 node5258Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1824 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1824 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1824 (originalVector B) := by
  rw [reducedTermArithmetic1824, ← sound5259 B hB hF]
  change (-5675419988165394432000 : ℝ) * mixedMoment B node5259 node5259Labels =
    (37623398400 : ℝ) * (((-150848148480 : ℤ) : ℝ) * mixedMoment B node5259 node5259Labels + 0)
  ring

theorem reducedTermEval1825 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1825 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1825 (originalVector B) := by
  rw [reducedTermArithmetic1825, ← sound5260 B hB hF]
  change (9126071378630148096000 : ℝ) * mixedMoment B node5260 node5260Labels =
    (37623398400 : ℝ) * ((242563717440 : ℝ) * mixedMoment B node5260 node5260Labels + 0)
  ring

theorem reducedTermEval1826 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1826 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1826 (originalVector B) := by
  rw [reducedTermArithmetic1826, ← sound5263 B hB hF]
  change (-16830413886397612032000 : ℝ) * mixedMoment B node5263 node5263Labels =
    (37623398400 : ℝ) * (((-447339012480 : ℤ) : ℝ) * mixedMoment B node5263 node5263Labels + 0)
  ring

theorem reducedTermEval1827 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1827 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1827 (originalVector B) := by
  rw [reducedTermArithmetic1827, ← sound5264 B hB hF]
  change (642323079345733632000 : ℝ) * mixedMoment B node5264 node5264Labels =
    (37623398400 : ℝ) * ((17072436480 : ℝ) * mixedMoment B node5264 node5264Labels + 0)
  ring

theorem reducedTermEval1828 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1828 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1828 (originalVector B) := by
  rw [reducedTermArithmetic1828, ← sound5265 B hB hF]
  change (-25288345262529183744000 : ℝ) * mixedMoment B node5265 node5265Labels =
    (37623398400 : ℝ) * (((-672144100160 : ℤ) : ℝ) * mixedMoment B node5265 node5265Labels + 0)
  ring

theorem reducedTermEval1829 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1829 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1829 (originalVector B) := by
  rw [reducedTermArithmetic1829, ← sound5266 B hB hF]
  change (-23758552131121446912000 : ℝ) * mixedMoment B node5266 node5266Labels =
    (37623398400 : ℝ) * (((-631483415680 : ℤ) : ℝ) * mixedMoment B node5266 node5266Labels + 0)
  ring

theorem reducedTermEval1830 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1830 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1830 (originalVector B) := by
  rw [reducedTermArithmetic1830, ← sound5267 B hB hF]
  change (-28266402523973419008000 : ℝ) * mixedMoment B node5267 node5267Labels =
    (37623398400 : ℝ) * (((-751298493120 : ℤ) : ℝ) * mixedMoment B node5267 node5267Labels + 0)
  ring

theorem reducedTermEval1831 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1831 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1831 (originalVector B) := by
  rw [reducedTermArithmetic1831, ← sound5268 B hB hF]
  change (-30906556284937568256000 : ℝ) * mixedMoment B node5268 node5268Labels =
    (37623398400 : ℝ) * (((-821471679840 : ℤ) : ℝ) * mixedMoment B node5268 node5268Labels + 0)
  ring

theorem reducedTermEval1832 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1832 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1832 (originalVector B) := by
  rw [reducedTermArithmetic1832, ← sound5269 B hB hF]
  change (19094161853855563776000 : ℝ) * mixedMoment B node5269 node5269Labels =
    (37623398400 : ℝ) * ((507507632640 : ℝ) * mixedMoment B node5269 node5269Labels + 0)
  ring

theorem reducedTermEval1833 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1833 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1833 (originalVector B) := by
  rw [reducedTermArithmetic1833, ← sound5270 B hB hF]
  change (23882407552008585216000 : ℝ) * mixedMoment B node5270 node5270Labels =
    (37623398400 : ℝ) * ((634775394240 : ℝ) * mixedMoment B node5270 node5270Labels + 0)
  ring

theorem reducedTermEval1834 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1834 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1834 (originalVector B) := by
  rw [reducedTermArithmetic1834, ← sound5271 B hB hF]
  change (39966852963647619072000 : ℝ) * mixedMoment B node5271 node5271Labels =
    (37623398400 : ℝ) * ((1062287158080 : ℝ) * mixedMoment B node5271 node5271Labels + 0)
  ring

theorem reducedTermEval1835 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1835 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1835 (originalVector B) := by
  rw [reducedTermArithmetic1835, ← sound5272 B hB hF]
  change (14928515917895172096000 : ℝ) * mixedMoment B node5272 node5272Labels =
    (37623398400 : ℝ) * ((396788077440 : ℝ) * mixedMoment B node5272 node5272Labels + 0)
  ring

theorem reducedTermEval1836 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1836 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1836 (originalVector B) := by
  rw [reducedTermArithmetic1836, ← sound5273 B hB hF]
  change (30317413650479972352000 : ℝ) * mixedMoment B node5273 node5273Labels =
    (37623398400 : ℝ) * ((805812737280 : ℝ) * mixedMoment B node5273 node5273Labels + 0)
  ring

theorem reducedTermEval1837 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1837 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1837 (originalVector B) := by
  rw [reducedTermArithmetic1837, ← sound5274 B hB hF]
  change (42629122980199268352000 : ℝ) * mixedMoment B node5274 node5274Labels =
    (37623398400 : ℝ) * ((1133048177280 : ℝ) * mixedMoment B node5274 node5274Labels + 0)
  ring

theorem reducedTermEval1838 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1838 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1838 (originalVector B) := by
  rw [reducedTermArithmetic1838, ← sound5275 B hB hF]
  change (8524243055252865024000 : ℝ) * mixedMoment B node5275 node5275Labels =
    (37623398400 : ℝ) * ((226567599360 : ℝ) * mixedMoment B node5275 node5275Labels + 0)
  ring

theorem reducedTermEval1839 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1839 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1839 (originalVector B) := by
  rw [reducedTermArithmetic1839, ← sound5276 B hB hF]
  change (-48308943425120501760000 : ℝ) * mixedMoment B node5276 node5276Labels =
    (37623398400 : ℝ) * (((-1284013286400 : ℤ) : ℝ) * mixedMoment B node5276 node5276Labels + 0)
  ring

theorem reducedTermEval1840 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1840 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1840 (originalVector B) := by
  rw [reducedTermArithmetic1840, ← sound5277 B hB hF]
  change (-7408755837351493632000 : ℝ) * mixedMoment B node5277 node5277Labels =
    (37623398400 : ℝ) * (((-196918836480 : ℤ) : ℝ) * mixedMoment B node5277 node5277Labels + 0)
  ring

theorem reducedTermEval1841 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1841 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1841 (originalVector B) := by
  rw [reducedTermArithmetic1841, ← sound5278 B hB hF]
  change (-5384845512904015872000 : ℝ) * mixedMoment B node5278 node5278Labels =
    (37623398400 : ℝ) * (((-143124910080 : ℤ) : ℝ) * mixedMoment B node5278 node5278Labels + 0)
  ring

theorem reducedTermEval1842 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1842 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1842 (originalVector B) := by
  rw [reducedTermArithmetic1842, ← sound5279 B hB hF]
  change (-13629983004992471040000 : ℝ) * mixedMoment B node5279 node5279Labels =
    (37623398400 : ℝ) * (((-362274105600 : ℤ) : ℝ) * mixedMoment B node5279 node5279Labels + 0)
  ring

theorem reducedTermEval1843 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1843 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1843 (originalVector B) := by
  rw [reducedTermArithmetic1843, ← sound5281 B hB hF]
  change (68956627891077513216000 : ℝ) * mixedMoment B node5281 node5281Labels =
    (37623398400 : ℝ) * ((1832812314240 : ℝ) * mixedMoment B node5281 node5281Labels + 0)
  ring

theorem reducedTermEval1844 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1844 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1844 (originalVector B) := by
  rw [reducedTermArithmetic1844, ← sound5282 B hB hF]
  change (-12260480058351157248000 : ℝ) * mixedMoment B node5282 node5282Labels =
    (37623398400 : ℝ) * (((-325873806720 : ℤ) : ℝ) * mixedMoment B node5282 node5282Labels + 0)
  ring

theorem reducedTermEval1845 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1845 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1845 (originalVector B) := by
  rw [reducedTermArithmetic1845, ← sound5284 B hB hF]
  change (-2084247660732088320000 : ℝ) * mixedMoment B node5284 node5284Labels =
    (37623398400 : ℝ) * (((-55397644800 : ℤ) : ℝ) * mixedMoment B node5284 node5284Labels + 0)
  ring

theorem reducedTermEval1846 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1846 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1846 (originalVector B) := by
  rw [reducedTermArithmetic1846, ← sound5286 B hB hF]
  change (-23256277065636249600000 : ℝ) * mixedMoment B node5286 node5286Labels =
    (37623398400 : ℝ) * (((-618133344000 : ℤ) : ℝ) * mixedMoment B node5286 node5286Labels + 0)
  ring

theorem reducedTermEval1847 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1847 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1847 (originalVector B) := by
  rw [reducedTermArithmetic1847, ← sound5287 B hB hF]
  change (-14631219146636918784000 : ℝ) * mixedMoment B node5287 node5287Labels =
    (37623398400 : ℝ) * (((-388886165760 : ℤ) : ℝ) * mixedMoment B node5287 node5287Labels + 0)
  ring

theorem reducedTermEval1848 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1848 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1848 (originalVector B) := by
  rw [reducedTermArithmetic1848, ← sound5288 B hB hF]
  change (-1665714719287148544000 : ℝ) * mixedMoment B node5288 node5288Labels =
    (37623398400 : ℝ) * (((-44273372160 : ℤ) : ℝ) * mixedMoment B node5288 node5288Labels + 0)
  ring

theorem reducedTermEval1849 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1849 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1849 (originalVector B) := by
  rw [reducedTermArithmetic1849, ← sound5289 B hB hF]
  change (-190845340189813112832000 : ℝ) * mixedMoment B node5289 node5289Labels =
    (37623398400 : ℝ) * (((-5072517324480 : ℤ) : ℝ) * mixedMoment B node5289 node5289Labels + 0)
  ring

theorem reducedTermEval1850 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1850 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1850 (originalVector B) := by
  rw [reducedTermArithmetic1850, ← sound5290 B hB hF]
  change (-37872715526115950592000 : ℝ) * mixedMoment B node5290 node5290Labels =
    (37623398400 : ℝ) * (((-1006626650880 : ℤ) : ℝ) * mixedMoment B node5290 node5290Labels + 0)
  ring

theorem reducedTermEval1851 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1851 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1851 (originalVector B) := by
  rw [reducedTermArithmetic1851, ← sound5291 B hB hF]
  change (-10945159428569038848000 : ℝ) * mixedMoment B node5291 node5291Labels =
    (37623398400 : ℝ) * (((-290913630720 : ℤ) : ℝ) * mixedMoment B node5291 node5291Labels + 0)
  ring

theorem reducedTermEval1852 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1852 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1852 (originalVector B) := by
  rw [reducedTermArithmetic1852, ← sound5295 B hB hF]
  change (-90385457830414516224000 : ℝ) * mixedMoment B node5295 node5295Labels =
    (37623398400 : ℝ) * (((-2402373567360 : ℤ) : ℝ) * mixedMoment B node5295 node5295Labels + 0)
  ring

theorem reducedTermEval1853 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1853 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1853 (originalVector B) := by
  rw [reducedTermArithmetic1853, ← sound5297 B hB hF]
  change (-4322559273236692992000 : ℝ) * mixedMoment B node5297 node5297Labels =
    (37623398400 : ℝ) * (((-114890186880 : ℤ) : ℝ) * mixedMoment B node5297 node5297Labels + 0)
  ring

theorem reducedTermEval1854 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1854 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1854 (originalVector B) := by
  rw [reducedTermArithmetic1854, ← sound5299 B hB hF]
  change (-9865202604365316096000 : ℝ) * mixedMoment B node5299 node5299Labels =
    (37623398400 : ℝ) * (((-262209237440 : ℤ) : ℝ) * mixedMoment B node5299 node5299Labels + 0)
  ring

theorem reducedTermEval1855 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1855 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1855 (originalVector B) := by
  rw [reducedTermArithmetic1855, ← sound5300 B hB hF]
  change (-19050929198037467136000 : ℝ) * mixedMoment B node5300 node5300Labels =
    (37623398400 : ℝ) * (((-506358543040 : ℤ) : ℝ) * mixedMoment B node5300 node5300Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1795 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1795 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1795 (originalVector B) := by
  rw [reducedMerge1795Check, Integer.Sparse.eval_mergeBy, reducedTermEval1800 B hB hF, reducedTermEval1801 B hB hF]
  rw [originalMerge1795, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1796 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1796 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1796 (originalVector B) := by
  rw [reducedMerge1796Check, Integer.Sparse.eval_mergeBy, reducedTermEval1799 B hB hF, reducedMergeEval1795 B hB hF]
  rw [originalMerge1796, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1797 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1797 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1797 (originalVector B) := by
  rw [reducedMerge1797Check, Integer.Sparse.eval_mergeBy, reducedTermEval1802 B hB hF, reducedTermEval1803 B hB hF]
  rw [originalMerge1797, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1798 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1798 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1798 (originalVector B) := by
  rw [reducedMerge1798Check, Integer.Sparse.eval_mergeBy, reducedTermEval1804 B hB hF, reducedTermEval1805 B hB hF]
  rw [originalMerge1798, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1799 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1799 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1799 (originalVector B) := by
  rw [reducedMerge1799Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1797 B hB hF, reducedMergeEval1798 B hB hF]
  rw [originalMerge1799, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1800 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1800 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1800 (originalVector B) := by
  rw [reducedMerge1800Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1796 B hB hF, reducedMergeEval1799 B hB hF]
  rw [originalMerge1800, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1801 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1801 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1801 (originalVector B) := by
  rw [reducedMerge1801Check, Integer.Sparse.eval_mergeBy, reducedTermEval1806 B hB hF, reducedTermEval1807 B hB hF]
  rw [originalMerge1801, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1802 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1802 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1802 (originalVector B) := by
  rw [reducedMerge1802Check, Integer.Sparse.eval_mergeBy, reducedTermEval1808 B hB hF, reducedTermEval1809 B hB hF]
  rw [originalMerge1802, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1803 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1803 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1803 (originalVector B) := by
  rw [reducedMerge1803Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1801 B hB hF, reducedMergeEval1802 B hB hF]
  rw [originalMerge1803, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1804 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1804 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1804 (originalVector B) := by
  rw [reducedMerge1804Check, Integer.Sparse.eval_mergeBy, reducedTermEval1810 B hB hF, reducedTermEval1811 B hB hF]
  rw [originalMerge1804, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1805 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1805 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1805 (originalVector B) := by
  rw [reducedMerge1805Check, Integer.Sparse.eval_mergeBy, reducedTermEval1812 B hB hF, reducedTermEval1813 B hB hF]
  rw [originalMerge1805, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1806 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1806 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1806 (originalVector B) := by
  rw [reducedMerge1806Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1804 B hB hF, reducedMergeEval1805 B hB hF]
  rw [originalMerge1806, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1807 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1807 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1807 (originalVector B) := by
  rw [reducedMerge1807Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1803 B hB hF, reducedMergeEval1806 B hB hF]
  rw [originalMerge1807, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1808 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1808 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1808 (originalVector B) := by
  rw [reducedMerge1808Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1800 B hB hF, reducedMergeEval1807 B hB hF]
  rw [originalMerge1808, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1809 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1809 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1809 (originalVector B) := by
  rw [reducedMerge1809Check, Integer.Sparse.eval_mergeBy, reducedTermEval1815 B hB hF, reducedTermEval1816 B hB hF]
  rw [originalMerge1809, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1810 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1810 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1810 (originalVector B) := by
  rw [reducedMerge1810Check, Integer.Sparse.eval_mergeBy, reducedTermEval1814 B hB hF, reducedMergeEval1809 B hB hF]
  rw [originalMerge1810, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1811 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1811 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1811 (originalVector B) := by
  rw [reducedMerge1811Check, Integer.Sparse.eval_mergeBy, reducedTermEval1817 B hB hF, reducedTermEval1818 B hB hF]
  rw [originalMerge1811, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1812 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1812 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1812 (originalVector B) := by
  rw [reducedMerge1812Check, Integer.Sparse.eval_mergeBy, reducedTermEval1819 B hB hF, reducedTermEval1820 B hB hF]
  rw [originalMerge1812, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1813 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1813 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1813 (originalVector B) := by
  rw [reducedMerge1813Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1811 B hB hF, reducedMergeEval1812 B hB hF]
  rw [originalMerge1813, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1814 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1814 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1814 (originalVector B) := by
  rw [reducedMerge1814Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1810 B hB hF, reducedMergeEval1813 B hB hF]
  rw [originalMerge1814, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1815 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1815 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1815 (originalVector B) := by
  rw [reducedMerge1815Check, Integer.Sparse.eval_mergeBy, reducedTermEval1821 B hB hF, reducedTermEval1822 B hB hF]
  rw [originalMerge1815, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1816 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1816 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1816 (originalVector B) := by
  rw [reducedMerge1816Check, Integer.Sparse.eval_mergeBy, reducedTermEval1823 B hB hF, reducedTermEval1824 B hB hF]
  rw [originalMerge1816, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1817 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1817 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1817 (originalVector B) := by
  rw [reducedMerge1817Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1815 B hB hF, reducedMergeEval1816 B hB hF]
  rw [originalMerge1817, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1818 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1818 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1818 (originalVector B) := by
  rw [reducedMerge1818Check, Integer.Sparse.eval_mergeBy, reducedTermEval1825 B hB hF, reducedTermEval1826 B hB hF]
  rw [originalMerge1818, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1819 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1819 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1819 (originalVector B) := by
  rw [reducedMerge1819Check, Integer.Sparse.eval_mergeBy, reducedTermEval1827 B hB hF, reducedTermEval1828 B hB hF]
  rw [originalMerge1819, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1820 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1820 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1820 (originalVector B) := by
  rw [reducedMerge1820Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1818 B hB hF, reducedMergeEval1819 B hB hF]
  rw [originalMerge1820, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1821 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1821 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1821 (originalVector B) := by
  rw [reducedMerge1821Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1817 B hB hF, reducedMergeEval1820 B hB hF]
  rw [originalMerge1821, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1822 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1822 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1822 (originalVector B) := by
  rw [reducedMerge1822Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1814 B hB hF, reducedMergeEval1821 B hB hF]
  rw [originalMerge1822, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1823 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1823 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1823 (originalVector B) := by
  rw [reducedMerge1823Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1808 B hB hF, reducedMergeEval1822 B hB hF]
  rw [originalMerge1823, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1856 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1856 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1856 (originalVector B) := by
  rw [reducedTermArithmetic1856, ← sound5301 B hB hF]
  change (-2253121590734880768000 : ℝ) * mixedMoment B node5301 node5301Labels =
    (37623398400 : ℝ) * (((-59886179520 : ℤ) : ℝ) * mixedMoment B node5301 node5301Labels + 0)
  ring

theorem reducedTermEval1857 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1857 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1857 (originalVector B) := by
  rw [reducedTermArithmetic1857, ← sound5302 B hB hF]
  change (-14840044105274228736000 : ℝ) * mixedMoment B node5302 node5302Labels =
    (37623398400 : ℝ) * (((-394436567040 : ℤ) : ℝ) * mixedMoment B node5302 node5302Labels + 0)
  ring

theorem reducedTermEval1858 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1858 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1858 (originalVector B) := by
  rw [reducedTermArithmetic1858, ← sound5303 B hB hF]
  change (4117655551595249664000 : ℝ) * mixedMoment B node5303 node5303Labels =
    (37623398400 : ℝ) * ((109444008960 : ℝ) * mixedMoment B node5303 node5303Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1824 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1824 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1824 (originalVector B) := by
  rw [reducedMerge1824Check, Integer.Sparse.eval_mergeBy, reducedTermEval1830 B hB hF, reducedTermEval1831 B hB hF]
  rw [originalMerge1824, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1825 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1825 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1825 (originalVector B) := by
  rw [reducedMerge1825Check, Integer.Sparse.eval_mergeBy, reducedTermEval1829 B hB hF, reducedMergeEval1824 B hB hF]
  rw [originalMerge1825, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1826 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1826 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1826 (originalVector B) := by
  rw [reducedMerge1826Check, Integer.Sparse.eval_mergeBy, reducedTermEval1832 B hB hF, reducedTermEval1833 B hB hF]
  rw [originalMerge1826, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1827 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1827 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1827 (originalVector B) := by
  rw [reducedMerge1827Check, Integer.Sparse.eval_mergeBy, reducedTermEval1834 B hB hF, reducedTermEval1835 B hB hF]
  rw [originalMerge1827, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1828 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1828 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1828 (originalVector B) := by
  rw [reducedMerge1828Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1826 B hB hF, reducedMergeEval1827 B hB hF]
  rw [originalMerge1828, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1829 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1829 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1829 (originalVector B) := by
  rw [reducedMerge1829Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1825 B hB hF, reducedMergeEval1828 B hB hF]
  rw [originalMerge1829, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1830 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1830 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1830 (originalVector B) := by
  rw [reducedMerge1830Check, Integer.Sparse.eval_mergeBy, reducedTermEval1836 B hB hF, reducedTermEval1837 B hB hF]
  rw [originalMerge1830, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1831 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1831 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1831 (originalVector B) := by
  rw [reducedMerge1831Check, Integer.Sparse.eval_mergeBy, reducedTermEval1838 B hB hF, reducedTermEval1839 B hB hF]
  rw [originalMerge1831, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1832 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1832 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1832 (originalVector B) := by
  rw [reducedMerge1832Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1830 B hB hF, reducedMergeEval1831 B hB hF]
  rw [originalMerge1832, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1833 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1833 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1833 (originalVector B) := by
  rw [reducedMerge1833Check, Integer.Sparse.eval_mergeBy, reducedTermEval1840 B hB hF, reducedTermEval1841 B hB hF]
  rw [originalMerge1833, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1834 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1834 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1834 (originalVector B) := by
  rw [reducedMerge1834Check, Integer.Sparse.eval_mergeBy, reducedTermEval1842 B hB hF, reducedTermEval1843 B hB hF]
  rw [originalMerge1834, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1835 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1835 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1835 (originalVector B) := by
  rw [reducedMerge1835Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1833 B hB hF, reducedMergeEval1834 B hB hF]
  rw [originalMerge1835, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1836 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1836 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1836 (originalVector B) := by
  rw [reducedMerge1836Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1832 B hB hF, reducedMergeEval1835 B hB hF]
  rw [originalMerge1836, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1837 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1837 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1837 (originalVector B) := by
  rw [reducedMerge1837Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1829 B hB hF, reducedMergeEval1836 B hB hF]
  rw [originalMerge1837, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1838 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1838 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1838 (originalVector B) := by
  rw [reducedMerge1838Check, Integer.Sparse.eval_mergeBy, reducedTermEval1845 B hB hF, reducedTermEval1846 B hB hF]
  rw [originalMerge1838, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1839 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1839 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1839 (originalVector B) := by
  rw [reducedMerge1839Check, Integer.Sparse.eval_mergeBy, reducedTermEval1844 B hB hF, reducedMergeEval1838 B hB hF]
  rw [originalMerge1839, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1840 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1840 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1840 (originalVector B) := by
  rw [reducedMerge1840Check, Integer.Sparse.eval_mergeBy, reducedTermEval1847 B hB hF, reducedTermEval1848 B hB hF]
  rw [originalMerge1840, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1841 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1841 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1841 (originalVector B) := by
  rw [reducedMerge1841Check, Integer.Sparse.eval_mergeBy, reducedTermEval1849 B hB hF, reducedTermEval1850 B hB hF]
  rw [originalMerge1841, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1842 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1842 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1842 (originalVector B) := by
  rw [reducedMerge1842Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1840 B hB hF, reducedMergeEval1841 B hB hF]
  rw [originalMerge1842, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1843 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1843 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1843 (originalVector B) := by
  rw [reducedMerge1843Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1839 B hB hF, reducedMergeEval1842 B hB hF]
  rw [originalMerge1843, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1844 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1844 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1844 (originalVector B) := by
  rw [reducedMerge1844Check, Integer.Sparse.eval_mergeBy, reducedTermEval1851 B hB hF, reducedTermEval1852 B hB hF]
  rw [originalMerge1844, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1845 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1845 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1845 (originalVector B) := by
  rw [reducedMerge1845Check, Integer.Sparse.eval_mergeBy, reducedTermEval1853 B hB hF, reducedTermEval1854 B hB hF]
  rw [originalMerge1845, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1846 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1846 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1846 (originalVector B) := by
  rw [reducedMerge1846Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1844 B hB hF, reducedMergeEval1845 B hB hF]
  rw [originalMerge1846, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1847 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1847 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1847 (originalVector B) := by
  rw [reducedMerge1847Check, Integer.Sparse.eval_mergeBy, reducedTermEval1855 B hB hF, reducedTermEval1856 B hB hF]
  rw [originalMerge1847, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1848 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1848 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1848 (originalVector B) := by
  rw [reducedMerge1848Check, Integer.Sparse.eval_mergeBy, reducedTermEval1857 B hB hF, reducedTermEval1858 B hB hF]
  rw [originalMerge1848, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1849 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1849 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1849 (originalVector B) := by
  rw [reducedMerge1849Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1847 B hB hF, reducedMergeEval1848 B hB hF]
  rw [originalMerge1849, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1850 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1850 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1850 (originalVector B) := by
  rw [reducedMerge1850Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1846 B hB hF, reducedMergeEval1849 B hB hF]
  rw [originalMerge1850, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1851 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1851 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1851 (originalVector B) := by
  rw [reducedMerge1851Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1843 B hB hF, reducedMergeEval1850 B hB hF]
  rw [originalMerge1851, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1852 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1852 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1852 (originalVector B) := by
  rw [reducedMerge1852Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1837 B hB hF, reducedMergeEval1851 B hB hF]
  rw [originalMerge1852, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1853 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1853 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1853 (originalVector B) := by
  rw [reducedMerge1853Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1823 B hB hF, reducedMergeEval1852 B hB hF]
  rw [originalMerge1853, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1913 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1913 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1913 (originalVector B) := by
  rw [reducedMerge1913Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1853 B hB hF, reducedMergeEval1912_e B hB hF]
  rw [originalMerge1913, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1914 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1914 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1914 (originalVector B) := by
  rw [reducedMerge1914Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1794_e B hB hF, reducedMergeEval1913 B hB hF]
  rw [originalMerge1914, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1915 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1915 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1915 (originalVector B) := by
  rw [reducedMerge1915Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1675_e B hB hF, reducedMergeEval1914 B hB hF]
  rw [originalMerge1915, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1916 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1916 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1916 (originalVector B) := by
  rw [reducedMerge1916Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1436_e B hB hF, reducedMergeEval1915 B hB hF]
  rw [originalMerge1916, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1917 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1917 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1917 (originalVector B) := by
  rw [reducedMerge1917Check, Integer.Sparse.eval_mergeBy, reducedMergeEval957_e B hB hF, reducedMergeEval1916 B hB hF]
  rw [originalMerge1917, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionFinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem originalReductionEval_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Combination.eval MixedData.targetRows (numericVector B) MixedData.rawCombination =
      (37623398400 : ℝ) * Integer.Sparse.eval originalPolynomial (originalVector B) := by
  rw [← numericReductionEval, reducedMergeEval1917 B hB hF, originalReductionCheck]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.originalReductionEval_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.originalReductionEval_e_oai
