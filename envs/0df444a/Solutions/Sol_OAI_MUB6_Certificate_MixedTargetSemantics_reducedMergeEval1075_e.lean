-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1075_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:08:08.038128+00:00
-- url     : https://prove2.me/submissions/265f0eea-0887-4e6a-8784-f9e44a579635

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E130
import Definitions.Def_OAIQ106E137
import Definitions.Def_OAIQ106E138
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E142
import Definitions.Def_OAIQ106E143
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E171

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

theorem IsHadamard.column_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, conj (H k i) * H k j = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.2
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem IsHadamard.row_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, H i k * conj (H j k) = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.row_gram
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem IsHadamard.transpose {H : CMatrix} (hH : IsHadamard H) :
    IsHadamard H.transpose := by
  refine ⟨fun i j => hH.1 j i, ?_⟩
  ext i j
  simpa [Matrix.mul_apply, Matrix.one_apply, mul_comm, eq_comm] using
    hH.row_orthogonal j i

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

theorem transition_reverse (b c : Basis) :
    transition c b = (transition b c).conjTranspose := by
  ext i j
  simp [transition, Matrix.conjTranspose_apply]

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

theorem average_prod (f : ι × κ → ℝ) :
    average f = average (fun i => average (fun k => f (i, k))) := by
  simp only [average, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, ← Finset.mul_sum]
  ring

theorem average_comm (f : ι → κ → ℝ) :
    average (fun i => average (fun k => f i k)) =
      average (fun k => average (fun i => f i k)) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

theorem sum_eq_card_mul_average (f : ι → ℝ) :
    (∑ i, f i) = (Fintype.card ι : ℝ) * average f := by
  classical
  by_cases hc : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    simp [average]
  · have hcr : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hc
    simp only [average, ← mul_assoc, mul_inv_cancel₀ hcr, one_mul]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_MomentSymmetry
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem injectiveMoment_iterated {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    injectiveMoment H A = average (fun ρ : Fin p ↪ Coord =>
      average (fun κ : Fin q ↪ Coord =>
        ((exponentMonomial H A ρ κ).re +
          (exponentMonomial H.transpose A ρ κ).re) / 2)) :=
  average_prod _

theorem injectiveMoment_reverse_iterated {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    (average (fun κ : Fin q ↪ Coord => average (fun ρ : Fin p ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2))) = injectiveMoment H A := by
  rw [average_comm]
  exact (injectiveMoment_iterated H A).symm

theorem exponentMonomial_transpose {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H A.transpose κ ρ = exponentMonomial H.transpose A ρ κ := by
  exact Finset.prod_comm

theorem injectiveMoment_transpose {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    injectiveMoment H A.transpose = injectiveMoment H A := by
  rw [injectiveMoment_iterated, injectiveMoment_iterated, average_comm]
  apply average_congr
  intro ρ
  apply average_congr
  intro κ
  rw [exponentMonomial_transpose, exponentMonomial_transpose]
  simp only [Matrix.transpose_transpose, add_comm]

theorem exponentMonomial_neg {p q : ℕ} (H : CMatrix)
    (hH : ∀ i j, Complex.normSq (H i j) = 1)
    (A : Matrix (Fin p) (Fin q) ℤ) (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H (-A) ρ κ = conj (exponentMonomial H A ρ κ) := by
  simp only [exponentMonomial, Matrix.neg_apply, zpow_neg, map_prod, map_zpow₀]
  apply Finset.prod_congr rfl
  intro u _
  apply Finset.prod_congr rfl
  intro v _
  rw [← unit_inv_eq_conj (hH (ρ u) (κ v)), inv_zpow]

theorem injectiveMoment_neg {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin p) (Fin q) ℤ) : injectiveMoment H (-A) = injectiveMoment H A := by
  apply average_congr
  intro s
  rw [exponentMonomial_neg H hH.1, exponentMonomial_neg H.transpose hH.transpose.1]
  simp

theorem exponentMonomial_row_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin p))
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H (fun i j => A (σ i) j) ρ κ =
      exponentMonomial H A (Equiv.embeddingCongr σ (Equiv.refl Coord) ρ) κ := by
  unfold exponentMonomial
  simpa only [Equiv.embeddingCongr_apply, Function.Embedding.congr_apply,
    Function.comp_apply, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.refl_apply, Equiv.symm_apply_apply] using
    Equiv.prod_comp σ (fun i => ∏ j, H (ρ (σ.symm i)) (κ j) ^ A i j)

theorem injectiveMoment_row_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin p)) :
    injectiveMoment H (fun i j => A (σ i) j) = injectiveMoment H A := by
  rw [injectiveMoment_iterated H (fun i j => A (σ i) j), injectiveMoment_iterated H A]
  simp_rw [exponentMonomial_row_permutation H A σ,
    exponentMonomial_row_permutation H.transpose A σ]
  exact average_equiv (Equiv.embeddingCongr σ (Equiv.refl Coord))
    (fun ρ : Fin p ↪ Coord => average (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2))

theorem injectiveMoment_column_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin q)) :
    injectiveMoment H (fun i j => A i (σ j)) = injectiveMoment H A := by
  rw [← injectiveMoment_transpose H (fun i j => A i (σ j))]
  change injectiveMoment H (fun i j => A.transpose (σ i) j) = _
  rw [injectiveMoment_row_permutation, injectiveMoment_transpose]

theorem exponentMonomial_zero_first_row {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (hA : ∀ j, A 0 j = 0)
    (ρ : Fin (p + 1) ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H A ρ κ =
      exponentMonomial H (fun i j => A i.succ j) (Sampling.dropFirst ρ) κ := by
  simp only [exponentMonomial, Fin.prod_univ_succ, hA, zpow_zero,
    Finset.prod_const_one, one_mul]
  rfl

theorem injectiveMoment_zero_first_row {p q : ℕ} (hp : p < 6) (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (hA : ∀ j, A 0 j = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A i.succ j) := by
  rw [injectiveMoment_iterated H A,
    injectiveMoment_iterated H (fun i j => A i.succ j)]
  simp_rw [exponentMonomial_zero_first_row H A hA,
    exponentMonomial_zero_first_row H.transpose A hA]
  exact Sampling.average_dropFirst hp
    (fun ρ : Fin p ↪ Coord => average (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H (fun i j => A i.succ j) ρ κ).re +
        (exponentMonomial H.transpose (fun i j => A i.succ j) ρ κ).re) / 2))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Canonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small semantic steps used by the generated canonicalization traces. Each
step preserves the actual averaged injective moment. The finite side conditions
(state dimensions, permutation inverses, and zero entries) are checked separately.
-/
noncomputable section
namespace MUB6.Certificate

/-- Move a zero row to the front and delete it. -/
theorem moment_delete_zero_row {p q : ℕ} (hp : p < 6) (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (σ : Equiv.Perm (Fin (p + 1)))
    (hzero : ∀ j, A (σ 0) j = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i.succ) j) := by
  calc
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) j) :=
      (injectiveMoment_row_permutation H A σ).symm
    _ = injectiveMoment H (fun i j => A (σ i.succ) j) :=
      injectiveMoment_zero_first_row hp H _ hzero

/-- The column version uses the transpose symmetry already present in the
manuscript's normalization. -/
theorem moment_delete_zero_column {p q : ℕ} (hq : q < 6) (H : CMatrix)
    (A : Matrix (Fin p) (Fin (q + 1)) ℤ) (σ : Equiv.Perm (Fin (q + 1)))
    (hzero : ∀ i, A i (σ 0) = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A i (σ j.succ)) := by
  calc
    injectiveMoment H A = injectiveMoment H A.transpose :=
      (injectiveMoment_transpose H A).symm
    _ = injectiveMoment H (fun i j => A.transpose (σ i.succ) j) :=
      moment_delete_zero_row hq H A.transpose σ hzero
    _ = injectiveMoment H (fun i j => A i (σ j.succ)) :=
      injectiveMoment_transpose H (fun i j => A i (σ j.succ))

/-- Simultaneous row and column relabeling. -/
theorem moment_permute {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ)
    (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) :
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) (τ j)) := by
  calc
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) j) :=
      (injectiveMoment_row_permutation H A σ).symm
    _ = injectiveMoment H (fun i j => A (σ i) (τ j)) :=
      (injectiveMoment_column_permutation H (fun i j => A (σ i) j) τ).symm

end MUB6.Certificate

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

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Interpretation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reindexing and averaging preserve the interpretation of sparse forms.
These algebraic facts connect finite checked coefficients to actual moments. -/
namespace MUB6.Certificate

namespace Sparse

variable {ι κ Ω : Type*}

theorem eval_average [Fintype Ω] (v : Sparse ι) (x : Ω → ι → ℝ) :
    eval v (fun i => average (fun ω => x ω i)) =
      average (fun ω => eval v (x ω)) := by
  induction v with
  | nil => simp
  | cons p v ih =>
    simp only [eval_cons, average_add, average_mul, ih]

end Sparse

end MUB6.Certificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_PartitionExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MUB6

theorem prod_zpow_eq_zpow_sum {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    {z : ℂ} (hz : z ≠ 0) : (∏ i ∈ s, z ^ a i) = z ^ (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hz]

theorem product_grouped {n k : ℕ} (label : Fin n → Fin k)
    (x : Fin k → ℂ) (hx : ∀ b, x b ≠ 0) (a : Fin n → ℤ) :
    (∏ j, x (label j) ^ a j) = ∏ b, x b ^ (∑ j with label j = b, a j) := by
  rw [← Finset.prod_fiberwise Finset.univ label]
  apply Finset.prod_congr rfl
  intro b _
  rw [← prod_zpow_eq_zpow_sum _ a (hx b)]
  apply Finset.prod_congr rfl
  intro j hj
  rw [(Finset.mem_filter.mp hj).2]

theorem rawMonomial_grouped {p n k : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin k)
    (ρ : Fin p ↪ Coord) (κ : Fin k ↪ Coord) :
    rawMonomial H A ρ (fun j => κ (label j)) =
      exponentMonomial H (groupedColumns A label) ρ κ := by
  unfold rawMonomial exponentMonomial groupedColumns
  apply Finset.prod_congr rfl
  intro i _
  exact product_grouped label (fun b => H (ρ i) (κ b))
    (fun b => unit_ne_zero (hH.1 _ _)) (fun j => A i j)

theorem rowFourier_product_expand {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) (ρ : Fin p ↪ Coord) :
    (∏ j, rowFourier H ρ (fun i => A i j)) =
      (6 : ℂ)⁻¹ ^ n * ∑ κ : Fin n → Coord, rawMonomial H A ρ κ := by
  simp only [rowFourier, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [Fintype.prod_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro κ _
  exact Finset.prod_comm

/-- The unnormalized equality-partition identity. The factor `(6)_k` in
the manuscript is exactly the cardinality of the inner injection type. -/
theorem rowFourier_partition_expand {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (ρ : Fin p ↪ Coord) (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    (∏ j, rowFourier H ρ (fun i => A i j)) =
      (6 : ℂ)⁻¹ ^ n * ∑ s, ∑ κ : Fin (F.blocks s) ↪ Coord,
        exponentMonomial H (groupedColumns A (F.label s)) ρ κ := by
  rw [rowFourier_product_expand]
  have hs := (F.assignmentsEquiv cover).sum_comp
    (fun κ : Fin n → Coord => rawMonomial H A ρ κ)
  change (∑ s : Σ s, Fin (F.blocks s) ↪ Coord,
    rawMonomial H A ρ (fun i => s.2 (F.label s.1 i))) = _ at hs
  rw [Fintype.sum_sigma] at hs
  rw [← hs]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro κ _
  exact rawMonomial_grouped hH A (F.label s) ρ κ

end MUB6

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_SmallPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.EqualityPatterns

theorem pattern3_0 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 = f 0)
    (_h20 : f 2 = f 0)
    (h21 : f 2 = f 1)
    : ∀ i j, family3.label 0 i = family3.label 0 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_1 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 = f 0)
    (h20 : f 2 ≠ f 0)
    (_h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 1 i = family3.label 1 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_2 {B : Type*} (f : Fin 3 → B)
    (_h10 : f 1 ≠ f 0)
    (h20 : f 2 = f 0)
    (h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 2 i = family3.label 2 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_3 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 ≠ f 0)
    (_h20 : f 2 ≠ f 0)
    (h21 : f 2 = f 1)
    : ∀ i j, family3.label 3 i = family3.label 3 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_4 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 ≠ f 0)
    (h20 : f 2 ≠ f 0)
    (h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 4 i = family3.label 4 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm] <;> grind

theorem covers3 {B : Type*} (f : Fin 3 → B) :
    ∃ p, ∀ i j, (family3.label p i = family3.label p j ↔ f i = f j) := by
  classical
  by_cases h10 : f 1 = f 0
  ·
    by_cases h20 : f 2 = f 0
    ·
      refine ⟨0, ?_⟩
      apply pattern3_0 f <;> simp_all [eq_comm]
    ·
      refine ⟨1, ?_⟩
      apply pattern3_1 f <;> simp_all [eq_comm]
  ·
    by_cases h20 : f 2 = f 0
    ·
      refine ⟨2, ?_⟩
      apply pattern3_2 f <;> simp_all [eq_comm]
    ·
      by_cases h21 : f 2 = f 1
      ·
        refine ⟨3, ?_⟩
        apply pattern3_3 f <;> simp_all [eq_comm]
      ·
        refine ⟨4, ?_⟩
        apply pattern3_4 f <;> simp_all [eq_comm]

end MUB6.EqualityPatterns

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_NormalizedPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MUB6

theorem inverse_six_pow_real (n : ℕ) :
    (6 : ℂ)⁻¹ ^ n = (((6 : ℝ)⁻¹ ^ n : ℝ) : ℂ) := by
  simp

theorem partition_integrand {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (ρ : Fin p ↪ Coord) (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    ((∏ j, rowFourier H ρ (fun i => A i j)).re +
      (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re) / 2 =
      (6 : ℝ)⁻¹ ^ n * ∑ s, ∑ κ : Fin (F.blocks s) ↪ Coord,
        ((exponentMonomial H (groupedColumns A (F.label s)) ρ κ).re +
          (exponentMonomial H.transpose (groupedColumns A (F.label s)) ρ κ).re) / 2 := by
  rw [rowFourier_partition_expand hH A ρ F cover,
    rowFourier_partition_expand hH.transpose A ρ F cover, inverse_six_pow_real]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.re_sum, div_eq_mul_inv, ← Finset.sum_mul,
    Finset.sum_add_distrib]
  ring

theorem average_injection_sum {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    average (fun ρ : Fin p ↪ Coord => ∑ κ : Fin q ↪ Coord,
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2) =
      (Fintype.card (Fin q ↪ Coord) : ℝ) * injectiveMoment H A := by
  have he (ρ : Fin p ↪ Coord) := sum_eq_card_mul_average
    (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2)
  simp_rw [he]
  rw [average_mul, ← injectiveMoment_iterated H A]

/-- The normalized equality-pattern expansion. For k blocks the coefficient
is `card (Fin k ↪ Fin 6) / 6^n`, exactly `(6)_k / 6^n` in the source. -/
theorem averagedRowProducts_partition {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    averagedRowProducts H A =
      ∑ s, ((Fintype.card (Fin (F.blocks s) ↪ Coord) : ℝ) / 6 ^ n) *
        injectiveMoment H (groupedColumns A (F.label s)) := by
  unfold averagedRowProducts
  simp_rw [partition_integrand hH A _ F cover]
  rw [average_mul, average_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [average_injection_sum H (groupedColumns A (F.label s))]
  simp only [div_eq_mul_inv, inv_pow]
  ring

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_OrderedPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem familyAverage_add (B : Fin 7 → Basis) (F G : CMatrix → ℝ) :
    familyAverage B (fun H => F H + G H) = familyAverage B F + familyAverage B G := by
  simp only [familyAverage, average_add]

theorem familyAverage_mul (B : Fin 7 → Basis) (c : ℝ) (F : CMatrix → ℝ) :
    familyAverage B (fun H => c * F H) = c * familyAverage B F := by
  simp only [familyAverage, average_mul]

theorem relativeMatrix_reverse (B : Fin 7 → Basis) (p : Fin 7 × Coord) :
    relativeMatrix B (reversePair p).1 (reversePair p).2 =
      (relativeMatrix B p.1 p.2).conjTranspose := by
  simp only [relativeMatrix, reversePair, Fin.succAbove_succAbove_predAbove]
  exact transition_reverse _ _

theorem familyAverage_transpose (B : Fin 7 → Basis) (F : CMatrix → ℝ)
    (hF : ∀ H, F (fun i j => conj (H i j)) = F H) :
    familyAverage B (fun H => F H.transpose) = familyAverage B F := by
  change (average (fun r : Fin 7 => average (fun s : Coord => F ((relativeMatrix B r s).transpose)))) =
    average (fun r : Fin 7 => average (fun s : Coord => F (relativeMatrix B r s)))
  rw [← average_prod (fun p : Fin 7 × Coord => F ((relativeMatrix B p.1 p.2).transpose)),
    ← average_prod (fun p : Fin 7 × Coord => F (relativeMatrix B p.1 p.2))]
  have h (p : Fin 7 × Coord) :
      F ((relativeMatrix B p.1 p.2).transpose) =
        F (relativeMatrix B (reversePair p).1 (reversePair p).2) := by
    rw [relativeMatrix_reverse]
    exact (hF ((relativeMatrix B p.1 p.2).transpose)).symm
  simp_rw [h]
  exact average_equiv reversePairEquiv (fun p => F (relativeMatrix B p.1 p.2))

theorem rowFourier_conjugate {p : ℕ} (H : CMatrix) (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    rowFourier (fun i j => conj (H i j)) ρ a = conj (rowFourier H ρ a) := by
  simp only [rowFourier, map_mul, map_sum, map_prod, map_zpow₀, map_inv₀, map_ofNat]

theorem unorientedRowProducts_conjugate {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    unorientedRowProducts (fun i j => conj (H i j)) A = unorientedRowProducts H A := by
  apply average_congr
  intro ρ
  simp only [rowFourier_conjugate, ← map_prod, Complex.conj_re]

theorem averagedRowProducts_split {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    averagedRowProducts H A =
      (1 / 2 : ℝ) * unorientedRowProducts H A +
        (1 / 2 : ℝ) * unorientedRowProducts H.transpose A := by
  have h (ρ : Fin p ↪ Coord) :
      ((∏ j, rowFourier H ρ (fun i => A i j)).re +
        (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re) / 2 =
      (1 / 2 : ℝ) * (∏ j, rowFourier H ρ (fun i => A i j)).re +
        (1 / 2 : ℝ) * (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re := by ring
  simp only [averagedRowProducts, h, average_add, average_mul, unorientedRowProducts]

theorem familyAverage_averagedRowProducts {p n : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    familyAverage B (fun H => averagedRowProducts H A) =
      familyAverage B (fun H => unorientedRowProducts H A) := by
  simp only [averagedRowProducts_split, familyAverage_add, familyAverage_mul]
  rw [familyAverage_transpose B (fun H => unorientedRowProducts H A)
    (fun H => unorientedRowProducts_conjugate H A)]
  ring

theorem mixedMoment_single_label {p n : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      familyAverage B (fun H => unorientedRowProducts H A) := by
  apply average_congr
  intro r
  have h (ρ : Fin p ↪ Coord) :
      average (fun τ : Fin 1 ↪ Coord =>
        (mixedIntegrand B A (fun _ => (0 : Fin 1)) r ρ τ).re) =
      average (fun s : Coord => (∏ j, rowFourier (relativeMatrix B r s) ρ (fun i => A i j)).re) := by
    exact average_equiv singletonEmbeddingEquiv
      (fun s => (∏ j, rowFourier (relativeMatrix B r s) ρ (fun i => A i j)).re)
  simp_rw [h]
  exact average_comm _

/-- Single-label mixed moments expand into the manuscript's transpose-averaged
pair moments with the exact falling-factorial weights. -/
theorem mixedMoment_single_label_partition {p n : ℕ} {P : Type*} [Fintype P]
    (B : Fin 7 → Basis) (hB : IsMUBFamily B) (A : Matrix (Fin p) (Fin n) ℤ)
    (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      ∑ s, ((Fintype.card (Fin (F.blocks s) ↪ Coord) : ℝ) / 6 ^ n) *
        familyPairMoment B (groupedColumns A (F.label s)) := by
  rw [mixedMoment_single_label, ← familyAverage_averagedRowProducts]
  unfold familyAverage
  simp_rw [averagedRowProducts_partition (relativeMatrix_isHadamard B hB _ _) A F cover,
    average_sum, average_mul]
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw264 raw264Labels = mixedMoment B node2753 node2753Labels := by
  calc
    mixedMoment B raw264 raw264Labels = mixedMoment B raw264step0 raw264step0Labels := by
      have ha : raw264step0 = (fun i j => raw264 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw264step0 raw264; decide +kernel
      have hl : raw264step0Labels = raw264Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw264 raw264Labels permutation32 permutation5
    mixedMoment B raw264step0 raw264step0Labels = mixedMoment B raw264step1 raw264step1Labels := by
      have ha : raw264step1 = raw264step0 := by apply Matrix.ext; unfold raw264step1 raw264step0; decide +kernel
      have hl : raw264step0Labels = labelEmbedding1 ∘ raw264step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw264step0 raw264step0Labels raw264step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2753 node2753Labels := by rfl

theorem canonical265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw265 raw265Labels = mixedMoment B node397 node397Labels := by
  calc
    mixedMoment B raw265 raw265Labels = mixedMoment B raw265step0 raw265step0Labels := by
      have ha : raw265step0 = (fun i j => raw265 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw265step0 raw265; decide +kernel
      have hl : raw265step0Labels = raw265Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw265 raw265Labels permutation32 permutation5
    _ = mixedMoment B node397 node397Labels := by rfl

theorem canonical266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw266 raw266Labels = mixedMoment B node2755 node2755Labels := by
  calc
    mixedMoment B raw266 raw266Labels = mixedMoment B raw266step0 raw266step0Labels := by
      have ha : raw266step0 = (fun i j => raw266 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw266step0 raw266; decide +kernel
      have hl : raw266step0Labels = raw266Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw266 raw266Labels permutation8 permutation5
    mixedMoment B raw266step0 raw266step0Labels = mixedMoment B raw266step1 raw266step1Labels := by
      have ha : raw266step1 = raw266step0 := by apply Matrix.ext; unfold raw266step1 raw266step0; decide +kernel
      have hl : raw266step0Labels = labelEmbedding1 ∘ raw266step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw266step0 raw266step0Labels raw266step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2755 node2755Labels := by rfl

theorem canonical267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw267 raw267Labels = mixedMoment B node262 node262Labels := by
  calc
    mixedMoment B raw267 raw267Labels = mixedMoment B raw267step0 raw267step0Labels := by
      have ha : raw267step0 = (fun i j => raw267 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw267step0 raw267; decide +kernel
      have hl : raw267step0Labels = raw267Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw267 raw267Labels permutation29 permutation4
    mixedMoment B raw267step0 raw267step0Labels = mixedMoment B raw267step1 raw267step1Labels := by
      have ha : raw267step1 = -raw267step0 := by apply Matrix.ext; change ∀ i j, raw267step1 i j = -(raw267step0 i j); unfold raw267step1 raw267step0; decide +kernel
      have hl : raw267step1Labels = raw267step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node262 node262Labels := by rfl

theorem canonical276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw276 raw276Labels = mixedMoment B node2775 node2775Labels := by
  calc
    mixedMoment B raw276 raw276Labels = mixedMoment B raw276step0 raw276step0Labels := by
      have ha : raw276step0 = (fun i j => raw276 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw276step0 raw276; decide +kernel
      have hl : raw276step0Labels = raw276Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw276 raw276Labels permutation32 permutation5
    mixedMoment B raw276step0 raw276step0Labels = mixedMoment B raw276step1 raw276step1Labels := by
      have ha : raw276step1 = raw276step0 := by apply Matrix.ext; unfold raw276step1 raw276step0; decide +kernel
      have hl : raw276step0Labels = labelEmbedding1 ∘ raw276step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw276step0 raw276step0Labels raw276step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2775 node2775Labels := by rfl

theorem canonical277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw277 raw277Labels = mixedMoment B node411 node411Labels := by
  calc
    mixedMoment B raw277 raw277Labels = mixedMoment B raw277step0 raw277step0Labels := by
      have ha : raw277step0 = (fun i j => raw277 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw277step0 raw277; decide +kernel
      have hl : raw277step0Labels = raw277Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw277 raw277Labels permutation32 permutation5
    _ = mixedMoment B node411 node411Labels := by rfl

theorem canonical278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw278 raw278Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw278 raw278Labels = mixedMoment B raw278step0 raw278step0Labels := by
      have ha : raw278step0 = (fun i j => raw278 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw278step0 raw278; decide +kernel
      have hl : raw278step0Labels = raw278Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw278 raw278Labels permutation8 permutation5
    mixedMoment B raw278step0 raw278step0Labels = mixedMoment B raw278step1 raw278step1Labels := by
      have ha : raw278step1 = raw278step0 := by apply Matrix.ext; unfold raw278step1 raw278step0; decide +kernel
      have hl : raw278step0Labels = labelEmbedding1 ∘ raw278step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw278step0 raw278step0Labels raw278step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2776 node2776Labels := by rfl

theorem canonical279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw279 raw279Labels = mixedMoment B node412 node412Labels := by
  calc
    mixedMoment B raw279 raw279Labels = mixedMoment B raw279step0 raw279step0Labels := by
      have ha : raw279step0 = (fun i j => raw279 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw279step0 raw279; decide +kernel
      have hl : raw279step0Labels = raw279Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw279 raw279Labels permutation8 permutation5
    _ = mixedMoment B node412 node412Labels := by rfl

theorem canonical280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw280 raw280Labels = mixedMoment B node2778 node2778Labels := by
  calc
    mixedMoment B raw280 raw280Labels = mixedMoment B raw280step0 raw280step0Labels := by
      have ha : raw280step0 = (fun i j => raw280 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw280step0 raw280; decide +kernel
      have hl : raw280step0Labels = raw280Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw280 raw280Labels permutation2 permutation5
    mixedMoment B raw280step0 raw280step0Labels = mixedMoment B raw280step1 raw280step1Labels := by
      have ha : raw280step1 = raw280step0 := by apply Matrix.ext; unfold raw280step1 raw280step0; decide +kernel
      have hl : raw280step0Labels = labelEmbedding1 ∘ raw280step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw280step0 raw280step0Labels raw280step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2778 node2778Labels := by rfl

theorem canonical281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw281 raw281Labels = mixedMoment B node270 node270Labels := by
  calc
    mixedMoment B raw281 raw281Labels = mixedMoment B raw281step0 raw281step0Labels := by
      have ha : raw281step0 = (fun i j => raw281 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw281step0 raw281; decide +kernel
      have hl : raw281step0Labels = raw281Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw281 raw281Labels permutation7 permutation4
    mixedMoment B raw281step0 raw281step0Labels = mixedMoment B raw281step1 raw281step1Labels := by
      have ha : raw281step1 = -raw281step0 := by apply Matrix.ext; change ∀ i j, raw281step1 i j = -(raw281step0 i j); unfold raw281step1 raw281step0; decide +kernel
      have hl : raw281step1Labels = raw281step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node270 node270Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_FiniteSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sum_fin_five {R : Type*} [AddCommMonoid R] (f : Fin 5 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + f 4))) = _
  ac_rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_GroupedColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit grouping formulas for the two- and three-column equality
patterns. These discharge the dependent finite-label calculations once,
so concrete certificate rows need only ordinary integer arithmetic. -/

open scoped BigOperators
namespace MUB6

theorem groupedColumns_family3_0 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 0) =
      (fun i (_ : Fin 1) => A i 0 + A i 1 + A i 2) := by
  change groupedColumns A (fun _ : Fin 3 => (0 : Fin 1)) = _
  ext i b
  have hb : b = 0 := Subsingleton.elim _ _
  subst b
  simp [groupedColumns, Fin.sum_univ_succ, add_assoc]

theorem groupedColumns_family3_1 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 1) =
      (fun i => ![A i 0 + A i 1, A i 2]) := by
  change groupedColumns A (![0, 0, 1] : Fin 3 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family3_2 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 2) =
      (fun i => ![A i 0 + A i 2, A i 1]) := by
  change groupedColumns A (![0, 1, 0] : Fin 3 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family3_3 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 3) =
      (fun i => ![A i 0, A i 1 + A i 2]) := by
  change groupedColumns A (![0, 1, 1] : Fin 3 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family3_4 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 4) = A := by
  change groupedColumns A (fun j : Fin 3 => j) = _
  ext i b
  simp [groupedColumns, Finset.sum_filter]

end MUB6

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_PairAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6.Certificate.MixedSemantics

theorem eval_familyPairVector (B : Fin 7 → Basis) (v : Sparse (Fin 909)) :
    Sparse.eval v (familyPairVector B) =
      familyAverage B (fun H => Sparse.eval v (PairSemantics.momentVector H)) := by
  unfold familyPairVector familyAverage
  rw [Sparse.eval_average]
  apply average_congr
  intro r
  exact Sparse.eval_average v _

theorem familyPairMoment_of_pointwise {p n : ℕ} (B : Fin 7 → Basis)
    (hB : IsMUBFamily B) (A : Matrix (Fin p) (Fin n) ℤ) (v : Sparse (Fin 909))
    (h : ∀ H, IsHadamard H →
      injectiveMoment H A = Sparse.eval v (PairSemantics.momentVector H)) :
    familyPairMoment B A = Sparse.eval v (familyPairVector B) := by
  rw [eval_familyPairVector]
  unfold familyPairMoment familyAverage
  apply average_congr
  intro r
  apply average_congr
  intro s
  exact h _ (relativeMatrix_isHadamard B hB r s)

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleRules
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

/-- The five equality patterns for three sampled column indices. -/
theorem single_label_three {p : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (A : Matrix (Fin p) (Fin 3) ℤ) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      (1 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 0)) +
      (5 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 1)) +
      (5 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 2)) +
      (5 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 3)) +
      (5 / 9 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 4)) := by
  have h := mixedMoment_single_label_partition B hB A
    EqualityPatterns.family3 EqualityPatterns.covers3
  rw [sum_fin_five] at h
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family3,
    EqualityPatterns.blocks3, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Nat.descFactorial] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical522 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw522 = injectiveMoment H node188 := by
  calc
    injectiveMoment H raw522 = injectiveMoment H raw522step0 := by
      have heq : raw522step0 = (fun i j => raw522 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw522 permutation27 permutation6
    _ = injectiveMoment H node188 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7977 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7977 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw7977 = injectiveMoment H raw7977step0 := by
      have heq : raw7977step0 = raw7977.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7977).symm
    injectiveMoment H raw7977step0 = injectiveMoment H raw7977step1 := by
      have heq : raw7977step1 = (fun i j => raw7977step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7977step0 permutation5 permutation2
    _ = injectiveMoment H node10 := by rfl

theorem canonical7979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7979 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7979 = injectiveMoment H raw7979step0 := by
      have hz : ∀ j, raw7979 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7979step0 = (fun i j => raw7979 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979 permutation7 hz
    injectiveMoment H raw7979step0 = injectiveMoment H raw7979step1 := by
      have hz : ∀ j, raw7979step0 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7979step1 = (fun i j => raw7979step0 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979step0 permutation2 hz
    injectiveMoment H raw7979step1 = injectiveMoment H raw7979step2 := by
      have hz : ∀ j, raw7979step1 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7979step2 = (fun i j => raw7979step1 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979step1 permutation0 hz
    injectiveMoment H raw7979step2 = injectiveMoment H raw7979step3 := by
      have hz : ∀ i, raw7979step2 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7979step3 = (fun i j => raw7979step2 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7979step2 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

theorem canonical7980 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7980 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7980 = injectiveMoment H raw7980step0 := by
      have hz : ∀ j, raw7980 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7980step0 = (fun i j => raw7980 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980 permutation27 hz
    injectiveMoment H raw7980step0 = injectiveMoment H raw7980step1 := by
      have hz : ∀ j, raw7980step0 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7980step1 = (fun i j => raw7980step0 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step0 permutation7 hz
    injectiveMoment H raw7980step1 = injectiveMoment H raw7980step2 := by
      have hz : ∀ j, raw7980step1 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7980step2 = (fun i j => raw7980step1 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step1 permutation2 hz
    injectiveMoment H raw7980step2 = injectiveMoment H raw7980step3 := by
      have hz : ∀ j, raw7980step2 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7980step3 = (fun i j => raw7980step2 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step2 permutation0 hz
    injectiveMoment H raw7980step3 = injectiveMoment H raw7980step4 := by
      have hz : ∀ i, raw7980step3 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7980step4 = (fun i j => raw7980step3 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7980step3 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

theorem canonical7981 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7981 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7981 = injectiveMoment H raw7981step0 := by
      have hz : ∀ j, raw7981 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7981step0 = (fun i j => raw7981 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981 permutation128 hz
    injectiveMoment H raw7981step0 = injectiveMoment H raw7981step1 := by
      have hz : ∀ j, raw7981step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7981step1 = (fun i j => raw7981step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step0 permutation27 hz
    injectiveMoment H raw7981step1 = injectiveMoment H raw7981step2 := by
      have hz : ∀ j, raw7981step1 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7981step2 = (fun i j => raw7981step1 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step1 permutation7 hz
    injectiveMoment H raw7981step2 = injectiveMoment H raw7981step3 := by
      have hz : ∀ j, raw7981step2 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7981step3 = (fun i j => raw7981step2 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step2 permutation2 hz
    injectiveMoment H raw7981step3 = injectiveMoment H raw7981step4 := by
      have hz : ∀ j, raw7981step3 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7981step4 = (fun i j => raw7981step3 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step3 permutation0 hz
    injectiveMoment H raw7981step4 = injectiveMoment H raw7981step5 := by
      have hz : ∀ i, raw7981step4 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7981step5 = (fun i j => raw7981step4 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7981step4 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical884 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw884 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw884 = injectiveMoment H raw884step0 := by
      have hz : ∀ j, raw884 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw884step0 = (fun i j => raw884 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw884 permutation80 hz
    injectiveMoment H raw884step0 = injectiveMoment H raw884step1 := by
      have hz : ∀ j, raw884step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw884step1 = (fun i j => raw884step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw884step0 permutation15 hz
    _ = injectiveMoment H node10 := by rfl

theorem canonical887 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw887 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw887 = injectiveMoment H raw887step0 := by
      have hz : ∀ j, raw887 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw887step0 = (fun i j => raw887 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw887 permutation21 hz
    injectiveMoment H raw887step0 = injectiveMoment H raw887step1 := by
      have hz : ∀ j, raw887step0 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw887step1 = (fun i j => raw887step0 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw887step0 permutation5 hz
    _ = injectiveMoment H node3 := by rfl

theorem canonical893 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw893 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw893 = injectiveMoment H raw893step0 := by
      have hz : ∀ j, raw893 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw893step0 = (fun i j => raw893 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw893 permutation57 hz
    _ = injectiveMoment H node26 := by rfl

theorem canonical895 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw895 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw895 = injectiveMoment H raw895step0 := by
      have hz : ∀ j, raw895 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw895step0 = (fun i j => raw895 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw895 permutation15 hz
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical279
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8946 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8946 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw8946 = injectiveMoment H raw8946step0 := by
      have hz : ∀ j, raw8946 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw8946step0 = (fun i j => raw8946 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8946 permutation0 hz
    injectiveMoment H raw8946step0 = injectiveMoment H raw8946step1 := by
      have hz : ∀ i, raw8946step0 i (permutation2 0) = 0 := by decide +kernel
      have heq : raw8946step1 = (fun i j => raw8946step0 i (permutation2 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8946step0 permutation2 hz
    injectiveMoment H raw8946step1 = injectiveMoment H raw8946step2 := by
      have hz : ∀ i, raw8946step1 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw8946step2 = (fun i j => raw8946step1 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8946step1 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical900 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw900 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw900 = injectiveMoment H raw900step0 := by
      have hz : ∀ j, raw900 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw900step0 = (fun i j => raw900 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw900 permutation5 hz
    _ = injectiveMoment H node3 := by rfl

theorem canonical914 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw914 = injectiveMoment H node26 := by
  rfl

theorem canonical917 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw917 = injectiveMoment H node10 := by
  rfl

theorem canonical924 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw924 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw924 = injectiveMoment H raw924step0 := by
      have heq : raw924step0 = (fun i j => raw924 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw924 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

theorem canonical926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw926 = injectiveMoment H node3 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical280
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8985 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8985 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8985 = injectiveMoment H raw8985step0 := by
      have hz : ∀ j, raw8985 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw8985step0 = (fun i j => raw8985 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8985 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical281
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9013 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9013 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9013 = injectiveMoment H raw9013step0 := by
      have hz : ∀ j, raw9013 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9013step0 = (fun i j => raw9013 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9013 permutation9 hz
    injectiveMoment H raw9013step0 = injectiveMoment H raw9013step1 := by
      have heq : raw9013step1 = (fun i j => raw9013step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9013step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_MomentContraction
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonality relations for injective moments. The saturated relation uses
only six-row moments, even though its generating exponent array has seven rows. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem rowMonomial_difference {q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (v w : Fin q) (t : Coord) (κ : Fin q ↪ Coord) :
    rowMonomial H (Pi.single v 1 - Pi.single w 1) t κ =
      H t (κ v) * conj (H t (κ w)) := by
  classical
  simp only [rowMonomial, Pi.sub_apply, zpow_sub₀ (unit_ne_zero (hH.1 _ _)),
    Finset.prod_div_distrib]
  have hv : (∏ j, H t (κ j) ^ ((Pi.single v 1 : Fin q → ℤ) j)) = H t (κ v) := by
    simp [Pi.single_apply]
  have hw : (∏ j, H t (κ j) ^ ((Pi.single w 1 : Fin q → ℤ) j)) = H t (κ w) := by
    simp [Pi.single_apply]
  rw [hv, hw, div_eq_mul_inv, unit_inv_eq_conj (hH.1 _ _)]

theorem rowMonomial_sum_zero {q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (v w : Fin q) (hvw : v ≠ w) (κ : Fin q ↪ Coord) :
    (∑ t, rowMonomial H (Pi.single v 1 - Pi.single w 1) t κ) = 0 := by
  simp_rw [rowMonomial_difference hH]
  have hkwv : κ w ≠ κ v := fun h => hvw (κ.injective h.symm)
  simpa only [hkwv, ite_false, if_false, mul_comm] using hH.column_orthogonal (κ w) (κ v)

theorem contractionMonomial_sum_zero {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    (∑ t, contractionMonomial H A ρ κ t) = 0 := by
  simp only [contractionMonomial, hA, ← Finset.mul_sum, rowMonomial_sum_zero hH v w hvw,
    mul_zero]

theorem contractionMonomial_new {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ)
    (ρ : Fin (p + 1) ↪ Coord) (κ : Fin q ↪ Coord) :
    contractionMonomial H A (Sampling.dropFirst ρ) κ (ρ 0) =
      exponentMonomial H A ρ κ := by
  simp only [contractionMonomial, exponentMonomial, rowMonomial, Fin.prod_univ_succ,
    Sampling.dropFirst_apply]
  exact mul_comm _ _

theorem contractionMonomial_occupied {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) (j : Fin p) :
    contractionMonomial H A ρ κ (ρ j) = exponentMonomial H (mergeFirst A j) ρ κ := by
  classical
  simp only [contractionMonomial, exponentMonomial, mergeFirst,
    zpow_add₀ (unit_ne_zero (hH.1 _ _)), Finset.prod_mul_distrib]
  congr 1
  simp [rowMonomial]

theorem contractionIntegrand_sum_zero {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    (∑ t, contractionIntegrand H A ρ κ t) = 0 := by
  simp only [contractionIntegrand, div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
    ← Complex.re_sum, contractionMonomial_sum_zero hH A v w hvw hA,
    contractionMonomial_sum_zero hH.transpose A v w hvw hA, Complex.zero_re,
    zero_add, zero_mul]

/-- The coefficient is 6-p, where p is the number of rows other than the
contracted row. Equivalently it is 7 minus the original row count. -/
theorem injectiveMoment_first_row_contraction {p q : ℕ} (hp : p < 6)
    {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1) :
    ((6 - p : ℕ) : ℝ) * injectiveMoment H A +
      (∑ j, injectiveMoment H (mergeFirst A j)) = 0 := by
  have ht (κ : Fin q ↪ Coord) := Sampling.average_contraction hp
    (fun ρ t => contractionIntegrand H A ρ κ t)
    (fun ρ => contractionIntegrand_sum_zero hH A v w hvw hA ρ κ)
  have hav : average (fun κ : Fin q ↪ Coord =>
      ((6 - p : ℕ) : ℝ) *
        average (fun ρ : Fin (p + 1) ↪ Coord =>
          contractionIntegrand H A (Sampling.dropFirst ρ) κ (ρ 0)) +
        ∑ j : Fin p, average (fun ρ : Fin p ↪ Coord =>
          contractionIntegrand H A ρ κ (ρ j))) = 0 := by
    simp only [ht, average_zero]
  rw [average_add, average_mul, average_sum] at hav
  simp only [contractionIntegrand, contractionMonomial_new,
    contractionMonomial_occupied hH, contractionMonomial_occupied hH.transpose] at hav
  simp only [injectiveMoment_reverse_iterated] at hav
  exact hav

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5177 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5177 = injectiveMoment H node11 := by
  clear _hH
  calc
    injectiveMoment H raw5177 = injectiveMoment H raw5177step0 := by
      have hz : ∀ j, raw5177 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5177step0 = (fun i j => raw5177 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5177 permutation15 hz
    _ = injectiveMoment H node11 := by rfl

theorem canonical5183 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5183 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5183 = injectiveMoment H raw5183step0 := by
      have hz : ∀ j, raw5183 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5183step0 = (fun i j => raw5183 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5183 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5197 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw5197 = injectiveMoment H raw5197step0 := by
      have hz : ∀ j, raw5197 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5197step0 = (fun i j => raw5197 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5197 permutation21 hz
    _ = injectiveMoment H node11 := by rfl

theorem canonical5199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5199 = injectiveMoment H node11 := by
  rfl

theorem canonical5204 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5204 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw5204 = injectiveMoment H raw5204step0 := by
      have hz : ∀ j, raw5204 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5204step0 = (fun i j => raw5204 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5204 permutation27 hz
    _ = injectiveMoment H node11 := by rfl

theorem canonical5205 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5205 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw5205 = injectiveMoment H raw5205step0 := by
      have hz : ∀ j, raw5205 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw5205step0 = (fun i j => raw5205 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5205 permutation128 hz
    injectiveMoment H raw5205step0 = injectiveMoment H raw5205step1 := by
      have hz : ∀ j, raw5205step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5205step1 = (fun i j => raw5205step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5205step0 permutation27 hz
    _ = injectiveMoment H node11 := by rfl

theorem canonical5210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5210 = injectiveMoment H node4 := by
  rfl

theorem canonical5215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5215 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw5215 = injectiveMoment H raw5215step0 := by
      have hz : ∀ j, raw5215 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5215step0 = (fun i j => raw5215 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5215 permutation27 hz
    injectiveMoment H raw5215step0 = injectiveMoment H raw5215step1 := by
      have hz : ∀ j, raw5215step0 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw5215step1 = (fun i j => raw5215step0 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5215step0 permutation7 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5458 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5458 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5458 = injectiveMoment H raw5458step0 := by
      have heq : raw5458step0 = raw5458.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5458).symm
    injectiveMoment H raw5458step0 = injectiveMoment H raw5458step1 := by
      have heq : raw5458step1 = (fun i j => raw5458step0 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5458step0 permutation6 permutation2
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical187
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5990 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5990 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5990 = injectiveMoment H raw5990step0 := by
      have heq : raw5990step0 = raw5990.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5990).symm
    injectiveMoment H raw5990step0 = injectiveMoment H raw5990step1 := by
      have heq : raw5990step1 = (fun i j => raw5990step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5990step0 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical215
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6885 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6885 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw6885 = injectiveMoment H raw6885step0 := by
      have heq : raw6885step0 = raw6885.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6885).symm
    injectiveMoment H raw6885step0 = injectiveMoment H raw6885step1 := by
      have heq : raw6885step1 = (fun i j => raw6885step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6885step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical241
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7718 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7718 = injectiveMoment H node5 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical250
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8005 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8005 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw8005 = injectiveMoment H raw8005step0 := by
      have hz : ∀ i, raw8005 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8005step0 = (fun i j => raw8005 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8005 permutation3 hz
    _ = injectiveMoment H node3 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical256
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8215 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8215 = injectiveMoment H raw8215step0 := by
      have hz : ∀ i, raw8215 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8215step0 = (fun i j => raw8215 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8215 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound0
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound0 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node0 = Sparse.eval value0 (momentVector H) := by
  have hc : momentVector H 0 = injectiveMoment H node0 := rfl
  simp [value0, Sparse.eval, hc]

theorem sound3 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node3 = Sparse.eval value3 (momentVector H) := by
  have hc : momentVector H 2 = injectiveMoment H node3 := rfl
  simp [value3, Sparse.eval, hc]

theorem sound4 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node4 = Sparse.eval value4 (momentVector H) := by
  have hc : momentVector H 1 = injectiveMoment H node4 := rfl
  simp [value4, Sparse.eval, hc]

theorem sound5 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node5 = Sparse.eval value5 (momentVector H) := by
  have heq : pivotMatrix5 = (fun u v => node5 (pivotPermutation5 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node5 = injectiveMoment H pivotMatrix5 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix5 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 1 < 6) hH pivotMatrix5 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix5 (0 : Fin 1)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : mergeFirst pivotMatrix5 (0 : Fin 1) = raw8946 := by ext i j; fin_cases i; fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8946 hH).trans (sound0 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (5 : ℝ) * injectiveMoment H node5 + (injectiveMoment H (mergeFirst pivotMatrix5 (0 : Fin 1))) = 0 at hc
  rw [hm0] at hc
  norm_num [value5, value0, Sparse.eval] at hc ⊢
  linarith

theorem sound10 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node10 = Sparse.eval value10 (momentVector H) := by
  have heq : pivotMatrix10 = (fun u v => node10 (pivotPermutation10 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node10 = injectiveMoment H pivotMatrix10 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix10 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix10 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix10 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix10 (0 : Fin 2) = raw5210 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5210 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix10 (1 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix10 (1 : Fin 2) = raw926 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical926 hH).trans (sound3 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node10 + (injectiveMoment H (mergeFirst pivotMatrix10 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix10 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value10, value3, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound11 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node11 = Sparse.eval value11 (momentVector H) := by
  have heq : pivotMatrix11 = (fun u v => node11 (pivotPermutation11 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node11 = injectiveMoment H pivotMatrix11 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix11 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix11 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix11 (0 : Fin 2)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix11 (0 : Fin 2) = raw7718 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7718 hH).trans (sound5 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix11 (1 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix11 (1 : Fin 2) = raw5210 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5210 hH).trans (sound4 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node11 + (injectiveMoment H (mergeFirst pivotMatrix11 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix11 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value11, value4, value5, Sparse.eval] at hc ⊢
  linarith

theorem sound26 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node26 = Sparse.eval value26 (momentVector H) := by
  have heq : pivotMatrix26 = (fun u v => node26 (pivotPermutation26 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node26 = injectiveMoment H pivotMatrix26 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix26 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix26 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix26 (0 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix26 (0 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix26 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix26 (1 : Fin 3) = raw924 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical924 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix26 (2 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix26 (2 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node26 + (injectiveMoment H (mergeFirst pivotMatrix26 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix26 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix26 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value26, value10, value11, Sparse.eval] at hc ⊢
  linarith

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound37 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node37 = Sparse.eval value37 (momentVector H) := by
  have hc : momentVector H 13 = injectiveMoment H node37 := rfl
  simp [value37, Sparse.eval, hc]

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

theorem sound46 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node46 = Sparse.eval value46 (momentVector H) := by
  have heq : pivotMatrix46 = (fun u v => node46 (pivotPermutation46 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node46 = injectiveMoment H pivotMatrix46 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix46 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix46 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix46 (0 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (0 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix46 (1 : Fin 3)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (1 : Fin 3) = raw5183 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5183 hH).trans (sound4 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix46 (2 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (2 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node46 + (injectiveMoment H (mergeFirst pivotMatrix46 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix46 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix46 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value46, value10, value11, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound56 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node56 = Sparse.eval value56 (momentVector H) := by
  have heq : pivotMatrix56 = (fun u v => node56 (pivotPermutation56 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node56 = injectiveMoment H pivotMatrix56 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix56 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix56 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix56 (0 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix56 (0 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix56 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix56 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node56 + (injectiveMoment H (mergeFirst pivotMatrix56 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix56 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value56, value10, value11, Sparse.eval] at hc ⊢
  linarith

theorem sound57 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node57 = Sparse.eval value57 (momentVector H) := by
  have heq : pivotMatrix57 = (fun u v => node57 (pivotPermutation57 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node57 = injectiveMoment H pivotMatrix57 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix57 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix57 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix57 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix57 (0 : Fin 2) = raw8215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8215 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix57 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix57 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node57 + (injectiveMoment H (mergeFirst pivotMatrix57 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix57 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value57, value10, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound58 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node58 = Sparse.eval value58 (momentVector H) := by
  have heq : pivotMatrix58 = (fun u v => node58 (pivotPermutation58 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node58 = injectiveMoment H pivotMatrix58 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix58 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix58 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix58 (0 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix58 (0 : Fin 2) = raw8005 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8005 hH).trans (sound3 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix58 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix58 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node58 + (injectiveMoment H (mergeFirst pivotMatrix58 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix58 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value58, value10, value3, Sparse.eval] at hc ⊢
  linarith

theorem sound62 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node62 = Sparse.eval value62 (momentVector H) := by
  have heq : pivotMatrix62 = (fun u v => node62 (pivotPermutation62 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node62 = injectiveMoment H pivotMatrix62 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix62 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix62 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix62 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix62 (0 : Fin 2) = raw8215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8215 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix62 (1 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix62 (1 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node62 + (injectiveMoment H (mergeFirst pivotMatrix62 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix62 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value62, value11, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound63 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node63 = Sparse.eval value63 (momentVector H) := by
  have heq : pivotMatrix63 = (fun u v => node63.transpose (pivotPermutation63 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node63 = injectiveMoment H pivotMatrix63 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix63 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix63 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix63 (0 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix63 (0 : Fin 2) = raw5458 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5458 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix63 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix63 (1 : Fin 2) = raw7977 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7977 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node63 + (injectiveMoment H (mergeFirst pivotMatrix63 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix63 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value63, value10, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4134 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4134 = injectiveMoment H raw4134step0 := by
      have heq : raw4134step0 = (fun i j => raw4134 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4134 permutation7 permutation6
    _ = injectiveMoment H node62 := by rfl

theorem canonical4140 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4140 = injectiveMoment H node207 := by
  calc
    injectiveMoment H raw4140 = injectiveMoment H raw4140step0 := by
      have heq : raw4140step0 = (fun i j => raw4140 (permutation18 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4140 permutation18 permutation7
    _ = injectiveMoment H node207 := by rfl

theorem canonical4141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4141 = injectiveMoment H node41 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical556 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw556 = injectiveMoment H node37 := by
  calc
    injectiveMoment H raw556 = injectiveMoment H raw556step0 := by
      have heq : raw556step0 = (fun i j => raw556 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw556 permutation7 permutation6
    _ = injectiveMoment H node37 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical769 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw769 = injectiveMoment H node573 := by
  calc
    injectiveMoment H raw769 = injectiveMoment H raw769step0 := by
      have heq : raw769step0 = -raw769 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw769).symm
    injectiveMoment H raw769step0 = injectiveMoment H raw769step1 := by
      have heq : raw769step1 = (fun i j => raw769step0 (permutation49 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw769step0 permutation49 permutation8
    _ = injectiveMoment H node573 := by rfl

theorem canonical791 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw791 = injectiveMoment H node566 := by
  calc
    injectiveMoment H raw791 = injectiveMoment H raw791step0 := by
      have heq : raw791step0 = -raw791 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw791).symm
    injectiveMoment H raw791step0 = injectiveMoment H raw791step1 := by
      have heq : raw791step1 = (fun i j => raw791step0 (permutation42 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw791step0 permutation42 permutation8
    _ = injectiveMoment H node566 := by rfl

theorem canonical792 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw792 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw792 = injectiveMoment H raw792step0 := by
      have heq : raw792step0 = -raw792 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw792).symm
    injectiveMoment H raw792step0 = injectiveMoment H raw792step1 := by
      have heq : raw792step1 = (fun i j => raw792step0 (permutation12 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw792step0 permutation12 permutation8
    _ = injectiveMoment H node177 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2848 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2848 = injectiveMoment H node188 := by
  rfl

theorem canonical2849 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2849 = injectiveMoment H node37 := by
  rfl

theorem canonical2863 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2863 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2863 = injectiveMoment H raw2863step0 := by
      have heq : raw2863step0 = (fun i j => raw2863 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2863 permutation4 permutation5
    _ = injectiveMoment H node56 := by rfl

theorem canonical2864 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2864 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw2864 = injectiveMoment H raw2864step0 := by
      have heq : raw2864step0 = raw2864.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2864).symm
    injectiveMoment H raw2864step0 = injectiveMoment H raw2864step1 := by
      have heq : raw2864step1 = (fun i j => raw2864step0 (permutation6 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2864step0 permutation6 permutation7
    _ = injectiveMoment H node63 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4117 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4117 = injectiveMoment H node207 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4956 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4956 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4956 = injectiveMoment H raw4956step0 := by
      have heq : raw4956step0 = -raw4956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4956).symm
    injectiveMoment H raw4956step0 = injectiveMoment H raw4956step1 := by
      have heq : raw4956step1 = (fun i j => raw4956step0 (permutation4 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4956step0 permutation4 permutation8
    _ = injectiveMoment H node62 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2803 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2803 = injectiveMoment H node176 := by
  rfl

theorem canonical2811 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2811 = injectiveMoment H node177 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2823 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2823 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw2823 = injectiveMoment H raw2823step0 := by
      have heq : raw2823step0 = (fun i j => raw2823 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2823 permutation4 permutation5
    _ = injectiveMoment H node57 := by rfl

theorem canonical2833 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2833 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw2833 = injectiveMoment H raw2833step0 := by
      have heq : raw2833step0 = (fun i j => raw2833 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2833 permutation11 permutation3
    _ = injectiveMoment H node177 := by rfl

theorem canonical2842 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2842 = injectiveMoment H node185 := by
  rfl

theorem canonical2843 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2843 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw2843 = injectiveMoment H raw2843step0 := by
      have heq : raw2843step0 = (fun i j => raw2843 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2843 permutation10 permutation3
    _ = injectiveMoment H node185 := by rfl

theorem canonical2845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2845 = injectiveMoment H node36 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical186
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5979 = injectiveMoment H node57 := by
  rfl

theorem canonical5982 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5982 = injectiveMoment H node58 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound176 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node176 = Sparse.eval value176 (momentVector H) := by
  have heq : pivotMatrix176 = (fun u v => node176 (pivotPermutation176 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node176 = injectiveMoment H pivotMatrix176 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix176 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix176 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix176 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (0 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix176 (1 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (1 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix176 (2 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (2 : Fin 3) = raw2823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2823 hH).trans (sound57 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node176 + (injectiveMoment H (mergeFirst pivotMatrix176 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix176 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix176 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value176, value36, value57, value62, Sparse.eval] at hc ⊢
  linarith

theorem sound177 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node177 = Sparse.eval value177 (momentVector H) := by
  have heq : pivotMatrix177 = (fun u v => node177 (pivotPermutation177 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node177 = injectiveMoment H pivotMatrix177 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix177 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix177 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix177 (0 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix177 (0 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix177 (1 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix177 (1 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix177 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix177 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node177 + (injectiveMoment H (mergeFirst pivotMatrix177 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix177 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix177 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value177, value36, value37, value41, Sparse.eval] at hc ⊢
  linarith

theorem sound185 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node185 = Sparse.eval value185 (momentVector H) := by
  have heq : pivotMatrix185 = (fun u v => node185 (pivotPermutation185 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node185 = injectiveMoment H pivotMatrix185 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix185 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix185 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix185 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (0 : Fin 3) = raw5979 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix185 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (1 : Fin 3) = raw2863 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2863 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix185 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node185 + (injectiveMoment H (mergeFirst pivotMatrix185 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix185 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix185 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value185, value36, value56, value57, Sparse.eval] at hc ⊢
  linarith

theorem sound188 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node188 = Sparse.eval value188 (momentVector H) := by
  have heq : pivotMatrix188 = (fun u v => node188 (pivotPermutation188 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node188 = injectiveMoment H pivotMatrix188 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix188 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix188 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix188 (0 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix188 (0 : Fin 3) = raw5982 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5982 hH).trans (sound58 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix188 (1 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix188 (1 : Fin 3) = raw2864 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2864 hH).trans (sound63 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix188 (2 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix188 (2 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node188 + (injectiveMoment H (mergeFirst pivotMatrix188 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix188 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix188 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value188, value37, value58, value63, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical238
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7634 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7634 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7634 = injectiveMoment H raw7634step0 := by
      have heq : raw7634step0 = (fun i j => raw7634 (permutation57 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7634 permutation57 permutation1
    _ = injectiveMoment H node232 := by rfl

theorem canonical7636 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7636 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7636 = injectiveMoment H raw7636step0 := by
      have heq : raw7636step0 = (fun i j => raw7636 (permutation15 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7636 permutation15 permutation1
    _ = injectiveMoment H node46 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound3
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound207 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node207 = Sparse.eval value207 (momentVector H) := by
  have heq : pivotMatrix207 = (fun u v => node207 (pivotPermutation207 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node207 = injectiveMoment H pivotMatrix207 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix207 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix207 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix207 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix207 (0 : Fin 3) = raw4956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4956 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix207 (1 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix207 (1 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix207 (2 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix207 (2 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node207 + (injectiveMoment H (mergeFirst pivotMatrix207 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix207 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix207 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value207, value41, value62, Sparse.eval] at hc ⊢
  linarith

theorem sound232 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node232 = Sparse.eval value232 (momentVector H) := by
  have heq : pivotMatrix232 = (fun u v => node232 (pivotPermutation232 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node232 = injectiveMoment H pivotMatrix232 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix232 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix232 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix232 (0 : Fin 4)) =
      Sparse.eval value26 (momentVector H) := by
    have heq : mergeFirst pivotMatrix232 (0 : Fin 4) = raw914 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical914 hH).trans (sound26 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix232 (1 : Fin 4)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix232 (1 : Fin 4) = raw5177 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5177 hH).trans (sound11 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix232 (2 : Fin 4)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix232 (2 : Fin 4) = raw5197 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5197 hH).trans (sound11 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix232 (3 : Fin 4)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix232 (3 : Fin 4) = raw5204 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5204 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node232 + (injectiveMoment H (mergeFirst pivotMatrix232 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix232 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix232 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix232 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value232, value11, value26, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical239
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7659 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7659 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7659 = injectiveMoment H raw7659step0 := by
      have heq : raw7659step0 = (fun i j => raw7659 (permutation145 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7659 permutation145 permutation2
    _ = injectiveMoment H node232 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound8
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound566 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node566 = Sparse.eval value566 (momentVector H) := by
  have heq : pivotMatrix566 = (fun u v => node566 (pivotPermutation566 u) v) := by apply Matrix.ext; unfold pivotMatrix566 node566 pivotPermutation566; decide +kernel
  have hmoment : injectiveMoment H node566 = injectiveMoment H pivotMatrix566 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix566 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix566 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix566 (0 : Fin 4)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix566 (0 : Fin 4) = raw4117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix566 raw4117; decide +kernel
    rw [heq]
    exact (canonical4117 hH).trans (sound207 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix566 (1 : Fin 4)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix566 (1 : Fin 4) = raw2833 := by apply Matrix.ext; unfold mergeFirst pivotMatrix566 raw2833; decide +kernel
    rw [heq]
    exact (canonical2833 hH).trans (sound177 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix566 (2 : Fin 4)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix566 (2 : Fin 4) = raw2811 := by apply Matrix.ext; unfold mergeFirst pivotMatrix566 raw2811; decide +kernel
    rw [heq]
    exact (canonical2811 hH).trans (sound177 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix566 (3 : Fin 4)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix566 (3 : Fin 4) = raw2803 := by apply Matrix.ext; unfold mergeFirst pivotMatrix566 raw2803; decide +kernel
    rw [heq]
    exact (canonical2803 hH).trans (sound176 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node566 + (injectiveMoment H (mergeFirst pivotMatrix566 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix566 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix566 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix566 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value566, value176, value177, value207, Sparse.eval] at hc ⊢
  linarith

theorem sound573 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node573 = Sparse.eval value573 (momentVector H) := by
  have heq : pivotMatrix573 = (fun u v => node573 (pivotPermutation573 u) v) := by apply Matrix.ext; unfold pivotMatrix573 node573 pivotPermutation573; decide +kernel
  have hmoment : injectiveMoment H node573 = injectiveMoment H pivotMatrix573 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix573 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix573 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix573 (0 : Fin 4)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix573 (0 : Fin 4) = raw4140 := by apply Matrix.ext; unfold mergeFirst pivotMatrix573 raw4140; decide +kernel
    rw [heq]
    exact (canonical4140 hH).trans (sound207 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix573 (1 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix573 (1 : Fin 4) = raw2848 := by apply Matrix.ext; unfold mergeFirst pivotMatrix573 raw2848; decide +kernel
    rw [heq]
    exact (canonical2848 hH).trans (sound188 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix573 (2 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix573 (2 : Fin 4) = raw2843 := by apply Matrix.ext; unfold mergeFirst pivotMatrix573 raw2843; decide +kernel
    rw [heq]
    exact (canonical2843 hH).trans (sound185 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix573 (3 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix573 (3 : Fin 4) = raw2842 := by apply Matrix.ext; unfold mergeFirst pivotMatrix573 raw2842; decide +kernel
    rw [heq]
    exact (canonical2842 hH).trans (sound185 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node573 + (injectiveMoment H (mergeFirst pivotMatrix573 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix573 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix573 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix573 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value573, value185, value188, value207, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair262 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node262 node262Labels = Sparse.eval singlePairValue262 (familyPairVector B) := by
  have hp := single_label_three B hB node262
  have hl : node262Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node262 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node262 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node262 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node262 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node262 (EqualityPatterns.family3.label 1) = PairSemantics.raw914 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node262 PairSemantics.raw914
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical914 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node262 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node262 (EqualityPatterns.family3.label 2) = PairSemantics.raw9013 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node262 PairSemantics.raw9013
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9013 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node262 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node262 (EqualityPatterns.family3.label 3) = PairSemantics.raw887 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node262 PairSemantics.raw887
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical887 hH).trans (PairSemantics.sound3 hH)
  have hm4 : familyPairMoment B (groupedColumns node262 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value188 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node262 (EqualityPatterns.family3.label 4) = PairSemantics.raw522 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node262 PairSemantics.raw522
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical522 hH).trans (PairSemantics.sound188 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue262, PairSemantics.value0, PairSemantics.value3, PairSemantics.value11, PairSemantics.value26, PairSemantics.value188, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair270 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node270 node270Labels = Sparse.eval singlePairValue270 (familyPairVector B) := by
  have hp := single_label_three B hB node270
  have hl : node270Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node270 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node270 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node270 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node270 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node270 (EqualityPatterns.family3.label 1) = PairSemantics.raw924 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node270 PairSemantics.raw924; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical924 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node270 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node270 (EqualityPatterns.family3.label 2) = PairSemantics.raw8985 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node270 PairSemantics.raw8985; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8985 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node270 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node270 (EqualityPatterns.family3.label 3) = PairSemantics.raw900 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node270 PairSemantics.raw900; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical900 hH).trans (PairSemantics.sound3 hH)
  have hm4 : familyPairMoment B (groupedColumns node270 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value37 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node270 (EqualityPatterns.family3.label 4) = PairSemantics.raw556 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node270 PairSemantics.raw556; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical556 hH).trans (PairSemantics.sound37 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue270, PairSemantics.value0, PairSemantics.value3, PairSemantics.value4, PairSemantics.value10, PairSemantics.value37, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair397 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node397 node397Labels = Sparse.eval singlePairValue397 (familyPairVector B) := by
  have hp := single_label_three B hB node397
  have hl : node397Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node397 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node397 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node397 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node397 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node397 (EqualityPatterns.family3.label 1) = PairSemantics.raw5205 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node397 PairSemantics.raw5205; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5205 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node397 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node397 (EqualityPatterns.family3.label 2) = PairSemantics.raw7659 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node397 PairSemantics.raw7659; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7659 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node397 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node397 (EqualityPatterns.family3.label 3) = PairSemantics.raw884 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node397 PairSemantics.raw884; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical884 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node397 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value573 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node397 (EqualityPatterns.family3.label 4) = PairSemantics.raw769 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node397 PairSemantics.raw769; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical769 hH).trans (PairSemantics.sound573 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue397, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value232, PairSemantics.value573, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical163
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5216 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5216 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw5216 = injectiveMoment H raw5216step0 := by
      have hz : ∀ j, raw5216 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw5216step0 = (fun i j => raw5216 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5216 permutation128 hz
    injectiveMoment H raw5216step0 = injectiveMoment H raw5216step1 := by
      have hz : ∀ j, raw5216step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5216step1 = (fun i j => raw5216step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5216step0 permutation27 hz
    injectiveMoment H raw5216step1 = injectiveMoment H raw5216step2 := by
      have hz : ∀ j, raw5216step1 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw5216step2 = (fun i j => raw5216step1 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5216step1 permutation7 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair411 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node411 node411Labels = Sparse.eval singlePairValue411 (familyPairVector B) := by
  have hp := single_label_three B hB node411
  have hl : node411Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node411 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node411 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node411 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node411 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node411 (EqualityPatterns.family3.label 1) = PairSemantics.raw5216 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node411 PairSemantics.raw5216; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5216 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node411 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node411 (EqualityPatterns.family3.label 2) = PairSemantics.raw7634 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node411 PairSemantics.raw7634; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7634 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node411 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node411 (EqualityPatterns.family3.label 3) = PairSemantics.raw893 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node411 PairSemantics.raw893; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical893 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node411 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value566 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node411 (EqualityPatterns.family3.label 4) = PairSemantics.raw791 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node411 PairSemantics.raw791; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical791 hH).trans (PairSemantics.sound566 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue411, PairSemantics.value0, PairSemantics.value4, PairSemantics.value26, PairSemantics.value232, PairSemantics.value566, Sparse.eval] at hp ⊢
  linarith only [hp]

theorem singlePair412 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node412 node412Labels = Sparse.eval singlePairValue412 (familyPairVector B) := by
  have hp := single_label_three B hB node412
  have hl : node412Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node412 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node412 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node412 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node412 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node412 (EqualityPatterns.family3.label 1) = PairSemantics.raw5215 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node412 PairSemantics.raw5215; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5215 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node412 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node412 (EqualityPatterns.family3.label 2) = PairSemantics.raw7636 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node412 PairSemantics.raw7636; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7636 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node412 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node412 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node412 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node412 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value177 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node412 (EqualityPatterns.family3.label 4) = PairSemantics.raw792 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node412 PairSemantics.raw792; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical792 hH).trans (PairSemantics.sound177 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue412, PairSemantics.value0, PairSemantics.value4, PairSemantics.value10, PairSemantics.value46, PairSemantics.value177, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton2753 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2753 node2753Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node397 node397Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw264 singletonSmall2753
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2753) = raw264Labels := by decide +kernel
  rw [hl, canonical264 B hB] at h
  have hc0 : mixedMoment B raw264 (Fin.cases (0 : Fin 1) singletonSmall2753) =
      mixedMoment B node397 node397Labels := by
    have ha : raw264 = raw265 := by apply Matrix.ext; unfold raw264 raw265; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2753 = raw265Labels := by decide +kernel
    rw [ha, hj, canonical265 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton2755 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2755 node2755Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node262 node262Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw266 singletonSmall2755
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2755) = raw266Labels := by decide +kernel
  rw [hl, canonical266 B hB] at h
  have hc0 : mixedMoment B raw266 (Fin.cases (0 : Fin 1) singletonSmall2755) =
      mixedMoment B node262 node262Labels := by
    have ha : raw266 = raw267 := by apply Matrix.ext; unfold raw266 raw267; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2755 = raw267Labels := by decide +kernel
    rw [ha, hj, canonical267 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton2775 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2775 node2775Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node411 node411Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw276 singletonSmall2775
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2775) = raw276Labels := by decide +kernel
  rw [hl, canonical276 B hB] at h
  have hc0 : mixedMoment B raw276 (Fin.cases (0 : Fin 1) singletonSmall2775) =
      mixedMoment B node411 node411Labels := by
    have ha : raw276 = raw277 := by apply Matrix.ext; unfold raw276 raw277; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2775 = raw277Labels := by decide +kernel
    rw [ha, hj, canonical277 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton2776 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2776 node2776Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node412 node412Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw278 singletonSmall2776
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2776) = raw278Labels := by decide +kernel
  rw [hl, canonical278 B hB] at h
  have hc0 : mixedMoment B raw278 (Fin.cases (0 : Fin 1) singletonSmall2776) =
      mixedMoment B node412 node412Labels := by
    have ha : raw278 = raw279 := by apply Matrix.ext; unfold raw278 raw279; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2776 = raw279Labels := by decide +kernel
    rw [ha, hj, canonical279 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton2778 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2778 node2778Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node270 node270Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw280 singletonSmall2778
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2778) = raw280Labels := by decide +kernel
  rw [hl, canonical280 B hB] at h
  have hc0 : mixedMoment B raw280 (Fin.cases (0 : Fin 1) singletonSmall2778) =
      mixedMoment B node270 node270Labels := by
    have ha : raw280 = raw281 := by apply Matrix.ext; unfold raw280 raw281; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2778 = raw281Labels := by decide +kernel
    rw [ha, hj, canonical281 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node262 node262Labels = Sparse.eval nodeValue262 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue262 (familyPairVector B) := singlePair262 B _hB
    _ = _ := by norm_num [singlePairValue262, nodeValue262, Sparse.eval, mixedVector] <;> ring

theorem sound270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node270 node270Labels = Sparse.eval nodeValue270 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue270 (familyPairVector B) := singlePair270 B _hB
    _ = _ := by norm_num [singlePairValue270, nodeValue270, Sparse.eval, mixedVector] <;> ring

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2720 node2720Labels = 0 := by
  exact mixedMoment_alpha B hF node2720 node2720Labels 1 permutation203
    (by decide +kernel)

theorem zero2741 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2741 node2741Labels = 0 := by
  exact mixedMoment_order_one B hB node2741 node2741Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2742 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2742 node2742Labels = 0 := by
  exact mixedMoment_order_one B hB node2742 node2742Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2716 node2716Labels = Sparse.eval nodeValue2716 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2716) = mixedMoment B node2716 node2716Labels := rfl
  simpa [nodeValue2716, Sparse.eval] using hc.symm

theorem sound2718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2718 node2718Labels = Sparse.eval nodeValue2718 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2718) = mixedMoment B node2718 node2718Labels := rfl
  simpa [nodeValue2718, Sparse.eval] using hc.symm

theorem sound2719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2719 node2719Labels = Sparse.eval nodeValue2719 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2719) = mixedMoment B node2719 node2719Labels := rfl
  simpa [nodeValue2719, Sparse.eval] using hc.symm

theorem sound2720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2720 node2720Labels = Sparse.eval nodeValue2720 (mixedVector B) := by
  simpa only [nodeValue2720, Sparse.eval_nil] using zero2720 B _hB _hF

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

theorem sound2724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2724 node2724Labels = Sparse.eval nodeValue2724 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2724) = mixedMoment B node2724 node2724Labels := rfl
  simpa [nodeValue2724, Sparse.eval] using hc.symm

theorem sound2726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2726 node2726Labels = Sparse.eval nodeValue2726 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2726) = mixedMoment B node2726 node2726Labels := rfl
  simpa [nodeValue2726, Sparse.eval] using hc.symm

theorem sound2728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2728 node2728Labels = Sparse.eval nodeValue2728 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2728) = mixedMoment B node2728 node2728Labels := rfl
  simpa [nodeValue2728, Sparse.eval] using hc.symm

theorem sound2729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2729 node2729Labels = Sparse.eval nodeValue2729 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2729) = mixedMoment B node2729 node2729Labels := rfl
  simpa [nodeValue2729, Sparse.eval] using hc.symm

theorem sound2730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2730 node2730Labels = Sparse.eval nodeValue2730 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2730) = mixedMoment B node2730 node2730Labels := rfl
  simpa [nodeValue2730, Sparse.eval] using hc.symm

theorem sound2731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2731 node2731Labels = Sparse.eval nodeValue2731 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2731) = mixedMoment B node2731 node2731Labels := rfl
  simpa [nodeValue2731, Sparse.eval] using hc.symm

theorem sound2732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2732 node2732Labels = Sparse.eval nodeValue2732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2732) = mixedMoment B node2732 node2732Labels := rfl
  simpa [nodeValue2732, Sparse.eval] using hc.symm

theorem sound2734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2734 node2734Labels = Sparse.eval nodeValue2734 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2734) = mixedMoment B node2734 node2734Labels := rfl
  simpa [nodeValue2734, Sparse.eval] using hc.symm

theorem sound2735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2735 node2735Labels = Sparse.eval nodeValue2735 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2735) = mixedMoment B node2735 node2735Labels := rfl
  simpa [nodeValue2735, Sparse.eval] using hc.symm

theorem sound2736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2736 node2736Labels = Sparse.eval nodeValue2736 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2736) = mixedMoment B node2736 node2736Labels := rfl
  simpa [nodeValue2736, Sparse.eval] using hc.symm

theorem sound2737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2737 node2737Labels = Sparse.eval nodeValue2737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2737) = mixedMoment B node2737 node2737Labels := rfl
  simpa [nodeValue2737, Sparse.eval] using hc.symm

theorem sound2738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2738 node2738Labels = Sparse.eval nodeValue2738 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2738) = mixedMoment B node2738 node2738Labels := rfl
  simpa [nodeValue2738, Sparse.eval] using hc.symm

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

theorem sound2741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2741 node2741Labels = Sparse.eval nodeValue2741 (mixedVector B) := by
  simpa only [nodeValue2741, Sparse.eval_nil] using zero2741 B _hB _hF

theorem sound2742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2742 node2742Labels = Sparse.eval nodeValue2742 (mixedVector B) := by
  simpa only [nodeValue2742, Sparse.eval_nil] using zero2742 B _hB _hF

theorem sound2743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2743 node2743Labels = Sparse.eval nodeValue2743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2743) = mixedMoment B node2743 node2743Labels := rfl
  simpa [nodeValue2743, Sparse.eval] using hc.symm

theorem sound2744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2744 node2744Labels = Sparse.eval nodeValue2744 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2744) = mixedMoment B node2744 node2744Labels := rfl
  simpa [nodeValue2744, Sparse.eval] using hc.symm

theorem sound2745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2745 node2745Labels = Sparse.eval nodeValue2745 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2745) = mixedMoment B node2745 node2745Labels := rfl
  simpa [nodeValue2745, Sparse.eval] using hc.symm

theorem sound2746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2746 node2746Labels = Sparse.eval nodeValue2746 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2746) = mixedMoment B node2746 node2746Labels := rfl
  simpa [nodeValue2746, Sparse.eval] using hc.symm

theorem sound2747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2747 node2747Labels = Sparse.eval nodeValue2747 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2747) = mixedMoment B node2747 node2747Labels := rfl
  simpa [nodeValue2747, Sparse.eval] using hc.symm

theorem sound2748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2748 node2748Labels = Sparse.eval nodeValue2748 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2748) = mixedMoment B node2748 node2748Labels := rfl
  simpa [nodeValue2748, Sparse.eval] using hc.symm

theorem sound2750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2750 node2750Labels = Sparse.eval nodeValue2750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2750) = mixedMoment B node2750 node2750Labels := rfl
  simpa [nodeValue2750, Sparse.eval] using hc.symm

theorem sound2751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2751 node2751Labels = Sparse.eval nodeValue2751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2751) = mixedMoment B node2751 node2751Labels := rfl
  simpa [nodeValue2751, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node397 node397Labels = Sparse.eval nodeValue397 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue397 (familyPairVector B) := singlePair397 B _hB
    _ = _ := by
      norm_num [singlePairValue397, nodeValue397, Sparse.eval, mixedVector]
      ring

theorem sound411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node411 node411Labels = Sparse.eval nodeValue411 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue411 (familyPairVector B) := singlePair411 B _hB
    _ = _ := by
      norm_num [singlePairValue411, nodeValue411, Sparse.eval, mixedVector]
      ring

theorem sound412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node412 node412Labels = Sparse.eval nodeValue412 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue412 (familyPairVector B) := singlePair412 B _hB
    _ = _ := by
      norm_num [singlePairValue412, nodeValue412, Sparse.eval, mixedVector]
      ring

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

theorem sound2753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2753 node2753Labels = Sparse.eval nodeValue2753 (mixedVector B) := by
  have h := singleton2753 B _hB
  rw [sound397 B _hB _hF] at h
  norm_num [nodeValue2753, nodeValue397, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2754 node2754Labels = Sparse.eval nodeValue2754 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2754) = mixedMoment B node2754 node2754Labels := rfl
  simpa [nodeValue2754, Sparse.eval] using hc.symm

theorem sound2755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2755 node2755Labels = Sparse.eval nodeValue2755 (mixedVector B) := by
  have h := singleton2755 B _hB
  rw [sound262 B _hB _hF] at h
  norm_num [nodeValue2755, nodeValue262, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2758 node2758Labels = Sparse.eval nodeValue2758 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2758) = mixedMoment B node2758 node2758Labels := rfl
  simpa [nodeValue2758, Sparse.eval] using hc.symm

theorem sound2759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2759 node2759Labels = Sparse.eval nodeValue2759 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2759) = mixedMoment B node2759 node2759Labels := rfl
  simpa [nodeValue2759, Sparse.eval] using hc.symm

theorem sound2760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2760 node2760Labels = Sparse.eval nodeValue2760 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2760) = mixedMoment B node2760 node2760Labels := rfl
  simpa [nodeValue2760, Sparse.eval] using hc.symm

theorem sound2761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2761 node2761Labels = Sparse.eval nodeValue2761 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2761) = mixedMoment B node2761 node2761Labels := rfl
  simpa [nodeValue2761, Sparse.eval] using hc.symm

theorem sound2763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2763 node2763Labels = Sparse.eval nodeValue2763 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2763) = mixedMoment B node2763 node2763Labels := rfl
  simpa [nodeValue2763, Sparse.eval] using hc.symm

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

theorem sound2769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2769 node2769Labels = Sparse.eval nodeValue2769 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2769) = mixedMoment B node2769 node2769Labels := rfl
  simpa [nodeValue2769, Sparse.eval] using hc.symm

theorem sound2771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2771 node2771Labels = Sparse.eval nodeValue2771 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2771) = mixedMoment B node2771 node2771Labels := rfl
  simpa [nodeValue2771, Sparse.eval] using hc.symm

theorem sound2773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2773 node2773Labels = Sparse.eval nodeValue2773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2773) = mixedMoment B node2773 node2773Labels := rfl
  simpa [nodeValue2773, Sparse.eval] using hc.symm

theorem sound2774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2774 node2774Labels = Sparse.eval nodeValue2774 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2774) = mixedMoment B node2774 node2774Labels := rfl
  simpa [nodeValue2774, Sparse.eval] using hc.symm

theorem sound2775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2775 node2775Labels = Sparse.eval nodeValue2775 (mixedVector B) := by
  have h := singleton2775 B _hB
  rw [sound411 B _hB _hF] at h
  norm_num [nodeValue2775, nodeValue411, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2776 node2776Labels = Sparse.eval nodeValue2776 (mixedVector B) := by
  have h := singleton2776 B _hB
  rw [sound412 B _hB _hF] at h
  norm_num [nodeValue2776, nodeValue412, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2777 node2777Labels = Sparse.eval nodeValue2777 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2777) = mixedMoment B node2777 node2777Labels := rfl
  simpa [nodeValue2777, Sparse.eval] using hc.symm

theorem sound2778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2778 node2778Labels = Sparse.eval nodeValue2778 (mixedVector B) := by
  have h := singleton2778 B _hB
  rw [sound270 B _hB _hF] at h
  norm_num [nodeValue2778, nodeValue270, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2779 node2779Labels = Sparse.eval nodeValue2779 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2779) = mixedMoment B node2779 node2779Labels := rfl
  simpa [nodeValue2779, Sparse.eval] using hc.symm

theorem sound2780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2780 node2780Labels = Sparse.eval nodeValue2780 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2780) = mixedMoment B node2780 node2780Labels := rfl
  simpa [nodeValue2780, Sparse.eval] using hc.symm

theorem sound2781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2781 node2781Labels = Sparse.eval nodeValue2781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2781) = mixedMoment B node2781 node2781Labels := rfl
  simpa [nodeValue2781, Sparse.eval] using hc.symm

theorem sound2782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2782 node2782Labels = Sparse.eval nodeValue2782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2782) = mixedMoment B node2782 node2782Labels := rfl
  simpa [nodeValue2782, Sparse.eval] using hc.symm

theorem sound2783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2783 node2783Labels = Sparse.eval nodeValue2783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2783) = mixedMoment B node2783 node2783Labels := rfl
  simpa [nodeValue2783, Sparse.eval] using hc.symm

theorem sound2789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2789 node2789Labels = Sparse.eval nodeValue2789 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2789) = mixedMoment B node2789 node2789Labels := rfl
  simpa [nodeValue2789, Sparse.eval] using hc.symm

theorem sound2797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2797 node2797Labels = Sparse.eval nodeValue2797 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2797) = mixedMoment B node2797 node2797Labels := rfl
  simpa [nodeValue2797, Sparse.eval] using hc.symm

theorem sound2798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2798 node2798Labels = Sparse.eval nodeValue2798 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2798) = mixedMoment B node2798 node2798Labels := rfl
  simpa [nodeValue2798, Sparse.eval] using hc.symm

theorem sound2800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2800 node2800Labels = Sparse.eval nodeValue2800 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2800) = mixedMoment B node2800 node2800Labels := rfl
  simpa [nodeValue2800, Sparse.eval] using hc.symm

theorem sound2801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2801 node2801Labels = Sparse.eval nodeValue2801 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2801) = mixedMoment B node2801 node2801Labels := rfl
  simpa [nodeValue2801, Sparse.eval] using hc.symm

theorem sound2802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2802 node2802Labels = Sparse.eval nodeValue2802 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2802) = mixedMoment B node2802 node2802Labels := rfl
  simpa [nodeValue2802, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1019 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1019 x = (178978720009420800000 : ℝ) * Sparse.eval nodeValue2716 x := by
  norm_num [reducedTerm1019, nodeValue2716, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1020 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1020 x = (2657205919166496768000 : ℝ) * Sparse.eval nodeValue2718 x := by
  norm_num [reducedTerm1020, nodeValue2718, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1021 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1021 x = (189716558307655680000 : ℝ) * Sparse.eval nodeValue2719 x := by
  norm_num [reducedTerm1021, nodeValue2719, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1022 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1022 x = (13122384698173685760000 : ℝ) * Sparse.eval nodeValue2720 x := by
  norm_num [reducedTerm1022, nodeValue2720, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1023 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1023 x = (-19158304125686906880000 : ℝ) * Sparse.eval nodeValue2721 x := by
  norm_num [reducedTerm1023, nodeValue2721, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1024 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1024 x = (-53630193427477954560000 : ℝ) * Sparse.eval nodeValue2722 x := by
  norm_num [reducedTerm1024, nodeValue2722, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1025 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1025 x = (-6132895964194406400000 : ℝ) * Sparse.eval nodeValue2723 x := by
  norm_num [reducedTerm1025, nodeValue2723, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1026 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1026 x = (151499143634485248000 : ℝ) * Sparse.eval nodeValue2724 x := by
  norm_num [reducedTerm1026, nodeValue2724, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1027 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1027 x = (-21951447043276800000 : ℝ) * Sparse.eval nodeValue2726 x := by
  norm_num [reducedTerm1027, nodeValue2726, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1028 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1028 x = (-4207603471599403008000 : ℝ) * Sparse.eval nodeValue2728 x := by
  norm_num [reducedTerm1028, nodeValue2728, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1029 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1029 x = (160580769836433408000 : ℝ) * Sparse.eval nodeValue2729 x := by
  norm_num [reducedTerm1029, nodeValue2729, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1030 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1030 x = (-5448613796115775488000 : ℝ) * Sparse.eval nodeValue2730 x := by
  norm_num [reducedTerm1030, nodeValue2730, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1031 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1031 x = (1891520709844598784000 : ℝ) * Sparse.eval nodeValue2731 x := by
  norm_num [reducedTerm1031, nodeValue2731, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1032 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1032 x = (-3902216098532032512000 : ℝ) * Sparse.eval nodeValue2732 x := by
  norm_num [reducedTerm1032, nodeValue2732, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1033 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1033 x = (6171454343172980736000 : ℝ) * Sparse.eval nodeValue2734 x := by
  norm_num [reducedTerm1033, nodeValue2734, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1034 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1034 x = (3357311730124455936000 : ℝ) * Sparse.eval nodeValue2735 x := by
  norm_num [reducedTerm1034, nodeValue2735, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1035 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1035 x = (4773540463463890944000 : ℝ) * Sparse.eval nodeValue2736 x := by
  norm_num [reducedTerm1035, nodeValue2736, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1036 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1036 x = (-189385081118392320000 : ℝ) * Sparse.eval nodeValue2737 x := by
  norm_num [reducedTerm1036, nodeValue2737, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1037 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1037 x = (4201772064568049664000 : ℝ) * Sparse.eval nodeValue2738 x := by
  norm_num [reducedTerm1037, nodeValue2738, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1038 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1038 x = (863627382126673920000 : ℝ) * Sparse.eval nodeValue2739 x := by
  norm_num [reducedTerm1038, nodeValue2739, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1039 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1039 x = (-636663027329925120000 : ℝ) * Sparse.eval nodeValue2740 x := by
  norm_num [reducedTerm1039, nodeValue2740, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1040 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1040 x = (21683846257842585600000 : ℝ) * Sparse.eval nodeValue2741 x := by
  norm_num [reducedTerm1040, nodeValue2741, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1041 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1041 x = (46576712078516551680000 : ℝ) * Sparse.eval nodeValue2742 x := by
  norm_num [reducedTerm1041, nodeValue2742, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1042 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1042 x = (11054987203142615040000 : ℝ) * Sparse.eval nodeValue2743 x := by
  norm_num [reducedTerm1042, nodeValue2743, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1043 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1043 x = (-22996102308321558528000 : ℝ) * Sparse.eval nodeValue2744 x := by
  norm_num [reducedTerm1043, nodeValue2744, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1044 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1044 x = (-5202654127895347200000 : ℝ) * Sparse.eval nodeValue2745 x := by
  norm_num [reducedTerm1044, nodeValue2745, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1045 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1045 x = (5202654127895347200000 : ℝ) * Sparse.eval nodeValue2746 x := by
  norm_num [reducedTerm1045, nodeValue2746, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1046 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1046 x = (-1346211378226003968000 : ℝ) * Sparse.eval nodeValue2747 x := by
  norm_num [reducedTerm1046, nodeValue2747, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1047 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1047 x = (-3407495751248117760000 : ℝ) * Sparse.eval nodeValue2748 x := by
  norm_num [reducedTerm1047, nodeValue2748, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1048 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1048 x = (27983833967776038912000 : ℝ) * Sparse.eval nodeValue2750 x := by
  norm_num [reducedTerm1048, nodeValue2750, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1049 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1049 x = (-28257993540927553536000 : ℝ) * Sparse.eval nodeValue2751 x := by
  norm_num [reducedTerm1049, nodeValue2751, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1050 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1050 x = (-521061915183022080000 : ℝ) * Sparse.eval nodeValue2753 x := by
  norm_num [reducedTerm1050, nodeValue2753, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1051 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1051 x = (-4946831880077574144000 : ℝ) * Sparse.eval nodeValue2754 x := by
  norm_num [reducedTerm1051, nodeValue2754, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1052 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1052 x = (757011477946171392000 : ℝ) * Sparse.eval nodeValue2755 x := by
  norm_num [reducedTerm1052, nodeValue2755, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1053 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1053 x = (-8092322011089469440000 : ℝ) * Sparse.eval nodeValue2758 x := by
  norm_num [reducedTerm1053, nodeValue2758, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1054 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1054 x = (-7444916811245813760000 : ℝ) * Sparse.eval nodeValue2759 x := by
  norm_num [reducedTerm1054, nodeValue2759, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1055 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1055 x = (-416428679821787136000 : ℝ) * Sparse.eval nodeValue2760 x := by
  norm_num [reducedTerm1055, nodeValue2760, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1056 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1056 x = (-1016042941450027008000 : ℝ) * Sparse.eval nodeValue2761 x := by
  norm_num [reducedTerm1056, nodeValue2761, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1057 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1057 x = (-21955095856769531904000 : ℝ) * Sparse.eval nodeValue2763 x := by
  norm_num [reducedTerm1057, nodeValue2763, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1058 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1058 x = (-23846279734862807040000 : ℝ) * Sparse.eval nodeValue2764 x := by
  norm_num [reducedTerm1058, nodeValue2764, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1059 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1059 x = (9533108969263595520000 : ℝ) * Sparse.eval nodeValue2765 x := by
  norm_num [reducedTerm1059, nodeValue2765, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1060 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1060 x = (-22778979783065468928000 : ℝ) * Sparse.eval nodeValue2769 x := by
  norm_num [reducedTerm1060, nodeValue2769, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1061 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1061 x = (-1080639818309173248000 : ℝ) * Sparse.eval nodeValue2771 x := by
  norm_num [reducedTerm1061, nodeValue2771, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1062 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1062 x = (-7680684652994691072000 : ℝ) * Sparse.eval nodeValue2773 x := by
  norm_num [reducedTerm1062, nodeValue2773, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1063 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1063 x = (4689897337119375360000 : ℝ) * Sparse.eval nodeValue2774 x := by
  norm_num [reducedTerm1063, nodeValue2774, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1064 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1064 x = (-563280397683720192000 : ℝ) * Sparse.eval nodeValue2775 x := by
  norm_num [reducedTerm1064, nodeValue2775, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1065 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1065 x = (-3710011026318557184000 : ℝ) * Sparse.eval nodeValue2776 x := by
  norm_num [reducedTerm1065, nodeValue2776, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1066 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1066 x = (-4714450911702024192000 : ℝ) * Sparse.eval nodeValue2777 x := by
  norm_num [reducedTerm1066, nodeValue2777, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1067 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1067 x = (-1215313374856347648000 : ℝ) * Sparse.eval nodeValue2778 x := by
  norm_num [reducedTerm1067, nodeValue2778, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1068 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1068 x = (1029413887898812416000 : ℝ) * Sparse.eval nodeValue2779 x := by
  norm_num [reducedTerm1068, nodeValue2779, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1069 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1069 x = (-218973289450438656000 : ℝ) * Sparse.eval nodeValue2780 x := by
  norm_num [reducedTerm1069, nodeValue2780, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1070 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1070 x = (-9759313319373176832000 : ℝ) * Sparse.eval nodeValue2781 x := by
  norm_num [reducedTerm1070, nodeValue2781, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1071 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1071 x = (-28741157247379046400000 : ℝ) * Sparse.eval nodeValue2782 x := by
  norm_num [reducedTerm1071, nodeValue2782, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1072 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1072 x = (-12330745384768634880000 : ℝ) * Sparse.eval nodeValue2783 x := by
  norm_num [reducedTerm1072, nodeValue2783, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1073 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1073 x = (-13743886838351265792000 : ℝ) * Sparse.eval nodeValue2789 x := by
  norm_num [reducedTerm1073, nodeValue2789, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1074 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1074 x = (10817029381629542400000 : ℝ) * Sparse.eval nodeValue2797 x := by
  norm_num [reducedTerm1074, nodeValue2797, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1075 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1075 x = (-6752922376232632320000 : ℝ) * Sparse.eval nodeValue2798 x := by
  norm_num [reducedTerm1075, nodeValue2798, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1076 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1076 x = (-3995973679581757440000 : ℝ) * Sparse.eval nodeValue2800 x := by
  norm_num [reducedTerm1076, nodeValue2800, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1077 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1077 x = (-1340821167243264000000 : ℝ) * Sparse.eval nodeValue2801 x := by
  norm_num [reducedTerm1077, nodeValue2801, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1078 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1078 x = (4806257162718412800000 : ℝ) * Sparse.eval nodeValue2802 x := by
  norm_num [reducedTerm1078, nodeValue2802, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1017Check : reducedMerge1017 = Integer.Sparse.mergeBy masterLess reducedTerm1020 reducedTerm1021 := by decide +kernel

theorem reducedMerge1018Check : reducedMerge1018 = Integer.Sparse.mergeBy masterLess reducedTerm1019 reducedMerge1017 := by decide +kernel

theorem reducedMerge1019Check : reducedMerge1019 = Integer.Sparse.mergeBy masterLess reducedTerm1022 reducedTerm1023 := by decide +kernel

theorem reducedMerge1020Check : reducedMerge1020 = Integer.Sparse.mergeBy masterLess reducedTerm1024 reducedTerm1025 := by decide +kernel

theorem reducedMerge1021Check : reducedMerge1021 = Integer.Sparse.mergeBy masterLess reducedMerge1019 reducedMerge1020 := by decide +kernel

theorem reducedMerge1022Check : reducedMerge1022 = Integer.Sparse.mergeBy masterLess reducedMerge1018 reducedMerge1021 := by decide +kernel

theorem reducedMerge1023Check : reducedMerge1023 = Integer.Sparse.mergeBy masterLess reducedTerm1026 reducedTerm1027 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1024Check : reducedMerge1024 = Integer.Sparse.mergeBy masterLess reducedTerm1028 reducedTerm1029 := by decide +kernel

theorem reducedMerge1025Check : reducedMerge1025 = Integer.Sparse.mergeBy masterLess reducedMerge1023 reducedMerge1024 := by decide +kernel

theorem reducedMerge1026Check : reducedMerge1026 = Integer.Sparse.mergeBy masterLess reducedTerm1030 reducedTerm1031 := by decide +kernel

theorem reducedMerge1027Check : reducedMerge1027 = Integer.Sparse.mergeBy masterLess reducedTerm1032 reducedTerm1033 := by decide +kernel

theorem reducedMerge1028Check : reducedMerge1028 = Integer.Sparse.mergeBy masterLess reducedMerge1026 reducedMerge1027 := by decide +kernel

theorem reducedMerge1029Check : reducedMerge1029 = Integer.Sparse.mergeBy masterLess reducedMerge1025 reducedMerge1028 := by decide +kernel

theorem reducedMerge1030Check : reducedMerge1030 = Integer.Sparse.mergeBy masterLess reducedMerge1022 reducedMerge1029 := by decide +kernel

theorem reducedMerge1031Check : reducedMerge1031 = Integer.Sparse.mergeBy masterLess reducedTerm1035 reducedTerm1036 := by decide +kernel

theorem reducedMerge1032Check : reducedMerge1032 = Integer.Sparse.mergeBy masterLess reducedTerm1034 reducedMerge1031 := by decide +kernel

theorem reducedMerge1033Check : reducedMerge1033 = Integer.Sparse.mergeBy masterLess reducedTerm1037 reducedTerm1038 := by decide +kernel

theorem reducedMerge1034Check : reducedMerge1034 = Integer.Sparse.mergeBy masterLess reducedTerm1039 reducedTerm1040 := by decide +kernel

theorem reducedMerge1035Check : reducedMerge1035 = Integer.Sparse.mergeBy masterLess reducedMerge1033 reducedMerge1034 := by decide +kernel

theorem reducedMerge1036Check : reducedMerge1036 = Integer.Sparse.mergeBy masterLess reducedMerge1032 reducedMerge1035 := by decide +kernel

theorem reducedMerge1037Check : reducedMerge1037 = Integer.Sparse.mergeBy masterLess reducedTerm1041 reducedTerm1042 := by decide +kernel

theorem reducedMerge1038Check : reducedMerge1038 = Integer.Sparse.mergeBy masterLess reducedTerm1043 reducedTerm1044 := by decide +kernel

theorem reducedMerge1039Check : reducedMerge1039 = Integer.Sparse.mergeBy masterLess reducedMerge1037 reducedMerge1038 := by decide +kernel

theorem reducedMerge1040Check : reducedMerge1040 = Integer.Sparse.mergeBy masterLess reducedTerm1045 reducedTerm1046 := by decide +kernel

theorem reducedMerge1041Check : reducedMerge1041 = Integer.Sparse.mergeBy masterLess reducedTerm1047 reducedTerm1048 := by decide +kernel

theorem reducedMerge1042Check : reducedMerge1042 = Integer.Sparse.mergeBy masterLess reducedMerge1040 reducedMerge1041 := by decide +kernel

theorem reducedMerge1043Check : reducedMerge1043 = Integer.Sparse.mergeBy masterLess reducedMerge1039 reducedMerge1042 := by decide +kernel

theorem reducedMerge1044Check : reducedMerge1044 = Integer.Sparse.mergeBy masterLess reducedMerge1036 reducedMerge1043 := by decide +kernel

theorem reducedMerge1045Check : reducedMerge1045 = Integer.Sparse.mergeBy masterLess reducedMerge1030 reducedMerge1044 := by decide +kernel

theorem reducedMerge1046Check : reducedMerge1046 = Integer.Sparse.mergeBy masterLess reducedTerm1050 reducedTerm1051 := by decide +kernel

theorem reducedMerge1047Check : reducedMerge1047 = Integer.Sparse.mergeBy masterLess reducedTerm1049 reducedMerge1046 := by decide +kernel

theorem reducedMerge1048Check : reducedMerge1048 = Integer.Sparse.mergeBy masterLess reducedTerm1052 reducedTerm1053 := by decide +kernel

theorem reducedMerge1049Check : reducedMerge1049 = Integer.Sparse.mergeBy masterLess reducedTerm1054 reducedTerm1055 := by decide +kernel

theorem reducedMerge1050Check : reducedMerge1050 = Integer.Sparse.mergeBy masterLess reducedMerge1048 reducedMerge1049 := by decide +kernel

theorem reducedMerge1051Check : reducedMerge1051 = Integer.Sparse.mergeBy masterLess reducedMerge1047 reducedMerge1050 := by decide +kernel

theorem reducedMerge1052Check : reducedMerge1052 = Integer.Sparse.mergeBy masterLess reducedTerm1056 reducedTerm1057 := by decide +kernel

theorem reducedMerge1053Check : reducedMerge1053 = Integer.Sparse.mergeBy masterLess reducedTerm1058 reducedTerm1059 := by decide +kernel

theorem reducedMerge1054Check : reducedMerge1054 = Integer.Sparse.mergeBy masterLess reducedMerge1052 reducedMerge1053 := by decide +kernel

theorem reducedMerge1055Check : reducedMerge1055 = Integer.Sparse.mergeBy masterLess reducedTerm1060 reducedTerm1061 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1056Check : reducedMerge1056 = Integer.Sparse.mergeBy masterLess reducedTerm1062 reducedTerm1063 := by decide +kernel

theorem reducedMerge1057Check : reducedMerge1057 = Integer.Sparse.mergeBy masterLess reducedMerge1055 reducedMerge1056 := by decide +kernel

theorem reducedMerge1058Check : reducedMerge1058 = Integer.Sparse.mergeBy masterLess reducedMerge1054 reducedMerge1057 := by decide +kernel

theorem reducedMerge1059Check : reducedMerge1059 = Integer.Sparse.mergeBy masterLess reducedMerge1051 reducedMerge1058 := by decide +kernel

theorem reducedMerge1060Check : reducedMerge1060 = Integer.Sparse.mergeBy masterLess reducedTerm1065 reducedTerm1066 := by decide +kernel

theorem reducedMerge1061Check : reducedMerge1061 = Integer.Sparse.mergeBy masterLess reducedTerm1064 reducedMerge1060 := by decide +kernel

theorem reducedMerge1062Check : reducedMerge1062 = Integer.Sparse.mergeBy masterLess reducedTerm1067 reducedTerm1068 := by decide +kernel

theorem reducedMerge1063Check : reducedMerge1063 = Integer.Sparse.mergeBy masterLess reducedTerm1069 reducedTerm1070 := by decide +kernel

theorem reducedMerge1064Check : reducedMerge1064 = Integer.Sparse.mergeBy masterLess reducedMerge1062 reducedMerge1063 := by decide +kernel

theorem reducedMerge1065Check : reducedMerge1065 = Integer.Sparse.mergeBy masterLess reducedMerge1061 reducedMerge1064 := by decide +kernel

theorem reducedMerge1066Check : reducedMerge1066 = Integer.Sparse.mergeBy masterLess reducedTerm1071 reducedTerm1072 := by decide +kernel

theorem reducedMerge1067Check : reducedMerge1067 = Integer.Sparse.mergeBy masterLess reducedTerm1073 reducedTerm1074 := by decide +kernel

theorem reducedMerge1068Check : reducedMerge1068 = Integer.Sparse.mergeBy masterLess reducedMerge1066 reducedMerge1067 := by decide +kernel

theorem reducedMerge1069Check : reducedMerge1069 = Integer.Sparse.mergeBy masterLess reducedTerm1075 reducedTerm1076 := by decide +kernel

theorem reducedMerge1070Check : reducedMerge1070 = Integer.Sparse.mergeBy masterLess reducedTerm1077 reducedTerm1078 := by decide +kernel

theorem reducedMerge1071Check : reducedMerge1071 = Integer.Sparse.mergeBy masterLess reducedMerge1069 reducedMerge1070 := by decide +kernel

theorem reducedMerge1072Check : reducedMerge1072 = Integer.Sparse.mergeBy masterLess reducedMerge1068 reducedMerge1071 := by decide +kernel

theorem reducedMerge1073Check : reducedMerge1073 = Integer.Sparse.mergeBy masterLess reducedMerge1065 reducedMerge1072 := by decide +kernel

theorem reducedMerge1074Check : reducedMerge1074 = Integer.Sparse.mergeBy masterLess reducedMerge1059 reducedMerge1073 := by decide +kernel

theorem reducedMerge1075Check : reducedMerge1075 = Integer.Sparse.mergeBy masterLess reducedMerge1045 reducedMerge1074 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1019 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1019 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1019 (originalVector B) := by
  rw [reducedTermArithmetic1019, ← sound2716 B hB hF]
  change (178978720009420800000 : ℝ) * mixedMoment B node2716 node2716Labels =
    (37623398400 : ℝ) * ((4757112000 : ℝ) * mixedMoment B node2716 node2716Labels + 0)
  ring

theorem reducedTermEval1020 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1020 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1020 (originalVector B) := by
  rw [reducedTermArithmetic1020, ← sound2718 B hB hF]
  change (2657205919166496768000 : ℝ) * mixedMoment B node2718 node2718Labels =
    (37623398400 : ℝ) * ((70626419520 : ℝ) * mixedMoment B node2718 node2718Labels + 0)
  ring

theorem reducedTermEval1021 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1021 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1021 (originalVector B) := by
  rw [reducedTermArithmetic1021, ← sound2719 B hB hF]
  change (189716558307655680000 : ℝ) * mixedMoment B node2719 node2719Labels =
    (37623398400 : ℝ) * ((5042515200 : ℝ) * mixedMoment B node2719 node2719Labels + 0)
  ring

theorem reducedTermEval1022 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1022 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1022 (originalVector B) := by
  rw [reducedTermArithmetic1022, ← sound2720 B hB hF]
  change (13122384698173685760000 : ℝ) * mixedMoment B node2720 node2720Labels =
    (37623398400 : ℝ) * ((348782546400 : ℝ) * mixedMoment B node2720 node2720Labels + 0)
  ring

theorem reducedTermEval1023 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1023 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1023 (originalVector B) := by
  rw [reducedTermArithmetic1023, ← sound2721 B hB hF]
  change (-19158304125686906880000 : ℝ) * mixedMoment B node2721 node2721Labels =
    (37623398400 : ℝ) * (((-509212483200 : ℤ) : ℝ) * mixedMoment B node2721 node2721Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1024 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1024 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1024 (originalVector B) := by
  rw [reducedTermArithmetic1024, ← sound2722 B hB hF]
  change (-53630193427477954560000 : ℝ) * mixedMoment B node2722 node2722Labels =
    (37623398400 : ℝ) * (((-1425447878400 : ℤ) : ℝ) * mixedMoment B node2722 node2722Labels + 0)
  ring

theorem reducedTermEval1025 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1025 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1025 (originalVector B) := by
  rw [reducedTermArithmetic1025, ← sound2723 B hB hF]
  change (-6132895964194406400000 : ℝ) * mixedMoment B node2723 node2723Labels =
    (37623398400 : ℝ) * (((-163007496000 : ℤ) : ℝ) * mixedMoment B node2723 node2723Labels + 0)
  ring

theorem reducedTermEval1026 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1026 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1026 (originalVector B) := by
  rw [reducedTermArithmetic1026, ← sound2724 B hB hF]
  change (151499143634485248000 : ℝ) * mixedMoment B node2724 node2724Labels =
    (37623398400 : ℝ) * ((4026726720 : ℝ) * mixedMoment B node2724 node2724Labels + 0)
  ring

theorem reducedTermEval1027 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1027 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1027 (originalVector B) := by
  rw [reducedTermArithmetic1027, ← sound2726 B hB hF]
  change (-21951447043276800000 : ℝ) * mixedMoment B node2726 node2726Labels =
    (37623398400 : ℝ) * (((-583452000 : ℤ) : ℝ) * mixedMoment B node2726 node2726Labels + 0)
  ring

theorem reducedTermEval1028 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1028 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1028 (originalVector B) := by
  rw [reducedTermArithmetic1028, ← sound2728 B hB hF]
  change (-4207603471599403008000 : ℝ) * mixedMoment B node2728 node2728Labels =
    (37623398400 : ℝ) * (((-111834753120 : ℤ) : ℝ) * mixedMoment B node2728 node2728Labels + 0)
  ring

theorem reducedTermEval1029 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1029 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1029 (originalVector B) := by
  rw [reducedTermArithmetic1029, ← sound2729 B hB hF]
  change (160580769836433408000 : ℝ) * mixedMoment B node2729 node2729Labels =
    (37623398400 : ℝ) * ((4268109120 : ℝ) * mixedMoment B node2729 node2729Labels + 0)
  ring

theorem reducedTermEval1030 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1030 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1030 (originalVector B) := by
  rw [reducedTermArithmetic1030, ← sound2730 B hB hF]
  change (-5448613796115775488000 : ℝ) * mixedMoment B node2730 node2730Labels =
    (37623398400 : ℝ) * (((-144819820320 : ℤ) : ℝ) * mixedMoment B node2730 node2730Labels + 0)
  ring

theorem reducedTermEval1031 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1031 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1031 (originalVector B) := by
  rw [reducedTermArithmetic1031, ← sound2731 B hB hF]
  change (1891520709844598784000 : ℝ) * mixedMoment B node2731 node2731Labels =
    (37623398400 : ℝ) * ((50275115760 : ℝ) * mixedMoment B node2731 node2731Labels + 0)
  ring

theorem reducedTermEval1032 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1032 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1032 (originalVector B) := by
  rw [reducedTermArithmetic1032, ← sound2732 B hB hF]
  change (-3902216098532032512000 : ℝ) * mixedMoment B node2732 node2732Labels =
    (37623398400 : ℝ) * (((-103717799680 : ℤ) : ℝ) * mixedMoment B node2732 node2732Labels + 0)
  ring

theorem reducedTermEval1033 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1033 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1033 (originalVector B) := by
  rw [reducedTermArithmetic1033, ← sound2734 B hB hF]
  change (6171454343172980736000 : ℝ) * mixedMoment B node2734 node2734Labels =
    (37623398400 : ℝ) * ((164032347040 : ℝ) * mixedMoment B node2734 node2734Labels + 0)
  ring

theorem reducedTermEval1034 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1034 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1034 (originalVector B) := by
  rw [reducedTermArithmetic1034, ← sound2735 B hB hF]
  change (3357311730124455936000 : ℝ) * mixedMoment B node2735 node2735Labels =
    (37623398400 : ℝ) * ((89234675040 : ℝ) * mixedMoment B node2735 node2735Labels + 0)
  ring

theorem reducedTermEval1035 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1035 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1035 (originalVector B) := by
  rw [reducedTermArithmetic1035, ← sound2736 B hB hF]
  change (4773540463463890944000 : ℝ) * mixedMoment B node2736 node2736Labels =
    (37623398400 : ℝ) * ((126876908160 : ℝ) * mixedMoment B node2736 node2736Labels + 0)
  ring

theorem reducedTermEval1036 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1036 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1036 (originalVector B) := by
  rw [reducedTermArithmetic1036, ← sound2737 B hB hF]
  change (-189385081118392320000 : ℝ) * mixedMoment B node2737 node2737Labels =
    (37623398400 : ℝ) * (((-5033704800 : ℤ) : ℝ) * mixedMoment B node2737 node2737Labels + 0)
  ring

theorem reducedTermEval1037 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1037 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1037 (originalVector B) := by
  rw [reducedTermArithmetic1037, ← sound2738 B hB hF]
  change (4201772064568049664000 : ℝ) * mixedMoment B node2738 node2738Labels =
    (37623398400 : ℝ) * ((111679758960 : ℝ) * mixedMoment B node2738 node2738Labels + 0)
  ring

theorem reducedTermEval1038 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1038 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1038 (originalVector B) := by
  rw [reducedTermArithmetic1038, ← sound2739 B hB hF]
  change (863627382126673920000 : ℝ) * mixedMoment B node2739 node2739Labels =
    (37623398400 : ℝ) * ((22954528800 : ℝ) * mixedMoment B node2739 node2739Labels + 0)
  ring

theorem reducedTermEval1039 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1039 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1039 (originalVector B) := by
  rw [reducedTermArithmetic1039, ← sound2740 B hB hF]
  change (-636663027329925120000 : ℝ) * mixedMoment B node2740 node2740Labels =
    (37623398400 : ℝ) * (((-16921996800 : ℤ) : ℝ) * mixedMoment B node2740 node2740Labels + 0)
  ring

theorem reducedTermEval1040 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1040 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1040 (originalVector B) := by
  rw [reducedTermArithmetic1040, ← sound2741 B hB hF]
  change (21683846257842585600000 : ℝ) * mixedMoment B node2741 node2741Labels =
    (37623398400 : ℝ) * ((576339384000 : ℝ) * mixedMoment B node2741 node2741Labels + 0)
  ring

theorem reducedTermEval1041 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1041 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1041 (originalVector B) := by
  rw [reducedTermArithmetic1041, ← sound2742 B hB hF]
  change (46576712078516551680000 : ℝ) * mixedMoment B node2742 node2742Labels =
    (37623398400 : ℝ) * ((1237971955200 : ℝ) * mixedMoment B node2742 node2742Labels + 0)
  ring

theorem reducedTermEval1042 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1042 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1042 (originalVector B) := by
  rw [reducedTermArithmetic1042, ← sound2743 B hB hF]
  change (11054987203142615040000 : ℝ) * mixedMoment B node2743 node2743Labels =
    (37623398400 : ℝ) * ((293832765600 : ℝ) * mixedMoment B node2743 node2743Labels + 0)
  ring

theorem reducedTermEval1043 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1043 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1043 (originalVector B) := by
  rw [reducedTermArithmetic1043, ← sound2744 B hB hF]
  change (-22996102308321558528000 : ℝ) * mixedMoment B node2744 node2744Labels =
    (37623398400 : ℝ) * (((-611218105920 : ℤ) : ℝ) * mixedMoment B node2744 node2744Labels + 0)
  ring

theorem reducedTermEval1044 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1044 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1044 (originalVector B) := by
  rw [reducedTermArithmetic1044, ← sound2745 B hB hF]
  change (-5202654127895347200000 : ℝ) * mixedMoment B node2745 node2745Labels =
    (37623398400 : ℝ) * (((-138282408000 : ℤ) : ℝ) * mixedMoment B node2745 node2745Labels + 0)
  ring

theorem reducedTermEval1045 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1045 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1045 (originalVector B) := by
  rw [reducedTermArithmetic1045, ← sound2746 B hB hF]
  change (5202654127895347200000 : ℝ) * mixedMoment B node2746 node2746Labels =
    (37623398400 : ℝ) * ((138282408000 : ℝ) * mixedMoment B node2746 node2746Labels + 0)
  ring

theorem reducedTermEval1046 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1046 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1046 (originalVector B) := by
  rw [reducedTermArithmetic1046, ← sound2747 B hB hF]
  change (-1346211378226003968000 : ℝ) * mixedMoment B node2747 node2747Labels =
    (37623398400 : ℝ) * (((-35781227520 : ℤ) : ℝ) * mixedMoment B node2747 node2747Labels + 0)
  ring

theorem reducedTermEval1047 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1047 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1047 (originalVector B) := by
  rw [reducedTermArithmetic1047, ← sound2748 B hB hF]
  change (-3407495751248117760000 : ℝ) * mixedMoment B node2748 node2748Labels =
    (37623398400 : ℝ) * (((-90568526400 : ℤ) : ℝ) * mixedMoment B node2748 node2748Labels + 0)
  ring

theorem reducedTermEval1048 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1048 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1048 (originalVector B) := by
  rw [reducedTermArithmetic1048, ← sound2750 B hB hF]
  change (27983833967776038912000 : ℝ) * mixedMoment B node2750 node2750Labels =
    (37623398400 : ℝ) * ((743788045680 : ℝ) * mixedMoment B node2750 node2750Labels + 0)
  ring

theorem reducedTermEval1049 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1049 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1049 (originalVector B) := by
  rw [reducedTermArithmetic1049, ← sound2751 B hB hF]
  change (-28257993540927553536000 : ℝ) * mixedMoment B node2751 node2751Labels =
    (37623398400 : ℝ) * (((-751074989040 : ℤ) : ℝ) * mixedMoment B node2751 node2751Labels + 0)
  ring

theorem reducedTermEval1050 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1050 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1050 (originalVector B) := by
  rw [reducedTermArithmetic1050, ← sound2753 B hB hF]
  change (-521061915183022080000 : ℝ) * mixedMoment B node2753 node2753Labels =
    (37623398400 : ℝ) * (((-13849411200 : ℤ) : ℝ) * mixedMoment B node2753 node2753Labels + 0)
  ring

theorem reducedTermEval1051 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1051 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1051 (originalVector B) := by
  rw [reducedTermArithmetic1051, ← sound2754 B hB hF]
  change (-4946831880077574144000 : ℝ) * mixedMoment B node2754 node2754Labels =
    (37623398400 : ℝ) * (((-131482856160 : ℤ) : ℝ) * mixedMoment B node2754 node2754Labels + 0)
  ring

theorem reducedTermEval1052 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1052 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1052 (originalVector B) := by
  rw [reducedTermArithmetic1052, ← sound2755 B hB hF]
  change (757011477946171392000 : ℝ) * mixedMoment B node2755 node2755Labels =
    (37623398400 : ℝ) * ((20120762880 : ℝ) * mixedMoment B node2755 node2755Labels + 0)
  ring

theorem reducedTermEval1053 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1053 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1053 (originalVector B) := by
  rw [reducedTermArithmetic1053, ← sound2758 B hB hF]
  change (-8092322011089469440000 : ℝ) * mixedMoment B node2758 node2758Labels =
    (37623398400 : ℝ) * (((-215087481600 : ℤ) : ℝ) * mixedMoment B node2758 node2758Labels + 0)
  ring

theorem reducedTermEval1054 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1054 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1054 (originalVector B) := by
  rw [reducedTermArithmetic1054, ← sound2759 B hB hF]
  change (-7444916811245813760000 : ℝ) * mixedMoment B node2759 node2759Labels =
    (37623398400 : ℝ) * (((-197879966400 : ℤ) : ℝ) * mixedMoment B node2759 node2759Labels + 0)
  ring

theorem reducedTermEval1055 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1055 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1055 (originalVector B) := by
  rw [reducedTermArithmetic1055, ← sound2760 B hB hF]
  change (-416428679821787136000 : ℝ) * mixedMoment B node2760 node2760Labels =
    (37623398400 : ℝ) * (((-11068343040 : ℤ) : ℝ) * mixedMoment B node2760 node2760Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1017 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1017 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1017 (originalVector B) := by
  rw [reducedMerge1017Check, Integer.Sparse.eval_mergeBy, reducedTermEval1020 B hB hF, reducedTermEval1021 B hB hF]
  rw [originalMerge1017, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1018 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1018 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1018 (originalVector B) := by
  rw [reducedMerge1018Check, Integer.Sparse.eval_mergeBy, reducedTermEval1019 B hB hF, reducedMergeEval1017 B hB hF]
  rw [originalMerge1018, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1019 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1019 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1019 (originalVector B) := by
  rw [reducedMerge1019Check, Integer.Sparse.eval_mergeBy, reducedTermEval1022 B hB hF, reducedTermEval1023 B hB hF]
  rw [originalMerge1019, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1020 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1020 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1020 (originalVector B) := by
  rw [reducedMerge1020Check, Integer.Sparse.eval_mergeBy, reducedTermEval1024 B hB hF, reducedTermEval1025 B hB hF]
  rw [originalMerge1020, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1021 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1021 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1021 (originalVector B) := by
  rw [reducedMerge1021Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1019 B hB hF, reducedMergeEval1020 B hB hF]
  rw [originalMerge1021, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1022 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1022 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1022 (originalVector B) := by
  rw [reducedMerge1022Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1018 B hB hF, reducedMergeEval1021 B hB hF]
  rw [originalMerge1022, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1023 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1023 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1023 (originalVector B) := by
  rw [reducedMerge1023Check, Integer.Sparse.eval_mergeBy, reducedTermEval1026 B hB hF, reducedTermEval1027 B hB hF]
  rw [originalMerge1023, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1056 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1056 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1056 (originalVector B) := by
  rw [reducedTermArithmetic1056, ← sound2761 B hB hF]
  change (-1016042941450027008000 : ℝ) * mixedMoment B node2761 node2761Labels =
    (37623398400 : ℝ) * (((-27005613120 : ℤ) : ℝ) * mixedMoment B node2761 node2761Labels + 0)
  ring

theorem reducedTermEval1057 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1057 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1057 (originalVector B) := by
  rw [reducedTermArithmetic1057, ← sound2763 B hB hF]
  change (-21955095856769531904000 : ℝ) * mixedMoment B node2763 node2763Labels =
    (37623398400 : ℝ) * (((-583548982560 : ℤ) : ℝ) * mixedMoment B node2763 node2763Labels + 0)
  ring

theorem reducedTermEval1058 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1058 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1058 (originalVector B) := by
  rw [reducedTermArithmetic1058, ← sound2764 B hB hF]
  change (-23846279734862807040000 : ℝ) * mixedMoment B node2764 node2764Labels =
    (37623398400 : ℝ) * (((-633815145600 : ℤ) : ℝ) * mixedMoment B node2764 node2764Labels + 0)
  ring

theorem reducedTermEval1059 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1059 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1059 (originalVector B) := by
  rw [reducedTermArithmetic1059, ← sound2765 B hB hF]
  change (9533108969263595520000 : ℝ) * mixedMoment B node2765 node2765Labels =
    (37623398400 : ℝ) * ((253382452800 : ℝ) * mixedMoment B node2765 node2765Labels + 0)
  ring

theorem reducedTermEval1060 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1060 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1060 (originalVector B) := by
  rw [reducedTermArithmetic1060, ← sound2769 B hB hF]
  change (-22778979783065468928000 : ℝ) * mixedMoment B node2769 node2769Labels =
    (37623398400 : ℝ) * (((-605447161920 : ℤ) : ℝ) * mixedMoment B node2769 node2769Labels + 0)
  ring

theorem reducedTermEval1061 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1061 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1061 (originalVector B) := by
  rw [reducedTermArithmetic1061, ← sound2771 B hB hF]
  change (-1080639818309173248000 : ℝ) * mixedMoment B node2771 node2771Labels =
    (37623398400 : ℝ) * (((-28722546720 : ℤ) : ℝ) * mixedMoment B node2771 node2771Labels + 0)
  ring

theorem reducedTermEval1062 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1062 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1062 (originalVector B) := by
  rw [reducedTermArithmetic1062, ← sound2773 B hB hF]
  change (-7680684652994691072000 : ℝ) * mixedMoment B node2773 node2773Labels =
    (37623398400 : ℝ) * (((-204146488080 : ℤ) : ℝ) * mixedMoment B node2773 node2773Labels + 0)
  ring

theorem reducedTermEval1063 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1063 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1063 (originalVector B) := by
  rw [reducedTermArithmetic1063, ← sound2774 B hB hF]
  change (4689897337119375360000 : ℝ) * mixedMoment B node2774 node2774Labels =
    (37623398400 : ℝ) * ((124653740400 : ℝ) * mixedMoment B node2774 node2774Labels + 0)
  ring

theorem reducedTermEval1064 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1064 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1064 (originalVector B) := by
  rw [reducedTermArithmetic1064, ← sound2775 B hB hF]
  change (-563280397683720192000 : ℝ) * mixedMoment B node2775 node2775Labels =
    (37623398400 : ℝ) * (((-14971544880 : ℤ) : ℝ) * mixedMoment B node2775 node2775Labels + 0)
  ring

theorem reducedTermEval1065 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1065 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1065 (originalVector B) := by
  rw [reducedTermArithmetic1065, ← sound2776 B hB hF]
  change (-3710011026318557184000 : ℝ) * mixedMoment B node2776 node2776Labels =
    (37623398400 : ℝ) * (((-98609141760 : ℤ) : ℝ) * mixedMoment B node2776 node2776Labels + 0)
  ring

theorem reducedTermEval1066 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1066 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1066 (originalVector B) := by
  rw [reducedTermArithmetic1066, ← sound2777 B hB hF]
  change (-4714450911702024192000 : ℝ) * mixedMoment B node2777 node2777Labels =
    (37623398400 : ℝ) * (((-125306354880 : ℤ) : ℝ) * mixedMoment B node2777 node2777Labels + 0)
  ring

theorem reducedTermEval1067 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1067 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1067 (originalVector B) := by
  rw [reducedTermArithmetic1067, ← sound2778 B hB hF]
  change (-1215313374856347648000 : ℝ) * mixedMoment B node2778 node2778Labels =
    (37623398400 : ℝ) * (((-32302062720 : ℤ) : ℝ) * mixedMoment B node2778 node2778Labels + 0)
  ring

theorem reducedTermEval1068 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1068 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1068 (originalVector B) := by
  rw [reducedTermArithmetic1068, ← sound2779 B hB hF]
  change (1029413887898812416000 : ℝ) * mixedMoment B node2779 node2779Labels =
    (37623398400 : ℝ) * ((27361002240 : ℝ) * mixedMoment B node2779 node2779Labels + 0)
  ring

theorem reducedTermEval1069 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1069 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1069 (originalVector B) := by
  rw [reducedTermArithmetic1069, ← sound2780 B hB hF]
  change (-218973289450438656000 : ℝ) * mixedMoment B node2780 node2780Labels =
    (37623398400 : ℝ) * (((-5820135840 : ℤ) : ℝ) * mixedMoment B node2780 node2780Labels + 0)
  ring

theorem reducedTermEval1070 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1070 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1070 (originalVector B) := by
  rw [reducedTermArithmetic1070, ← sound2781 B hB hF]
  change (-9759313319373176832000 : ℝ) * mixedMoment B node2781 node2781Labels =
    (37623398400 : ℝ) * (((-259394784480 : ℤ) : ℝ) * mixedMoment B node2781 node2781Labels + 0)
  ring

theorem reducedTermEval1071 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1071 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1071 (originalVector B) := by
  rw [reducedTermArithmetic1071, ← sound2782 B hB hF]
  change (-28741157247379046400000 : ℝ) * mixedMoment B node2782 node2782Labels =
    (37623398400 : ℝ) * (((-763917096000 : ℤ) : ℝ) * mixedMoment B node2782 node2782Labels + 0)
  ring

theorem reducedTermEval1072 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1072 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1072 (originalVector B) := by
  rw [reducedTermArithmetic1072, ← sound2783 B hB hF]
  change (-12330745384768634880000 : ℝ) * mixedMoment B node2783 node2783Labels =
    (37623398400 : ℝ) * (((-327741403200 : ℤ) : ℝ) * mixedMoment B node2783 node2783Labels + 0)
  ring

theorem reducedTermEval1073 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1073 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1073 (originalVector B) := by
  rw [reducedTermArithmetic1073, ← sound2789 B hB hF]
  change (-13743886838351265792000 : ℝ) * mixedMoment B node2789 node2789Labels =
    (37623398400 : ℝ) * (((-365301578880 : ℤ) : ℝ) * mixedMoment B node2789 node2789Labels + 0)
  ring

theorem reducedTermEval1074 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1074 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1074 (originalVector B) := by
  rw [reducedTermArithmetic1074, ← sound2797 B hB hF]
  change (10817029381629542400000 : ℝ) * mixedMoment B node2797 node2797Labels =
    (37623398400 : ℝ) * ((287508036000 : ℝ) * mixedMoment B node2797 node2797Labels + 0)
  ring

theorem reducedTermEval1075 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1075 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1075 (originalVector B) := by
  rw [reducedTermArithmetic1075, ← sound2798 B hB hF]
  change (-6752922376232632320000 : ℝ) * mixedMoment B node2798 node2798Labels =
    (37623398400 : ℝ) * (((-179487304800 : ℤ) : ℝ) * mixedMoment B node2798 node2798Labels + 0)
  ring

theorem reducedTermEval1076 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1076 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1076 (originalVector B) := by
  rw [reducedTermArithmetic1076, ← sound2800 B hB hF]
  change (-3995973679581757440000 : ℝ) * mixedMoment B node2800 node2800Labels =
    (37623398400 : ℝ) * (((-106209801600 : ℤ) : ℝ) * mixedMoment B node2800 node2800Labels + 0)
  ring

theorem reducedTermEval1077 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1077 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1077 (originalVector B) := by
  rw [reducedTermArithmetic1077, ← sound2801 B hB hF]
  change (-1340821167243264000000 : ℝ) * mixedMoment B node2801 node2801Labels =
    (37623398400 : ℝ) * (((-35637960000 : ℤ) : ℝ) * mixedMoment B node2801 node2801Labels + 0)
  ring

theorem reducedTermEval1078 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1078 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1078 (originalVector B) := by
  rw [reducedTermArithmetic1078, ← sound2802 B hB hF]
  change (4806257162718412800000 : ℝ) * mixedMoment B node2802 node2802Labels =
    (37623398400 : ℝ) * ((127746492000 : ℝ) * mixedMoment B node2802 node2802Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1024 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1024 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1024 (originalVector B) := by
  rw [reducedMerge1024Check, Integer.Sparse.eval_mergeBy, reducedTermEval1028 B hB hF, reducedTermEval1029 B hB hF]
  rw [originalMerge1024, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1025 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1025 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1025 (originalVector B) := by
  rw [reducedMerge1025Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1023 B hB hF, reducedMergeEval1024 B hB hF]
  rw [originalMerge1025, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1026 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1026 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1026 (originalVector B) := by
  rw [reducedMerge1026Check, Integer.Sparse.eval_mergeBy, reducedTermEval1030 B hB hF, reducedTermEval1031 B hB hF]
  rw [originalMerge1026, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1027 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1027 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1027 (originalVector B) := by
  rw [reducedMerge1027Check, Integer.Sparse.eval_mergeBy, reducedTermEval1032 B hB hF, reducedTermEval1033 B hB hF]
  rw [originalMerge1027, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1028 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1028 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1028 (originalVector B) := by
  rw [reducedMerge1028Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1026 B hB hF, reducedMergeEval1027 B hB hF]
  rw [originalMerge1028, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1029 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1029 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1029 (originalVector B) := by
  rw [reducedMerge1029Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1025 B hB hF, reducedMergeEval1028 B hB hF]
  rw [originalMerge1029, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1030 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1030 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1030 (originalVector B) := by
  rw [reducedMerge1030Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1022 B hB hF, reducedMergeEval1029 B hB hF]
  rw [originalMerge1030, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1031 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1031 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1031 (originalVector B) := by
  rw [reducedMerge1031Check, Integer.Sparse.eval_mergeBy, reducedTermEval1035 B hB hF, reducedTermEval1036 B hB hF]
  rw [originalMerge1031, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1032 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1032 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1032 (originalVector B) := by
  rw [reducedMerge1032Check, Integer.Sparse.eval_mergeBy, reducedTermEval1034 B hB hF, reducedMergeEval1031 B hB hF]
  rw [originalMerge1032, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1033 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1033 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1033 (originalVector B) := by
  rw [reducedMerge1033Check, Integer.Sparse.eval_mergeBy, reducedTermEval1037 B hB hF, reducedTermEval1038 B hB hF]
  rw [originalMerge1033, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1034 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1034 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1034 (originalVector B) := by
  rw [reducedMerge1034Check, Integer.Sparse.eval_mergeBy, reducedTermEval1039 B hB hF, reducedTermEval1040 B hB hF]
  rw [originalMerge1034, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1035 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1035 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1035 (originalVector B) := by
  rw [reducedMerge1035Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1033 B hB hF, reducedMergeEval1034 B hB hF]
  rw [originalMerge1035, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1036 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1036 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1036 (originalVector B) := by
  rw [reducedMerge1036Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1032 B hB hF, reducedMergeEval1035 B hB hF]
  rw [originalMerge1036, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1037 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1037 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1037 (originalVector B) := by
  rw [reducedMerge1037Check, Integer.Sparse.eval_mergeBy, reducedTermEval1041 B hB hF, reducedTermEval1042 B hB hF]
  rw [originalMerge1037, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1038 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1038 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1038 (originalVector B) := by
  rw [reducedMerge1038Check, Integer.Sparse.eval_mergeBy, reducedTermEval1043 B hB hF, reducedTermEval1044 B hB hF]
  rw [originalMerge1038, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1039 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1039 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1039 (originalVector B) := by
  rw [reducedMerge1039Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1037 B hB hF, reducedMergeEval1038 B hB hF]
  rw [originalMerge1039, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1040 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1040 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1040 (originalVector B) := by
  rw [reducedMerge1040Check, Integer.Sparse.eval_mergeBy, reducedTermEval1045 B hB hF, reducedTermEval1046 B hB hF]
  rw [originalMerge1040, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1041 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1041 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1041 (originalVector B) := by
  rw [reducedMerge1041Check, Integer.Sparse.eval_mergeBy, reducedTermEval1047 B hB hF, reducedTermEval1048 B hB hF]
  rw [originalMerge1041, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1042 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1042 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1042 (originalVector B) := by
  rw [reducedMerge1042Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1040 B hB hF, reducedMergeEval1041 B hB hF]
  rw [originalMerge1042, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1043 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1043 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1043 (originalVector B) := by
  rw [reducedMerge1043Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1039 B hB hF, reducedMergeEval1042 B hB hF]
  rw [originalMerge1043, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1044 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1044 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1044 (originalVector B) := by
  rw [reducedMerge1044Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1036 B hB hF, reducedMergeEval1043 B hB hF]
  rw [originalMerge1044, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1045 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1045 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1045 (originalVector B) := by
  rw [reducedMerge1045Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1030 B hB hF, reducedMergeEval1044 B hB hF]
  rw [originalMerge1045, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1046 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1046 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1046 (originalVector B) := by
  rw [reducedMerge1046Check, Integer.Sparse.eval_mergeBy, reducedTermEval1050 B hB hF, reducedTermEval1051 B hB hF]
  rw [originalMerge1046, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1047 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1047 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1047 (originalVector B) := by
  rw [reducedMerge1047Check, Integer.Sparse.eval_mergeBy, reducedTermEval1049 B hB hF, reducedMergeEval1046 B hB hF]
  rw [originalMerge1047, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1048 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1048 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1048 (originalVector B) := by
  rw [reducedMerge1048Check, Integer.Sparse.eval_mergeBy, reducedTermEval1052 B hB hF, reducedTermEval1053 B hB hF]
  rw [originalMerge1048, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1049 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1049 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1049 (originalVector B) := by
  rw [reducedMerge1049Check, Integer.Sparse.eval_mergeBy, reducedTermEval1054 B hB hF, reducedTermEval1055 B hB hF]
  rw [originalMerge1049, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1050 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1050 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1050 (originalVector B) := by
  rw [reducedMerge1050Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1048 B hB hF, reducedMergeEval1049 B hB hF]
  rw [originalMerge1050, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1051 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1051 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1051 (originalVector B) := by
  rw [reducedMerge1051Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1047 B hB hF, reducedMergeEval1050 B hB hF]
  rw [originalMerge1051, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1052 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1052 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1052 (originalVector B) := by
  rw [reducedMerge1052Check, Integer.Sparse.eval_mergeBy, reducedTermEval1056 B hB hF, reducedTermEval1057 B hB hF]
  rw [originalMerge1052, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1053 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1053 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1053 (originalVector B) := by
  rw [reducedMerge1053Check, Integer.Sparse.eval_mergeBy, reducedTermEval1058 B hB hF, reducedTermEval1059 B hB hF]
  rw [originalMerge1053, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1054 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1054 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1054 (originalVector B) := by
  rw [reducedMerge1054Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1052 B hB hF, reducedMergeEval1053 B hB hF]
  rw [originalMerge1054, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1055 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1055 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1055 (originalVector B) := by
  rw [reducedMerge1055Check, Integer.Sparse.eval_mergeBy, reducedTermEval1060 B hB hF, reducedTermEval1061 B hB hF]
  rw [originalMerge1055, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1056 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1056 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1056 (originalVector B) := by
  rw [reducedMerge1056Check, Integer.Sparse.eval_mergeBy, reducedTermEval1062 B hB hF, reducedTermEval1063 B hB hF]
  rw [originalMerge1056, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1057 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1057 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1057 (originalVector B) := by
  rw [reducedMerge1057Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1055 B hB hF, reducedMergeEval1056 B hB hF]
  rw [originalMerge1057, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1058 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1058 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1058 (originalVector B) := by
  rw [reducedMerge1058Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1054 B hB hF, reducedMergeEval1057 B hB hF]
  rw [originalMerge1058, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1059 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1059 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1059 (originalVector B) := by
  rw [reducedMerge1059Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1051 B hB hF, reducedMergeEval1058 B hB hF]
  rw [originalMerge1059, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1060 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1060 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1060 (originalVector B) := by
  rw [reducedMerge1060Check, Integer.Sparse.eval_mergeBy, reducedTermEval1065 B hB hF, reducedTermEval1066 B hB hF]
  rw [originalMerge1060, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1061 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1061 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1061 (originalVector B) := by
  rw [reducedMerge1061Check, Integer.Sparse.eval_mergeBy, reducedTermEval1064 B hB hF, reducedMergeEval1060 B hB hF]
  rw [originalMerge1061, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1062 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1062 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1062 (originalVector B) := by
  rw [reducedMerge1062Check, Integer.Sparse.eval_mergeBy, reducedTermEval1067 B hB hF, reducedTermEval1068 B hB hF]
  rw [originalMerge1062, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1063 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1063 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1063 (originalVector B) := by
  rw [reducedMerge1063Check, Integer.Sparse.eval_mergeBy, reducedTermEval1069 B hB hF, reducedTermEval1070 B hB hF]
  rw [originalMerge1063, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1064 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1064 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1064 (originalVector B) := by
  rw [reducedMerge1064Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1062 B hB hF, reducedMergeEval1063 B hB hF]
  rw [originalMerge1064, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1065 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1065 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1065 (originalVector B) := by
  rw [reducedMerge1065Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1061 B hB hF, reducedMergeEval1064 B hB hF]
  rw [originalMerge1065, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1066 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1066 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1066 (originalVector B) := by
  rw [reducedMerge1066Check, Integer.Sparse.eval_mergeBy, reducedTermEval1071 B hB hF, reducedTermEval1072 B hB hF]
  rw [originalMerge1066, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1067 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1067 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1067 (originalVector B) := by
  rw [reducedMerge1067Check, Integer.Sparse.eval_mergeBy, reducedTermEval1073 B hB hF, reducedTermEval1074 B hB hF]
  rw [originalMerge1067, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1068 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1068 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1068 (originalVector B) := by
  rw [reducedMerge1068Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1066 B hB hF, reducedMergeEval1067 B hB hF]
  rw [originalMerge1068, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1069 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1069 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1069 (originalVector B) := by
  rw [reducedMerge1069Check, Integer.Sparse.eval_mergeBy, reducedTermEval1075 B hB hF, reducedTermEval1076 B hB hF]
  rw [originalMerge1069, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1070 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1070 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1070 (originalVector B) := by
  rw [reducedMerge1070Check, Integer.Sparse.eval_mergeBy, reducedTermEval1077 B hB hF, reducedTermEval1078 B hB hF]
  rw [originalMerge1070, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1071 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1071 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1071 (originalVector B) := by
  rw [reducedMerge1071Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1069 B hB hF, reducedMergeEval1070 B hB hF]
  rw [originalMerge1071, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1072 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1072 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1072 (originalVector B) := by
  rw [reducedMerge1072Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1068 B hB hF, reducedMergeEval1071 B hB hF]
  rw [originalMerge1072, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1073 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1073 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1073 (originalVector B) := by
  rw [reducedMerge1073Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1065 B hB hF, reducedMergeEval1072 B hB hF]
  rw [originalMerge1073, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1074 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1074 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1074 (originalVector B) := by
  rw [reducedMerge1074Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1059 B hB hF, reducedMergeEval1073 B hB hF]
  rw [originalMerge1074, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1075_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1075 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1075 (originalVector B) := by
  rw [reducedMerge1075Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1045 B hB hF, reducedMergeEval1074 B hB hF]
  rw [originalMerge1075, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1075_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1075_e_oai
