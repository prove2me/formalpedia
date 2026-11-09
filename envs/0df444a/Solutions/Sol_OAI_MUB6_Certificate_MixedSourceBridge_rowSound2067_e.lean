-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2067_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:58:43.780754+00:00
-- url     : https://prove2.me/submissions/e8dd98e1-9a9b-4536-afaa-dd5196f22769

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E109
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170

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

theorem transition_cross_normSq {m : ℕ} (B : Fin m → Basis) (hB : IsMUBFamily B)
    (ref : Basis) (s t : Fin m) (hst : s ≠ t) (k l : Coord) :
    Complex.normSq (∑ i, conj (transition ref (B s) i k) * transition ref (B t) i l) = 6 := by
  rw [transition_column_inner, map_mul, hB s t hst k l]
  norm_num [Complex.normSq_ofNat]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_OffDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem offDiagSum_add_diag {V : Type*} [AddCommMonoid V] (f : Coord → Coord → V) :
    offDiagSum f + (∑ i, f i i) = ∑ i, ∑ j, f i j := by
  rw [offDiagSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_erase_add _ _ (Finset.mem_univ i)

theorem offDiagSum_sum {V ι : Type*} [AddCommMonoid V] [Fintype ι]
    (f : Coord → Coord → ι → V) :
    offDiagSum (fun i j => ∑ k, f i j k) =
      ∑ k, offDiagSum (fun i j => f i j k) := by
  unfold offDiagSum
  calc
    _ = ∑ i, ∑ k, ∑ j ∈ Finset.univ.erase i, f i j k := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

theorem offDiagSum_mul (c : ℂ) (f : Coord → Coord → ℂ) :
    offDiagSum (fun i j => c * f i j) = c * offDiagSum f := by
  simp only [offDiagSum, Finset.mul_sum]

theorem sum_mul_conj (z : Coord → ℂ) :
    (∑ i, ∑ j, z i * conj (z j)) = (Complex.normSq (∑ i, z i) : ℂ) := by
  rw [← Complex.mul_conj, map_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_DifferentMatrices
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem difference_reverse (i j : Coord) : difference j i = -difference i j := by
  simp [difference, neg_sub]

theorem cross_character_gram (x y : Coord → ℂ)
    (hx : ∀ i, Complex.normSq (x i) = 1) (hy : ∀ i, Complex.normSq (y i) = 1) :
    (∑ i, ∑ j, character x (difference i j) * character y (-difference i j)) =
      (Complex.normSq (∑ i, x i * conj (y i)) : ℂ) := by
  rw [← sum_mul_conj]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [character_neg y hy, character_difference x hx, character_difference y hy]
  simp only [map_mul, starRingEnd_apply, star_star]
  ring

theorem cross_character_offdiag (x y : Coord → ℂ)
    (hx : ∀ i, Complex.normSq (x i) = 1) (hy : ∀ i, Complex.normSq (y i) = 1)
    (hc : Complex.normSq (∑ i, x i * conj (y i)) = 6) :
    offDiagSum (fun i j => character x (difference i j) * character y (-difference i j)) = 0 := by
  have h := offDiagSum_add_diag
    (fun i j => character x (difference i j) * character y (-difference i j))
  rw [cross_character_gram x y hx hy, hc] at h
  have hd : (∑ i, character x (difference i i) * character y (-difference i i)) = (6 : ℂ) := by
    simp [difference]
  rw [hd] at h
  exact add_right_cancel (show _ + (6 : ℂ) = 0 + 6 by simpa using h)

theorem weighted_cross_character (x y : Coord → ℂ)
    (hx : ∀ i, Complex.normSq (x i) = 1) (hy : ∀ i, Complex.normSq (y i) = 1)
    (hc : Complex.normSq (∑ i, x i * conj (y i)) = 6) (a b : Charge) :
    offDiagSum (fun i j =>
      character x (a + difference i j) * character y (b + difference j i)) = 0 := by
  have he (i j : Coord) :
      character x (a + difference i j) * character y (b + difference j i) =
        (character x a * character y b) *
          (character x (difference i j) * character y (-difference i j)) := by
    rw [character_add x (fun i => unit_ne_zero (hx i)),
      character_add y (fun i => unit_ne_zero (hy i)), difference_reverse j i]
    ring_nf
  simp_rw [he]
  rw [offDiagSum_mul, cross_character_offdiag x y hx hy hc, mul_zero]

theorem g_product_expand (H K : CMatrix) (a b : Charge) :
    g H a * g K b = (6 : ℂ)⁻¹ * (6 : ℂ)⁻¹ *
      ∑ k, ∑ l, character (fun i => H i k) a * character (fun i => K i l) b := by
  unfold g
  calc
    _ = (6 : ℂ)⁻¹ * (6 : ℂ)⁻¹ *
      ((∑ k, character (fun i => H i k) a) * ∑ l, character (fun i => K i l) b) := by ring
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm

/-- The different-matrix Fourier identity from unbiasedness of every pair of
columns. The off-diagonal indexing lists each difference `e_i-e_j` once. -/
theorem different_matrices_identity {H K : CMatrix} (hH : IsHadamard H) (hK : IsHadamard K)
    (hc : ∀ k l, Complex.normSq (∑ i, H i k * conj (K i l)) = 6) (a b : Charge) :
    offDiagSum (fun i j => g H (a + difference i j) * g K (b + difference j i)) = 0 := by
  simp_rw [g_product_expand]
  rw [offDiagSum_mul, offDiagSum_sum]
  simp_rw [offDiagSum_sum]
  have hz : (∑ k, ∑ l, offDiagSum (fun i j =>
      character (fun r => H r k) (a + difference i j) *
        character (fun r => K r l) (b + difference j i))) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro l _
    exact weighted_cross_character _ _ (fun i => hH.1 i k) (fun i => hK.1 i l) (hc k l) a b
  rw [hz, mul_zero]

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

theorem relativeMatrix_cross (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (s t : Coord) (hst : s ≠ t) (k l : Coord) :
    Complex.normSq (∑ i, relativeMatrix B r s i k * conj (relativeMatrix B r t i l)) = 6 := by
  have ht : r.succAbove t ≠ r.succAbove s := by
    intro h
    exact hst (Fin.succAbove_right_injective h.symm)
  simpa only [relativeMatrix, mul_comm] using
    transition_cross_normSq B hB (B r) (r.succAbove t) (r.succAbove s) ht l k

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Equivalence
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem IsHadamard.permutations {H : CMatrix} (hH : IsHadamard H)
    (r c : Equiv.Perm Coord) : IsHadamard (fun i j => H (r i) (c j)) := by
  refine ⟨fun i j => hH.1 _ _, ?_⟩
  ext i j
  change (∑ k, conj (H (r k) (c i)) * H (r k) (c j)) =
    (6 : ℂ) * (if i = j then 1 else 0)
  rw [Equiv.sum_comp r (fun k => conj (H k (c i)) * H k (c j)), hH.column_orthogonal]
  simp only [Equiv.apply_eq_iff_eq]
  split_ifs <;> norm_num

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedShifts
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem sampledMatrix_isHadamard (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (ρ : Coord ↪ Coord) (s : Coord) : IsHadamard (sampledMatrix B r ρ s) := by
  let e : Equiv.Perm Coord := Equiv.ofBijective ρ
    ⟨ρ.injective, Finite.surjective_of_injective ρ.injective⟩
  exact (relativeMatrix_isHadamard B hB r s).permutations e (Equiv.refl Coord)

theorem sampledMatrix_cross (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (ρ : Coord ↪ Coord) (s t : Coord) (hst : s ≠ t) (k l : Coord) :
    Complex.normSq (∑ i, sampledMatrix B r ρ s i k * conj (sampledMatrix B r ρ t i l)) = 6 := by
  let e : Equiv.Perm Coord := Equiv.ofBijective ρ
    ⟨ρ.injective, Finite.surjective_of_injective ρ.injective⟩
  change Complex.normSq (∑ i, relativeMatrix B r s (e i) k * conj (relativeMatrix B r t (e i) l)) = 6
  rw [Equiv.sum_comp e (fun i => relativeMatrix B r s i k * conj (relativeMatrix B r t i l))]
  exact relativeMatrix_cross B hB r s t hst k l

theorem mixedIntegrand_three {l : ℕ} (B : Fin 7 → Basis) (a b c : Charge)
    (s t u : Fin l) (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
    mixedIntegrand B (tripleCharges a b c) ![s, t, u] r ρ τ =
      g (sampledMatrix B r ρ (τ s)) a * g (sampledMatrix B r ρ (τ t)) b *
        g (sampledMatrix B r ρ (τ u)) c := by
  simp [mixedIntegrand, tripleCharges, Fin.prod_univ_succ, rowFourier, g, character,
    sampledMatrix, mul_assoc]

theorem average_finset_sum {ι κ : Type*} [Fintype ι] (s : Finset κ) (f : ι → κ → ℝ) :
    average (fun i => ∑ k ∈ s, f i k) = ∑ k ∈ s, average (fun i => f i k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih => simp only [Finset.sum_insert hk, average_add, ih]

theorem average_offDiagSum {ι : Type*} [Fintype ι] (f : ι → Coord → Coord → ℝ) :
    average (fun k => offDiagSum (f k)) = offDiagSum (fun i j => average (fun k => f k i j)) := by
  simp only [offDiagSum, average_sum, average_finset_sum]

theorem mixedMoment_different {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s t u : Fin l) (hst : s ≠ t) :
    offDiagSum (fun i j =>
      mixedMoment B (tripleCharges (a + difference i j) (b + difference j i) c) ![s, t, u]) = 0 := by
  simp only [mixedMoment, ← average_offDiagSum]
  have hz (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
      offDiagSum (fun i j =>
        (mixedIntegrand B (tripleCharges (a + difference i j) (b + difference j i) c)
          ![s, t, u] r ρ τ).re) = 0 := by
    simp only [mixedIntegrand_three, offDiagSum, ← Complex.re_sum, ← Finset.sum_mul]
    change (offDiagSum (fun i j =>
      g (sampledMatrix B r ρ (τ s)) (a + difference i j) *
        g (sampledMatrix B r ρ (τ t)) (b + difference j i)) *
          g (sampledMatrix B r ρ (τ u)) c).re = 0
    rw [different_matrices_identity (sampledMatrix_isHadamard B hB r ρ _)
      (sampledMatrix_isHadamard B hB r ρ _)
      (sampledMatrix_cross B hB r ρ _ _ (fun h => hst (τ.injective h))) a b]
    simp
  simp only [hz, average_zero]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical145
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18573 raw18573Labels = mixedMoment B node5427 node5427Labels := by
  calc
    mixedMoment B raw18573 raw18573Labels = mixedMoment B raw18573step0 raw18573step0Labels := by
      have ha : raw18573step0 = (fun i j => raw18573 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18573step0 raw18573; decide +kernel
      have hl : raw18573step0Labels = raw18573Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18573 raw18573Labels permutation265 permutation2
    _ = mixedMoment B node5427 node5427Labels := by rfl

theorem canonical18584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18584 raw18584Labels = mixedMoment B node5383 node5383Labels := by
  calc
    mixedMoment B raw18584 raw18584Labels = mixedMoment B raw18584step0 raw18584step0Labels := by
      have ha : raw18584step0 = (fun i j => raw18584 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18584step0 raw18584; decide +kernel
      have hl : raw18584step0Labels = raw18584Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18584 raw18584Labels permutation265 permutation2
    _ = mixedMoment B node5383 node5383Labels := by rfl

theorem canonical18589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18589 raw18589Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw18589 raw18589Labels = mixedMoment B raw18589step0 raw18589step0Labels := by
      have ha : raw18589step0 = (fun i j => raw18589 (permutation268 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18589step0 raw18589; decide +kernel
      have hl : raw18589step0Labels = raw18589Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18589 raw18589Labels permutation268 permutation2
    _ = mixedMoment B node5380 node5380Labels := by rfl

theorem canonical18594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18594 raw18594Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw18594 raw18594Labels = mixedMoment B raw18594step0 raw18594step0Labels := by
      have ha : raw18594step0 = (fun i j => raw18594 (permutation266 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18594step0 raw18594; decide +kernel
      have hl : raw18594step0Labels = raw18594Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18594 raw18594Labels permutation266 permutation2
    _ = mixedMoment B node5380 node5380Labels := by rfl

theorem canonical18598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18598 raw18598Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw18598 raw18598Labels = mixedMoment B raw18598step0 raw18598step0Labels := by
      have ha : raw18598step0 = (fun i j => raw18598 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18598step0 raw18598; decide +kernel
      have hl : raw18598step0Labels = raw18598Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18598 raw18598Labels permutation152 permutation3
    mixedMoment B raw18598step0 raw18598step0Labels = mixedMoment B raw18598step1 raw18598step1Labels := by
      have ha : raw18598step1 = raw18598step0 := by apply Matrix.ext; unfold raw18598step1 raw18598step0; decide +kernel
      have hl : raw18598step0Labels = labelEmbedding6 ∘ raw18598step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18598step0 raw18598step0Labels raw18598step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4851 node4851Labels := by rfl

theorem canonical18600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18600 raw18600Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw18600 raw18600Labels = mixedMoment B raw18600step0 raw18600step0Labels := by
      have ha : raw18600step0 = (fun i j => raw18600 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18600step0 raw18600; decide +kernel
      have hl : raw18600step0Labels = raw18600Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18600 raw18600Labels permutation176 permutation3
    mixedMoment B raw18600step0 raw18600step0Labels = mixedMoment B raw18600step1 raw18600step1Labels := by
      have ha : raw18600step1 = raw18600step0 := by apply Matrix.ext; unfold raw18600step1 raw18600step0; decide +kernel
      have hl : raw18600step0Labels = labelEmbedding6 ∘ raw18600step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18600step0 raw18600step0Labels raw18600step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

theorem canonical18601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18601 raw18601Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw18601 raw18601Labels = mixedMoment B raw18601step0 raw18601step0Labels := by
      have ha : raw18601step0 = (fun i j => raw18601 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18601step0 raw18601; decide +kernel
      have hl : raw18601step0Labels = raw18601Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18601 raw18601Labels permutation212 permutation5
    mixedMoment B raw18601step0 raw18601step0Labels = mixedMoment B raw18601step1 raw18601step1Labels := by
      have ha : raw18601step1 = -raw18601step0 := by apply Matrix.ext; change ∀ i j, raw18601step1 i j = -(raw18601step0 i j); unfold raw18601step1 raw18601step0; decide +kernel
      have hl : raw18601step1Labels = raw18601step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18601step1 raw18601step1Labels = mixedMoment B raw18601step2 raw18601step2Labels := by
      have ha : raw18601step2 = raw18601step1 := by apply Matrix.ext; unfold raw18601step2 raw18601step1; decide +kernel
      have hl : raw18601step1Labels = labelEmbedding8 ∘ raw18601step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18601step1 raw18601step1Labels raw18601step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical18602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18602 raw18602Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw18602 raw18602Labels = mixedMoment B raw18602step0 raw18602step0Labels := by
      have ha : raw18602step0 = (fun i j => raw18602 (permutation234 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18602step0 raw18602; decide +kernel
      have hl : raw18602step0Labels = raw18602Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18602 raw18602Labels permutation234 permutation5
    mixedMoment B raw18602step0 raw18602step0Labels = mixedMoment B raw18602step1 raw18602step1Labels := by
      have ha : raw18602step1 = -raw18602step0 := by apply Matrix.ext; change ∀ i j, raw18602step1 i j = -(raw18602step0 i j); unfold raw18602step1 raw18602step0; decide +kernel
      have hl : raw18602step1Labels = raw18602step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18602step1 raw18602step1Labels = mixedMoment B raw18602step2 raw18602step2Labels := by
      have ha : raw18602step2 = raw18602step1 := by apply Matrix.ext; unfold raw18602step2 raw18602step1; decide +kernel
      have hl : raw18602step1Labels = labelEmbedding8 ∘ raw18602step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18602step1 raw18602step1Labels raw18602step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2139 raw2139Labels = mixedMoment B node5114 node5114Labels := by
  calc
    mixedMoment B raw2139 raw2139Labels = mixedMoment B raw2139step0 raw2139step0Labels := by
      have ha : raw2139step0 = (fun i j => raw2139 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2139step0 raw2139; decide +kernel
      have hl : raw2139step0Labels = raw2139Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2139 raw2139Labels permutation152 permutation5
    mixedMoment B raw2139step0 raw2139step0Labels = mixedMoment B raw2139step1 raw2139step1Labels := by
      have ha : raw2139step1 = raw2139step0 := by apply Matrix.ext; unfold raw2139step1 raw2139step0; decide +kernel
      have hl : raw2139step0Labels = labelEmbedding8 ∘ raw2139step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2139step0 raw2139step0Labels raw2139step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5114 node5114Labels := by rfl

theorem canonical2140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2140 raw2140Labels = mixedMoment B node2896 node2896Labels := by
  calc
    mixedMoment B raw2140 raw2140Labels = mixedMoment B raw2140step0 raw2140step0Labels := by
      have ha : raw2140step0 = (fun i j => raw2140 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2140step0 raw2140; decide +kernel
      have hl : raw2140step0Labels = raw2140Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2140 raw2140Labels permutation153 permutation4
    _ = mixedMoment B node2896 node2896Labels := by rfl

theorem canonical2141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2141 raw2141Labels = mixedMoment B node3597 node3597Labels := by
  calc
    mixedMoment B raw2141 raw2141Labels = mixedMoment B raw2141step0 raw2141step0Labels := by
      have ha : raw2141step0 = (fun i j => raw2141 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2141step0 raw2141; decide +kernel
      have hl : raw2141step0Labels = raw2141Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2141 raw2141Labels permutation152 permutation3
    mixedMoment B raw2141step0 raw2141step0Labels = mixedMoment B raw2141step1 raw2141step1Labels := by
      have ha : raw2141step1 = -raw2141step0 := by apply Matrix.ext; change ∀ i j, raw2141step1 i j = -(raw2141step0 i j); unfold raw2141step1 raw2141step0; decide +kernel
      have hl : raw2141step1Labels = raw2141step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2141step1 raw2141step1Labels = mixedMoment B raw2141step2 raw2141step2Labels := by
      have ha : raw2141step2 = raw2141step1 := by apply Matrix.ext; unfold raw2141step2 raw2141step1; decide +kernel
      have hl : raw2141step1Labels = labelEmbedding1 ∘ raw2141step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2141step1 raw2141step1Labels raw2141step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3597 node3597Labels := by rfl

theorem canonical2166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2166 raw2166Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw2166 raw2166Labels = mixedMoment B raw2166step0 raw2166step0Labels := by
      have ha : raw2166step0 = (fun i j => raw2166 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2166step0 raw2166; decide +kernel
      have hl : raw2166step0Labels = raw2166Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2166 raw2166Labels permutation152 permutation4
    mixedMoment B raw2166step0 raw2166step0Labels = mixedMoment B raw2166step1 raw2166step1Labels := by
      have ha : raw2166step1 = raw2166step0 := by apply Matrix.ext; unfold raw2166step1 raw2166step0; decide +kernel
      have hl : raw2166step0Labels = labelEmbedding7 ∘ raw2166step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2166step0 raw2166step0Labels raw2166step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5137 node5137Labels := by rfl

theorem canonical2167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2167 raw2167Labels = mixedMoment B node2556 node2556Labels := by
  calc
    mixedMoment B raw2167 raw2167Labels = mixedMoment B raw2167step0 raw2167step0Labels := by
      have ha : raw2167step0 = (fun i j => raw2167 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2167step0 raw2167; decide +kernel
      have hl : raw2167step0Labels = raw2167Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2167 raw2167Labels permutation152 permutation4
    _ = mixedMoment B node2556 node2556Labels := by rfl

theorem canonical2168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2168 raw2168Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw2168 raw2168Labels = mixedMoment B raw2168step0 raw2168step0Labels := by
      have ha : raw2168step0 = (fun i j => raw2168 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2168step0 raw2168; decide +kernel
      have hl : raw2168step0Labels = raw2168Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2168 raw2168Labels permutation176 permutation6
    mixedMoment B raw2168step0 raw2168step0Labels = mixedMoment B raw2168step1 raw2168step1Labels := by
      have ha : raw2168step1 = -raw2168step0 := by apply Matrix.ext; change ∀ i j, raw2168step1 i j = -(raw2168step0 i j); unfold raw2168step1 raw2168step0; decide +kernel
      have hl : raw2168step1Labels = raw2168step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2168step1 raw2168step1Labels = mixedMoment B raw2168step2 raw2168step2Labels := by
      have ha : raw2168step2 = raw2168step1 := by apply Matrix.ext; unfold raw2168step2 raw2168step1; decide +kernel
      have hl : raw2168step1Labels = labelEmbedding1 ∘ raw2168step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2168step1 raw2168step1Labels raw2168step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3521 node3521Labels := by rfl

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

theorem canonical2424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2424 raw2424Labels = mixedMoment B node5373 node5373Labels := by
  calc
    mixedMoment B raw2424 raw2424Labels = mixedMoment B raw2424step0 raw2424step0Labels := by
      have ha : raw2424step0 = (fun i j => raw2424 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2424step0 raw2424; decide +kernel
      have hl : raw2424step0Labels = raw2424Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2424 raw2424Labels permutation152 permutation4
    mixedMoment B raw2424step0 raw2424step0Labels = mixedMoment B raw2424step1 raw2424step1Labels := by
      have ha : raw2424step1 = raw2424step0 := by apply Matrix.ext; unfold raw2424step1 raw2424step0; decide +kernel
      have hl : raw2424step0Labels = labelEmbedding7 ∘ raw2424step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2424step0 raw2424step0Labels raw2424step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5373 node5373Labels := by rfl

theorem canonical2425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2425 raw2425Labels = mixedMoment B node3709 node3709Labels := by
  calc
    mixedMoment B raw2425 raw2425Labels = mixedMoment B raw2425step0 raw2425step0Labels := by
      have ha : raw2425step0 = (fun i j => raw2425 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2425step0 raw2425; decide +kernel
      have hl : raw2425step0Labels = raw2425Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2425 raw2425Labels permutation152 permutation4
    _ = mixedMoment B node3709 node3709Labels := by rfl

theorem canonical2426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2426 raw2426Labels = mixedMoment B node3792 node3792Labels := by
  calc
    mixedMoment B raw2426 raw2426Labels = mixedMoment B raw2426step0 raw2426step0Labels := by
      have ha : raw2426step0 = (fun i j => raw2426 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2426step0 raw2426; decide +kernel
      have hl : raw2426step0Labels = raw2426Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2426 raw2426Labels permutation176 permutation6
    mixedMoment B raw2426step0 raw2426step0Labels = mixedMoment B raw2426step1 raw2426step1Labels := by
      have ha : raw2426step1 = -raw2426step0 := by apply Matrix.ext; change ∀ i j, raw2426step1 i j = -(raw2426step0 i j); unfold raw2426step1 raw2426step0; decide +kernel
      have hl : raw2426step1Labels = raw2426step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2426step1 raw2426step1Labels = mixedMoment B raw2426step2 raw2426step2Labels := by
      have ha : raw2426step2 = raw2426step1 := by apply Matrix.ext; unfold raw2426step2 raw2426step1; decide +kernel
      have hl : raw2426step1Labels = labelEmbedding1 ∘ raw2426step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2426step1 raw2426step1Labels raw2426step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3792 node3792Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2433 raw2433Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw2433 raw2433Labels = mixedMoment B raw2433step0 raw2433step0Labels := by
      have ha : raw2433step0 = (fun i j => raw2433 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2433step0 raw2433; decide +kernel
      have hl : raw2433step0Labels = raw2433Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2433 raw2433Labels permutation152 permutation4
    mixedMoment B raw2433step0 raw2433step0Labels = mixedMoment B raw2433step1 raw2433step1Labels := by
      have ha : raw2433step1 = raw2433step0 := by apply Matrix.ext; unfold raw2433step1 raw2433step0; decide +kernel
      have hl : raw2433step0Labels = labelEmbedding7 ∘ raw2433step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2433step0 raw2433step0Labels raw2433step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5380 node5380Labels := by rfl

theorem canonical2434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2434 raw2434Labels = mixedMoment B node3721 node3721Labels := by
  calc
    mixedMoment B raw2434 raw2434Labels = mixedMoment B raw2434step0 raw2434step0Labels := by
      have ha : raw2434step0 = (fun i j => raw2434 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2434step0 raw2434; decide +kernel
      have hl : raw2434step0Labels = raw2434Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2434 raw2434Labels permutation152 permutation4
    _ = mixedMoment B node3721 node3721Labels := by rfl

theorem canonical2435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2435 raw2435Labels = mixedMoment B node3836 node3836Labels := by
  calc
    mixedMoment B raw2435 raw2435Labels = mixedMoment B raw2435step0 raw2435step0Labels := by
      have ha : raw2435step0 = (fun i j => raw2435 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2435step0 raw2435; decide +kernel
      have hl : raw2435step0Labels = raw2435Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2435 raw2435Labels permutation176 permutation6
    mixedMoment B raw2435step0 raw2435step0Labels = mixedMoment B raw2435step1 raw2435step1Labels := by
      have ha : raw2435step1 = -raw2435step0 := by apply Matrix.ext; change ∀ i j, raw2435step1 i j = -(raw2435step0 i j); unfold raw2435step1 raw2435step0; decide +kernel
      have hl : raw2435step1Labels = raw2435step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2435step1 raw2435step1Labels = mixedMoment B raw2435step2 raw2435step2Labels := by
      have ha : raw2435step2 = raw2435step1 := by apply Matrix.ext; unfold raw2435step2 raw2435step1; decide +kernel
      have hl : raw2435step1Labels = labelEmbedding1 ∘ raw2435step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2435step1 raw2435step1Labels raw2435step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3836 node3836Labels := by rfl

theorem canonical2436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2436 raw2436Labels = mixedMoment B node5383 node5383Labels := by
  calc
    mixedMoment B raw2436 raw2436Labels = mixedMoment B raw2436step0 raw2436step0Labels := by
      have ha : raw2436step0 = (fun i j => raw2436 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2436step0 raw2436; decide +kernel
      have hl : raw2436step0Labels = raw2436Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2436 raw2436Labels permutation152 permutation4
    mixedMoment B raw2436step0 raw2436step0Labels = mixedMoment B raw2436step1 raw2436step1Labels := by
      have ha : raw2436step1 = raw2436step0 := by apply Matrix.ext; unfold raw2436step1 raw2436step0; decide +kernel
      have hl : raw2436step0Labels = labelEmbedding7 ∘ raw2436step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2436step0 raw2436step0Labels raw2436step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5383 node5383Labels := by rfl

theorem canonical2437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2437 raw2437Labels = mixedMoment B node3731 node3731Labels := by
  calc
    mixedMoment B raw2437 raw2437Labels = mixedMoment B raw2437step0 raw2437step0Labels := by
      have ha : raw2437step0 = (fun i j => raw2437 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2437step0 raw2437; decide +kernel
      have hl : raw2437step0Labels = raw2437Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2437 raw2437Labels permutation152 permutation4
    _ = mixedMoment B node3731 node3731Labels := by rfl

theorem canonical2438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2438 raw2438Labels = mixedMoment B node3867 node3867Labels := by
  calc
    mixedMoment B raw2438 raw2438Labels = mixedMoment B raw2438step0 raw2438step0Labels := by
      have ha : raw2438step0 = (fun i j => raw2438 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2438step0 raw2438; decide +kernel
      have hl : raw2438step0Labels = raw2438Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2438 raw2438Labels permutation176 permutation6
    mixedMoment B raw2438step0 raw2438step0Labels = mixedMoment B raw2438step1 raw2438step1Labels := by
      have ha : raw2438step1 = -raw2438step0 := by apply Matrix.ext; change ∀ i j, raw2438step1 i j = -(raw2438step0 i j); unfold raw2438step1 raw2438step0; decide +kernel
      have hl : raw2438step1Labels = raw2438step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2438step1 raw2438step1Labels = mixedMoment B raw2438step2 raw2438step2Labels := by
      have ha : raw2438step2 = raw2438step1 := by apply Matrix.ext; unfold raw2438step2 raw2438step1; decide +kernel
      have hl : raw2438step1Labels = labelEmbedding1 ∘ raw2438step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2438step1 raw2438step1Labels raw2438step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3867 node3867Labels := by rfl

theorem canonical2508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2508 raw2508Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw2508 raw2508Labels = mixedMoment B raw2508step0 raw2508step0Labels := by
      have ha : raw2508step0 = (fun i j => raw2508 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2508step0 raw2508; decide +kernel
      have hl : raw2508step0Labels = raw2508Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2508 raw2508Labels permutation152 permutation5
    mixedMoment B raw2508step0 raw2508step0Labels = mixedMoment B raw2508step1 raw2508step1Labels := by
      have ha : raw2508step1 = raw2508step0 := by apply Matrix.ext; unfold raw2508step1 raw2508step0; decide +kernel
      have hl : raw2508step0Labels = labelEmbedding8 ∘ raw2508step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2508step0 raw2508step0Labels raw2508step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

theorem canonical2509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2509 raw2509Labels = mixedMoment B node3964 node3964Labels := by
  calc
    mixedMoment B raw2509 raw2509Labels = mixedMoment B raw2509step0 raw2509step0Labels := by
      have ha : raw2509step0 = (fun i j => raw2509 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2509step0 raw2509; decide +kernel
      have hl : raw2509step0Labels = raw2509Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2509 raw2509Labels permutation662 permutation4
    mixedMoment B raw2509step0 raw2509step0Labels = mixedMoment B raw2509step1 raw2509step1Labels := by
      have ha : raw2509step1 = -raw2509step0 := by apply Matrix.ext; change ∀ i j, raw2509step1 i j = -(raw2509step0 i j); unfold raw2509step1 raw2509step0; decide +kernel
      have hl : raw2509step1Labels = raw2509step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3964 node3964Labels := by rfl

theorem canonical2510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2510 raw2510Labels = mixedMoment B node3900 node3900Labels := by
  calc
    mixedMoment B raw2510 raw2510Labels = mixedMoment B raw2510step0 raw2510step0Labels := by
      have ha : raw2510step0 = (fun i j => raw2510 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2510step0 raw2510; decide +kernel
      have hl : raw2510step0Labels = raw2510Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2510 raw2510Labels permutation160 permutation3
    mixedMoment B raw2510step0 raw2510step0Labels = mixedMoment B raw2510step1 raw2510step1Labels := by
      have ha : raw2510step1 = -raw2510step0 := by apply Matrix.ext; change ∀ i j, raw2510step1 i j = -(raw2510step0 i j); unfold raw2510step1 raw2510step0; decide +kernel
      have hl : raw2510step1Labels = raw2510step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2510step1 raw2510step1Labels = mixedMoment B raw2510step2 raw2510step2Labels := by
      have ha : raw2510step2 = raw2510step1 := by apply Matrix.ext; unfold raw2510step2 raw2510step1; decide +kernel
      have hl : raw2510step1Labels = labelEmbedding1 ∘ raw2510step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2510step1 raw2510step1Labels raw2510step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3900 node3900Labels := by rfl

theorem canonical2514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2514 raw2514Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw2514 raw2514Labels = mixedMoment B raw2514step0 raw2514step0Labels := by
      have ha : raw2514step0 = (fun i j => raw2514 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2514step0 raw2514; decide +kernel
      have hl : raw2514step0Labels = raw2514Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2514 raw2514Labels permutation152 permutation4
    mixedMoment B raw2514step0 raw2514step0Labels = mixedMoment B raw2514step1 raw2514step1Labels := by
      have ha : raw2514step1 = raw2514step0 := by apply Matrix.ext; unfold raw2514step1 raw2514step0; decide +kernel
      have hl : raw2514step0Labels = labelEmbedding7 ∘ raw2514step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2514step0 raw2514step0Labels raw2514step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical2515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2515 raw2515Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw2515 raw2515Labels = mixedMoment B raw2515step0 raw2515step0Labels := by
      have ha : raw2515step0 = (fun i j => raw2515 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2515step0 raw2515; decide +kernel
      have hl : raw2515step0Labels = raw2515Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2515 raw2515Labels permutation152 permutation4
    _ = mixedMoment B node3838 node3838Labels := by rfl

theorem canonical2516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2516 raw2516Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw2516 raw2516Labels = mixedMoment B raw2516step0 raw2516step0Labels := by
      have ha : raw2516step0 = (fun i j => raw2516 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2516step0 raw2516; decide +kernel
      have hl : raw2516step0Labels = raw2516Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2516 raw2516Labels permutation176 permutation6
    mixedMoment B raw2516step0 raw2516step0Labels = mixedMoment B raw2516step1 raw2516step1Labels := by
      have ha : raw2516step1 = -raw2516step0 := by apply Matrix.ext; change ∀ i j, raw2516step1 i j = -(raw2516step0 i j); unfold raw2516step1 raw2516step0; decide +kernel
      have hl : raw2516step1Labels = raw2516step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2516step1 raw2516step1Labels = mixedMoment B raw2516step2 raw2516step2Labels := by
      have ha : raw2516step2 = raw2516step1 := by apply Matrix.ext; unfold raw2516step2 raw2516step1; decide +kernel
      have hl : raw2516step1Labels = labelEmbedding1 ∘ raw2516step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2516step1 raw2516step1Labels raw2516step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

theorem canonical2547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2547 raw2547Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw2547 raw2547Labels = mixedMoment B raw2547step0 raw2547step0Labels := by
      have ha : raw2547step0 = (fun i j => raw2547 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2547step0 raw2547; decide +kernel
      have hl : raw2547step0Labels = raw2547Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2547 raw2547Labels permutation152 permutation5
    mixedMoment B raw2547step0 raw2547step0Labels = mixedMoment B raw2547step1 raw2547step1Labels := by
      have ha : raw2547step1 = raw2547step0 := by apply Matrix.ext; unfold raw2547step1 raw2547step0; decide +kernel
      have hl : raw2547step0Labels = labelEmbedding8 ∘ raw2547step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2547step0 raw2547step0Labels raw2547step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

theorem canonical2548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2548 raw2548Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw2548 raw2548Labels = mixedMoment B raw2548step0 raw2548step0Labels := by
      have ha : raw2548step0 = (fun i j => raw2548 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2548step0 raw2548; decide +kernel
      have hl : raw2548step0Labels = raw2548Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2548 raw2548Labels permutation152 permutation4
    _ = mixedMoment B node4025 node4025Labels := by rfl

theorem canonical2549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2549 raw2549Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw2549 raw2549Labels = mixedMoment B raw2549step0 raw2549step0Labels := by
      have ha : raw2549step0 = (fun i j => raw2549 (permutation216 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2549step0 raw2549; decide +kernel
      have hl : raw2549step0Labels = raw2549Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2549 raw2549Labels permutation216 permutation3
    mixedMoment B raw2549step0 raw2549step0Labels = mixedMoment B raw2549step1 raw2549step1Labels := by
      have ha : raw2549step1 = -raw2549step0 := by apply Matrix.ext; change ∀ i j, raw2549step1 i j = -(raw2549step0 i j); unfold raw2549step1 raw2549step0; decide +kernel
      have hl : raw2549step1Labels = raw2549step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2549step1 raw2549step1Labels = mixedMoment B raw2549step2 raw2549step2Labels := by
      have ha : raw2549step2 = raw2549step1 := by apply Matrix.ext; unfold raw2549step2 raw2549step1; decide +kernel
      have hl : raw2549step1Labels = labelEmbedding1 ∘ raw2549step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2549step1 raw2549step1Labels raw2549step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3909 node3909Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical279
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical35769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35769 raw35769Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw35769 raw35769Labels = mixedMoment B raw35769step0 raw35769step0Labels := by
      have ha : raw35769step0 = (fun i j => raw35769 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35769step0 raw35769; decide +kernel
      have hl : raw35769step0Labels = raw35769Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35769 raw35769Labels permutation265 permutation2
    _ = mixedMoment B node5137 node5137Labels := by rfl

theorem canonical35770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35770 raw35770Labels = mixedMoment B node5396 node5396Labels := by
  calc
    mixedMoment B raw35770 raw35770Labels = mixedMoment B raw35770step0 raw35770step0Labels := by
      have ha : raw35770step0 = (fun i j => raw35770 (permutation289 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35770step0 raw35770; decide +kernel
      have hl : raw35770step0Labels = raw35770Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35770 raw35770Labels permutation289 permutation2
    _ = mixedMoment B node5396 node5396Labels := by rfl

theorem canonical35771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35771 raw35771Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw35771 raw35771Labels = mixedMoment B raw35771step0 raw35771step0Labels := by
      have ha : raw35771step0 = (fun i j => raw35771 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35771step0 raw35771; decide +kernel
      have hl : raw35771step0Labels = raw35771Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35771 raw35771Labels permutation265 permutation2
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical35772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35772 raw35772Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw35772 raw35772Labels = mixedMoment B raw35772step0 raw35772step0Labels := by
      have ha : raw35772step0 = (fun i j => raw35772 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35772step0 raw35772; decide +kernel
      have hl : raw35772step0Labels = raw35772Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35772 raw35772Labels permutation267 permutation2
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical35773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35773 raw35773Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw35773 raw35773Labels = mixedMoment B raw35773step0 raw35773step0Labels := by
      have ha : raw35773step0 = (fun i j => raw35773 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35773step0 raw35773; decide +kernel
      have hl : raw35773step0Labels = raw35773Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35773 raw35773Labels permutation152 permutation3
    mixedMoment B raw35773step0 raw35773step0Labels = mixedMoment B raw35773step1 raw35773step1Labels := by
      have ha : raw35773step1 = raw35773step0 := by apply Matrix.ext; unfold raw35773step1 raw35773step0; decide +kernel
      have hl : raw35773step0Labels = labelEmbedding6 ∘ raw35773step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35773step0 raw35773step0Labels raw35773step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

theorem canonical35774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35774 raw35774Labels = mixedMoment B node4677 node4677Labels := by
  calc
    mixedMoment B raw35774 raw35774Labels = mixedMoment B raw35774step0 raw35774step0Labels := by
      have ha : raw35774step0 = (fun i j => raw35774 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35774step0 raw35774; decide +kernel
      have hl : raw35774step0Labels = raw35774Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35774 raw35774Labels permutation160 permutation3
    mixedMoment B raw35774step0 raw35774step0Labels = mixedMoment B raw35774step1 raw35774step1Labels := by
      have ha : raw35774step1 = raw35774step0 := by apply Matrix.ext; unfold raw35774step1 raw35774step0; decide +kernel
      have hl : raw35774step0Labels = labelEmbedding6 ∘ raw35774step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35774step0 raw35774step0Labels raw35774step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4677 node4677Labels := by rfl

theorem canonical35775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35775 raw35775Labels = mixedMoment B node4964 node4964Labels := by
  calc
    mixedMoment B raw35775 raw35775Labels = mixedMoment B raw35775step0 raw35775step0Labels := by
      have ha : raw35775step0 = (fun i j => raw35775 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35775step0 raw35775; decide +kernel
      have hl : raw35775step0Labels = raw35775Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35775 raw35775Labels permutation265 permutation2
    _ = mixedMoment B node4964 node4964Labels := by rfl

theorem canonical35776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35776 raw35776Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw35776 raw35776Labels = mixedMoment B raw35776step0 raw35776step0Labels := by
      have ha : raw35776step0 = (fun i j => raw35776 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35776step0 raw35776; decide +kernel
      have hl : raw35776step0Labels = raw35776Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35776 raw35776Labels permutation160 permutation3
    mixedMoment B raw35776step0 raw35776step0Labels = mixedMoment B raw35776step1 raw35776step1Labels := by
      have ha : raw35776step1 = raw35776step0 := by apply Matrix.ext; unfold raw35776step1 raw35776step0; decide +kernel
      have hl : raw35776step0Labels = labelEmbedding6 ∘ raw35776step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35776step0 raw35776step0Labels raw35776step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

theorem canonical35777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35777 raw35777Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw35777 raw35777Labels = mixedMoment B raw35777step0 raw35777step0Labels := by
      have ha : raw35777step0 = (fun i j => raw35777 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35777step0 raw35777; decide +kernel
      have hl : raw35777step0Labels = raw35777Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35777 raw35777Labels permutation166 permutation3
    mixedMoment B raw35777step0 raw35777step0Labels = mixedMoment B raw35777step1 raw35777step1Labels := by
      have ha : raw35777step1 = raw35777step0 := by apply Matrix.ext; unfold raw35777step1 raw35777step0; decide +kernel
      have hl : raw35777step0Labels = labelEmbedding6 ∘ raw35777step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35777step0 raw35777step0Labels raw35777step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

theorem canonical35778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35778 raw35778Labels = mixedMoment B node4666 node4666Labels := by
  calc
    mixedMoment B raw35778 raw35778Labels = mixedMoment B raw35778step0 raw35778step0Labels := by
      have ha : raw35778step0 = (fun i j => raw35778 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35778step0 raw35778; decide +kernel
      have hl : raw35778step0Labels = raw35778Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35778 raw35778Labels permutation154 permutation3
    mixedMoment B raw35778step0 raw35778step0Labels = mixedMoment B raw35778step1 raw35778step1Labels := by
      have ha : raw35778step1 = raw35778step0 := by apply Matrix.ext; unfold raw35778step1 raw35778step0; decide +kernel
      have hl : raw35778step0Labels = labelEmbedding6 ∘ raw35778step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35778step0 raw35778step0Labels raw35778step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4666 node4666Labels := by rfl

theorem canonical35779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35779 raw35779Labels = mixedMoment B node4958 node4958Labels := by
  calc
    mixedMoment B raw35779 raw35779Labels = mixedMoment B raw35779step0 raw35779step0Labels := by
      have ha : raw35779step0 = (fun i j => raw35779 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35779step0 raw35779; decide +kernel
      have hl : raw35779step0Labels = raw35779Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35779 raw35779Labels permutation267 permutation2
    _ = mixedMoment B node4958 node4958Labels := by rfl

theorem canonical35780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35780 raw35780Labels = mixedMoment B node5373 node5373Labels := by
  calc
    mixedMoment B raw35780 raw35780Labels = mixedMoment B raw35780step0 raw35780step0Labels := by
      have ha : raw35780step0 = (fun i j => raw35780 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35780step0 raw35780; decide +kernel
      have hl : raw35780step0Labels = raw35780Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35780 raw35780Labels permutation267 permutation2
    _ = mixedMoment B node5373 node5373Labels := by rfl

theorem canonical35781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35781 raw35781Labels = mixedMoment B node5377 node5377Labels := by
  calc
    mixedMoment B raw35781 raw35781Labels = mixedMoment B raw35781step0 raw35781step0Labels := by
      have ha : raw35781step0 = (fun i j => raw35781 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35781step0 raw35781; decide +kernel
      have hl : raw35781step0Labels = raw35781Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35781 raw35781Labels permutation267 permutation2
    _ = mixedMoment B node5377 node5377Labels := by rfl

theorem canonical35782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35782 raw35782Labels = mixedMoment B node4666 node4666Labels := by
  calc
    mixedMoment B raw35782 raw35782Labels = mixedMoment B raw35782step0 raw35782step0Labels := by
      have ha : raw35782step0 = (fun i j => raw35782 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35782step0 raw35782; decide +kernel
      have hl : raw35782step0Labels = raw35782Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35782 raw35782Labels permutation152 permutation3
    mixedMoment B raw35782step0 raw35782step0Labels = mixedMoment B raw35782step1 raw35782step1Labels := by
      have ha : raw35782step1 = raw35782step0 := by apply Matrix.ext; unfold raw35782step1 raw35782step0; decide +kernel
      have hl : raw35782step0Labels = labelEmbedding6 ∘ raw35782step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35782step0 raw35782step0Labels raw35782step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4666 node4666Labels := by rfl

theorem canonical35783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35783 raw35783Labels = mixedMoment B node4958 node4958Labels := by
  calc
    mixedMoment B raw35783 raw35783Labels = mixedMoment B raw35783step0 raw35783step0Labels := by
      have ha : raw35783step0 = (fun i j => raw35783 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35783step0 raw35783; decide +kernel
      have hl : raw35783step0Labels = raw35783Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35783 raw35783Labels permutation265 permutation2
    _ = mixedMoment B node4958 node4958Labels := by rfl

theorem canonical35784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35784 raw35784Labels = mixedMoment B node5373 node5373Labels := by
  calc
    mixedMoment B raw35784 raw35784Labels = mixedMoment B raw35784step0 raw35784step0Labels := by
      have ha : raw35784step0 = (fun i j => raw35784 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35784step0 raw35784; decide +kernel
      have hl : raw35784step0Labels = raw35784Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35784 raw35784Labels permutation265 permutation2
    _ = mixedMoment B node5373 node5373Labels := by rfl

theorem canonical35785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35785 raw35785Labels = mixedMoment B node5377 node5377Labels := by
  calc
    mixedMoment B raw35785 raw35785Labels = mixedMoment B raw35785step0 raw35785step0Labels := by
      have ha : raw35785step0 = (fun i j => raw35785 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35785step0 raw35785; decide +kernel
      have hl : raw35785step0Labels = raw35785Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35785 raw35785Labels permutation265 permutation2
    _ = mixedMoment B node5377 node5377Labels := by rfl

theorem canonical35786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35786 raw35786Labels = mixedMoment B node4663 node4663Labels := by
  calc
    mixedMoment B raw35786 raw35786Labels = mixedMoment B raw35786step0 raw35786step0Labels := by
      have ha : raw35786step0 = (fun i j => raw35786 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35786step0 raw35786; decide +kernel
      have hl : raw35786step0Labels = raw35786Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35786 raw35786Labels permutation152 permutation3
    mixedMoment B raw35786step0 raw35786step0Labels = mixedMoment B raw35786step1 raw35786step1Labels := by
      have ha : raw35786step1 = raw35786step0 := by apply Matrix.ext; unfold raw35786step1 raw35786step0; decide +kernel
      have hl : raw35786step0Labels = labelEmbedding6 ∘ raw35786step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35786step0 raw35786step0Labels raw35786step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4663 node4663Labels := by rfl

theorem canonical35787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35787 raw35787Labels = mixedMoment B node4956 node4956Labels := by
  calc
    mixedMoment B raw35787 raw35787Labels = mixedMoment B raw35787step0 raw35787step0Labels := by
      have ha : raw35787step0 = (fun i j => raw35787 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35787step0 raw35787; decide +kernel
      have hl : raw35787step0Labels = raw35787Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35787 raw35787Labels permutation265 permutation2
    _ = mixedMoment B node4956 node4956Labels := by rfl

theorem canonical35788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35788 raw35788Labels = mixedMoment B node5114 node5114Labels := by
  calc
    mixedMoment B raw35788 raw35788Labels = mixedMoment B raw35788step0 raw35788step0Labels := by
      have ha : raw35788step0 = (fun i j => raw35788 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35788step0 raw35788; decide +kernel
      have hl : raw35788step0Labels = raw35788Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35788 raw35788Labels permutation664 permutation3
    mixedMoment B raw35788step0 raw35788step0Labels = mixedMoment B raw35788step1 raw35788step1Labels := by
      have ha : raw35788step1 = -raw35788step0 := by apply Matrix.ext; change ∀ i j, raw35788step1 i j = -(raw35788step0 i j); unfold raw35788step1 raw35788step0; decide +kernel
      have hl : raw35788step1Labels = raw35788step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35788step1 raw35788step1Labels = mixedMoment B raw35788step2 raw35788step2Labels := by
      have ha : raw35788step2 = raw35788step1 := by apply Matrix.ext; unfold raw35788step2 raw35788step1; decide +kernel
      have hl : raw35788step1Labels = labelEmbedding6 ∘ raw35788step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35788step1 raw35788step1Labels raw35788step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5114 node5114Labels := by rfl

theorem canonical35789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35789 raw35789Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw35789 raw35789Labels = mixedMoment B raw35789step0 raw35789step0Labels := by
      have ha : raw35789step0 = (fun i j => raw35789 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35789step0 raw35789; decide +kernel
      have hl : raw35789step0Labels = raw35789Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35789 raw35789Labels permutation682 permutation3
    mixedMoment B raw35789step0 raw35789step0Labels = mixedMoment B raw35789step1 raw35789step1Labels := by
      have ha : raw35789step1 = -raw35789step0 := by apply Matrix.ext; change ∀ i j, raw35789step1 i j = -(raw35789step0 i j); unfold raw35789step1 raw35789step0; decide +kernel
      have hl : raw35789step1Labels = raw35789step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35789step1 raw35789step1Labels = mixedMoment B raw35789step2 raw35789step2Labels := by
      have ha : raw35789step2 = raw35789step1 := by apply Matrix.ext; unfold raw35789step2 raw35789step1; decide +kernel
      have hl : raw35789step1Labels = labelEmbedding6 ∘ raw35789step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35789step1 raw35789step1Labels raw35789step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5129 node5129Labels := by rfl

theorem canonical35790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35790 raw35790Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw35790 raw35790Labels = mixedMoment B raw35790step0 raw35790step0Labels := by
      have ha : raw35790step0 = (fun i j => raw35790 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35790step0 raw35790; decide +kernel
      have hl : raw35790step0Labels = raw35790Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35790 raw35790Labels permutation658 permutation3
    mixedMoment B raw35790step0 raw35790step0Labels = mixedMoment B raw35790step1 raw35790step1Labels := by
      have ha : raw35790step1 = -raw35790step0 := by apply Matrix.ext; change ∀ i j, raw35790step1 i j = -(raw35790step0 i j); unfold raw35790step1 raw35790step0; decide +kernel
      have hl : raw35790step1Labels = raw35790step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35790step1 raw35790step1Labels = mixedMoment B raw35790step2 raw35790step2Labels := by
      have ha : raw35790step2 = raw35790step1 := by apply Matrix.ext; unfold raw35790step2 raw35790step1; decide +kernel
      have hl : raw35790step1Labels = labelEmbedding6 ∘ raw35790step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35790step1 raw35790step1Labels raw35790step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5129 node5129Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_NumericVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6.Certificate.MixedSemantics

theorem integer_eval_numericVector (B : Fin 7 → Basis) (v : Integer.Sparse (Fin 3237)) :
    Integer.Sparse.eval v (numericVector B) =
      Integer.Sparse.eval (Integer.Sparse.reindex keyMap v) (mixedVector B) := by
  rw [Integer.Sparse.eval_reindex]
  rfl

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5114 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5114 node5114Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2896 node2896Labels + mixedMoment B node3597 node3597Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2139 singletonSmall5114
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5114) = raw2139Labels := by decide +kernel
  rw [hl, canonical2139 B hB] at h
  have hc0 : mixedMoment B raw2139 (Fin.cases (0 : Fin 2) singletonSmall5114) =
      mixedMoment B node2896 node2896Labels := by
    have ha : raw2139 = raw2140 := by apply Matrix.ext; unfold raw2139 raw2140; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5114 = raw2140Labels := by decide +kernel
    rw [ha, hj, canonical2140 B hB]
  have hc1 : mixedMoment B raw2139 (Fin.cases (1 : Fin 2) singletonSmall5114) =
      mixedMoment B node3597 node3597Labels := by
    have ha : raw2139 = raw2141 := by apply Matrix.ext; unfold raw2139 raw2141; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5114 = raw2141Labels := by decide +kernel
    rw [ha, hj, canonical2141 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5137 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5137 node5137Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2556 node2556Labels + mixedMoment B node3521 node3521Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2166 singletonSmall5137
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5137) = raw2166Labels := by decide +kernel
  rw [hl, canonical2166 B hB] at h
  have hc0 : mixedMoment B raw2166 (Fin.cases (0 : Fin 2) singletonSmall5137) =
      mixedMoment B node2556 node2556Labels := by
    have ha : raw2166 = raw2167 := by apply Matrix.ext; unfold raw2166 raw2167; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5137 = raw2167Labels := by decide +kernel
    rw [ha, hj, canonical2167 B hB]
  have hc1 : mixedMoment B raw2166 (Fin.cases (1 : Fin 2) singletonSmall5137) =
      mixedMoment B node3521 node3521Labels := by
    have ha : raw2166 = raw2168 := by apply Matrix.ext; unfold raw2166 raw2168; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5137 = raw2168Labels := by decide +kernel
    rw [ha, hj, canonical2168 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5373 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5373 node5373Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3709 node3709Labels + mixedMoment B node3792 node3792Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2424 singletonSmall5373
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5373) = raw2424Labels := by decide +kernel
  rw [hl, canonical2424 B hB] at h
  have hc0 : mixedMoment B raw2424 (Fin.cases (0 : Fin 2) singletonSmall5373) =
      mixedMoment B node3709 node3709Labels := by
    have ha : raw2424 = raw2425 := by apply Matrix.ext; unfold raw2424 raw2425; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5373 = raw2425Labels := by decide +kernel
    rw [ha, hj, canonical2425 B hB]
  have hc1 : mixedMoment B raw2424 (Fin.cases (1 : Fin 2) singletonSmall5373) =
      mixedMoment B node3792 node3792Labels := by
    have ha : raw2424 = raw2426 := by apply Matrix.ext; unfold raw2424 raw2426; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5373 = raw2426Labels := by decide +kernel
    rw [ha, hj, canonical2426 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5380 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5380 node5380Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3721 node3721Labels + mixedMoment B node3836 node3836Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2433 singletonSmall5380
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5380) = raw2433Labels := by decide +kernel
  rw [hl, canonical2433 B hB] at h
  have hc0 : mixedMoment B raw2433 (Fin.cases (0 : Fin 2) singletonSmall5380) =
      mixedMoment B node3721 node3721Labels := by
    have ha : raw2433 = raw2434 := by apply Matrix.ext; unfold raw2433 raw2434; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5380 = raw2434Labels := by decide +kernel
    rw [ha, hj, canonical2434 B hB]
  have hc1 : mixedMoment B raw2433 (Fin.cases (1 : Fin 2) singletonSmall5380) =
      mixedMoment B node3836 node3836Labels := by
    have ha : raw2433 = raw2435 := by apply Matrix.ext; unfold raw2433 raw2435; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5380 = raw2435Labels := by decide +kernel
    rw [ha, hj, canonical2435 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5383 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5383 node5383Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3731 node3731Labels + mixedMoment B node3867 node3867Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2436 singletonSmall5383
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5383) = raw2436Labels := by decide +kernel
  rw [hl, canonical2436 B hB] at h
  have hc0 : mixedMoment B raw2436 (Fin.cases (0 : Fin 2) singletonSmall5383) =
      mixedMoment B node3731 node3731Labels := by
    have ha : raw2436 = raw2437 := by apply Matrix.ext; unfold raw2436 raw2437; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5383 = raw2437Labels := by decide +kernel
    rw [ha, hj, canonical2437 B hB]
  have hc1 : mixedMoment B raw2436 (Fin.cases (1 : Fin 2) singletonSmall5383) =
      mixedMoment B node3867 node3867Labels := by
    have ha : raw2436 = raw2438 := by apply Matrix.ext; unfold raw2436 raw2438; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5383 = raw2438Labels := by decide +kernel
    rw [ha, hj, canonical2438 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5422 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5422 node5422Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3964 node3964Labels + mixedMoment B node3900 node3900Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2508 singletonSmall5422
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5422) = raw2508Labels := by decide +kernel
  rw [hl, canonical2508 B hB] at h
  have hc0 : mixedMoment B raw2508 (Fin.cases (0 : Fin 2) singletonSmall5422) =
      mixedMoment B node3964 node3964Labels := by
    have ha : raw2508 = raw2509 := by apply Matrix.ext; unfold raw2508 raw2509; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5422 = raw2509Labels := by decide +kernel
    rw [ha, hj, canonical2509 B hB]
  have hc1 : mixedMoment B raw2508 (Fin.cases (1 : Fin 2) singletonSmall5422) =
      mixedMoment B node3900 node3900Labels := by
    have ha : raw2508 = raw2510 := by apply Matrix.ext; unfold raw2508 raw2510; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5422 = raw2510Labels := by decide +kernel
    rw [ha, hj, canonical2510 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5424 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5424 node5424Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3838 node3838Labels + mixedMoment B node3843 node3843Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2514 singletonSmall5424
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5424) = raw2514Labels := by decide +kernel
  rw [hl, canonical2514 B hB] at h
  have hc0 : mixedMoment B raw2514 (Fin.cases (0 : Fin 2) singletonSmall5424) =
      mixedMoment B node3838 node3838Labels := by
    have ha : raw2514 = raw2515 := by apply Matrix.ext; unfold raw2514 raw2515; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5424 = raw2515Labels := by decide +kernel
    rw [ha, hj, canonical2515 B hB]
  have hc1 : mixedMoment B raw2514 (Fin.cases (1 : Fin 2) singletonSmall5424) =
      mixedMoment B node3843 node3843Labels := by
    have ha : raw2514 = raw2516 := by apply Matrix.ext; unfold raw2514 raw2516; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5424 = raw2516Labels := by decide +kernel
    rw [ha, hj, canonical2516 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5447 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5447 node5447Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node4025 node4025Labels + mixedMoment B node3909 node3909Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2547 singletonSmall5447
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5447) = raw2547Labels := by decide +kernel
  rw [hl, canonical2547 B hB] at h
  have hc0 : mixedMoment B raw2547 (Fin.cases (0 : Fin 2) singletonSmall5447) =
      mixedMoment B node4025 node4025Labels := by
    have ha : raw2547 = raw2548 := by apply Matrix.ext; unfold raw2547 raw2548; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5447 = raw2548Labels := by decide +kernel
    rw [ha, hj, canonical2548 B hB]
  have hc1 : mixedMoment B raw2547 (Fin.cases (1 : Fin 2) singletonSmall5447) =
      mixedMoment B node3909 node3909Labels := by
    have ha : raw2547 = raw2549 := by apply Matrix.ext; unfold raw2547 raw2549; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5447 = raw2549Labels := by decide +kernel
    rw [ha, hj, canonical2549 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2556 node2556Labels = Sparse.eval nodeValue2556 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2556) = mixedMoment B node2556 node2556Labels := rfl
  simpa [nodeValue2556, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2896 node2896Labels = Sparse.eval nodeValue2896 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2896) = mixedMoment B node2896 node2896Labels := rfl
  simpa [nodeValue2896, Sparse.eval] using hc.symm

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

theorem sound3521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3521 node3521Labels = Sparse.eval nodeValue3521 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3521) = mixedMoment B node3521 node3521Labels := rfl
  simpa [nodeValue3521, Sparse.eval] using hc.symm

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

theorem sound3597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3597 node3597Labels = Sparse.eval nodeValue3597 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3597) = mixedMoment B node3597 node3597Labels := rfl
  simpa [nodeValue3597, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3709 node3709Labels = Sparse.eval nodeValue3709 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3709) = mixedMoment B node3709 node3709Labels := rfl
  simpa [nodeValue3709, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3721 node3721Labels = Sparse.eval nodeValue3721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3721) = mixedMoment B node3721 node3721Labels := rfl
  simpa [nodeValue3721, Sparse.eval] using hc.symm

theorem sound3731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3731 node3731Labels = Sparse.eval nodeValue3731 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3731) = mixedMoment B node3731 node3731Labels := rfl
  simpa [nodeValue3731, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3792 node3792Labels = Sparse.eval nodeValue3792 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3792) = mixedMoment B node3792 node3792Labels := rfl
  simpa [nodeValue3792, Sparse.eval] using hc.symm

theorem sound3836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3836 node3836Labels = Sparse.eval nodeValue3836 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3836) = mixedMoment B node3836 node3836Labels := rfl
  simpa [nodeValue3836, Sparse.eval] using hc.symm

theorem sound3838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3838 node3838Labels = Sparse.eval nodeValue3838 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3838) = mixedMoment B node3838 node3838Labels := rfl
  simpa [nodeValue3838, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3843 node3843Labels = Sparse.eval nodeValue3843 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3843) = mixedMoment B node3843 node3843Labels := rfl
  simpa [nodeValue3843, Sparse.eval] using hc.symm

theorem sound3867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3867 node3867Labels = Sparse.eval nodeValue3867 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3867) = mixedMoment B node3867 node3867Labels := rfl
  simpa [nodeValue3867, Sparse.eval] using hc.symm

theorem sound3900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3900 node3900Labels = Sparse.eval nodeValue3900 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3900) = mixedMoment B node3900 node3900Labels := rfl
  simpa [nodeValue3900, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3909 node3909Labels = Sparse.eval nodeValue3909 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3909) = mixedMoment B node3909 node3909Labels := rfl
  simpa [nodeValue3909, Sparse.eval] using hc.symm

theorem sound3964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3964 node3964Labels = Sparse.eval nodeValue3964 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3964) = mixedMoment B node3964 node3964Labels := rfl
  simpa [nodeValue3964, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4025 node4025Labels = Sparse.eval nodeValue4025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4025) = mixedMoment B node4025 node4025Labels := rfl
  simpa [nodeValue4025, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4663 node4663Labels = Sparse.eval nodeValue4663 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4663) = mixedMoment B node4663 node4663Labels := rfl
  simpa [nodeValue4663, Sparse.eval] using hc.symm

theorem sound4666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4666 node4666Labels = Sparse.eval nodeValue4666 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4666) = mixedMoment B node4666 node4666Labels := rfl
  simpa [nodeValue4666, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4677 node4677Labels = Sparse.eval nodeValue4677 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4677) = mixedMoment B node4677 node4677Labels := rfl
  simpa [nodeValue4677, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4851 node4851Labels = Sparse.eval nodeValue4851 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4851) = mixedMoment B node4851 node4851Labels := rfl
  simpa [nodeValue4851, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4956 node4956Labels = Sparse.eval nodeValue4956 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4956) = mixedMoment B node4956 node4956Labels := rfl
  simpa [nodeValue4956, Sparse.eval] using hc.symm

theorem sound4958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4958 node4958Labels = Sparse.eval nodeValue4958 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4958) = mixedMoment B node4958 node4958Labels := rfl
  simpa [nodeValue4958, Sparse.eval] using hc.symm

theorem sound4964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4964 node4964Labels = Sparse.eval nodeValue4964 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4964) = mixedMoment B node4964 node4964Labels := rfl
  simpa [nodeValue4964, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5114 node5114Labels = Sparse.eval nodeValue5114 (mixedVector B) := by
  have h := singleton5114 B _hB
  rw [sound2896 B _hB _hF, sound3597 B _hB _hF] at h
  norm_num [nodeValue5114, nodeValue2896, nodeValue3597, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5129 node5129Labels = Sparse.eval nodeValue5129 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5129) = mixedMoment B node5129 node5129Labels := rfl
  simpa [nodeValue5129, Sparse.eval] using hc.symm

theorem sound5137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5137 node5137Labels = Sparse.eval nodeValue5137 (mixedVector B) := by
  have h := singleton5137 B _hB
  rw [sound2556 B _hB _hF, sound3521 B _hB _hF] at h
  norm_num [nodeValue5137, nodeValue2556, nodeValue3521, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5373 node5373Labels = Sparse.eval nodeValue5373 (mixedVector B) := by
  have h := singleton5373 B _hB
  rw [sound3709 B _hB _hF, sound3792 B _hB _hF] at h
  norm_num [nodeValue5373, nodeValue3709, nodeValue3792, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5396 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5396 node5396Labels = 0 := by
  exact mixedMoment_order_one B hB node5396 node5396Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5427 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5427 node5427Labels = 0 := by
  exact mixedMoment_order_one B hB node5427 node5427Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5377 node5377Labels = Sparse.eval nodeValue5377 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5377) = mixedMoment B node5377 node5377Labels := rfl
  simpa [nodeValue5377, Sparse.eval] using hc.symm

theorem sound5379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5379 node5379Labels = Sparse.eval nodeValue5379 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5379) = mixedMoment B node5379 node5379Labels := rfl
  simpa [nodeValue5379, Sparse.eval] using hc.symm

theorem sound5380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5380 node5380Labels = Sparse.eval nodeValue5380 (mixedVector B) := by
  have h := singleton5380 B _hB
  rw [sound3721 B _hB _hF, sound3836 B _hB _hF] at h
  norm_num [nodeValue5380, nodeValue3721, nodeValue3836, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5383 node5383Labels = Sparse.eval nodeValue5383 (mixedVector B) := by
  have h := singleton5383 B _hB
  rw [sound3731 B _hB _hF, sound3867 B _hB _hF] at h
  norm_num [nodeValue5383, nodeValue3731, nodeValue3867, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5396 node5396Labels = Sparse.eval nodeValue5396 (mixedVector B) := by
  simpa only [nodeValue5396, Sparse.eval_nil] using zero5396 B _hB _hF

theorem sound5422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5422 node5422Labels = Sparse.eval nodeValue5422 (mixedVector B) := by
  have h := singleton5422 B _hB
  rw [sound3900 B _hB _hF, sound3964 B _hB _hF] at h
  norm_num [nodeValue5422, nodeValue3900, nodeValue3964, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5424 node5424Labels = Sparse.eval nodeValue5424 (mixedVector B) := by
  have h := singleton5424 B _hB
  rw [sound3838 B _hB _hF, sound3843 B _hB _hF] at h
  norm_num [nodeValue5424, nodeValue3838, nodeValue3843, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5427 node5427Labels = Sparse.eval nodeValue5427 (mixedVector B) := by
  simpa only [nodeValue5427, Sparse.eval_nil] using zero5427 B _hB _hF

theorem sound5430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5430 node5430Labels = Sparse.eval nodeValue5430 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5430) = mixedMoment B node5430 node5430Labels := rfl
  simpa [nodeValue5430, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5447 node5447Labels = Sparse.eval nodeValue5447 (mixedVector B) := by
  have h := singleton5447 B _hB
  rw [sound3909 B _hB _hF, sound4025 B _hB _hF] at h
  norm_num [nodeValue5447, nodeValue3909, nodeValue4025, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SourceRules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6.Certificate.MixedSemantics

theorem offDiagSum_explicit (f : Coord → Coord → ℝ) :
    offDiagSum f =
      f 0 1 + f 0 2 + f 0 3 + f 0 4 + f 0 5 +
      f 1 0 + f 1 2 + f 1 3 + f 1 4 + f 1 5 +
      f 2 0 + f 2 1 + f 2 3 + f 2 4 + f 2 5 +
      f 3 0 + f 3 1 + f 3 2 + f 3 4 + f 3 5 +
      f 4 0 + f 4 1 + f 4 2 + f 4 3 + f 4 5 +
      f 5 0 + f 5 1 + f 5 2 + f 5 3 + f 5 4 := by
  unfold offDiagSum
  simp only [Finset.sum_erase_eq_sub (Finset.mem_univ _), Fin.sum_univ_succ,
    Fin.sum_univ_zero, add_zero]
  simp only [Fin.succ, Nat.reduceAdd]
  ring_nf
  rfl

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources80
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2583 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2583 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2583 + difference 0 1) (sourceB2583 + difference 1 0) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA2583 + difference 0 1) (sourceB2583 + difference 1 0) sourceC2583) = raw35769 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35769; decide +kernel
    rw [ha]
    exact (canonical35769 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2583 + difference 0 2) (sourceB2583 + difference 2 0) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5396) := by
    have ha : (tripleCharges (sourceA2583 + difference 0 2) (sourceB2583 + difference 2 0) sourceC2583) = raw35770 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35770; decide +kernel
    rw [ha]
    exact (canonical35770 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2583 + difference 0 3) (sourceB2583 + difference 3 0) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA2583 + difference 0 3) (sourceB2583 + difference 3 0) sourceC2583) = raw35771 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35771; decide +kernel
    rw [ha]
    exact (canonical35771 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2583 + difference 0 4) (sourceB2583 + difference 4 0) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA2583 + difference 0 4) (sourceB2583 + difference 4 0) sourceC2583) = raw35772 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35772; decide +kernel
    rw [ha]
    exact (canonical35772 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2583 + difference 0 5) (sourceB2583 + difference 5 0) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5427) := by
    have ha : (tripleCharges (sourceA2583 + difference 0 5) (sourceB2583 + difference 5 0) sourceC2583) = raw18573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw18573; decide +kernel
    rw [ha]
    exact (canonical18573 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2583 + difference 1 0) (sourceB2583 + difference 0 1) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA2583 + difference 1 0) (sourceB2583 + difference 0 1) sourceC2583) = raw18598 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw18598; decide +kernel
    rw [ha]
    exact (canonical18598 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2583 + difference 1 2) (sourceB2583 + difference 2 1) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA2583 + difference 1 2) (sourceB2583 + difference 2 1) sourceC2583) = raw18600 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw18600; decide +kernel
    rw [ha]
    exact (canonical18600 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2583 + difference 1 3) (sourceB2583 + difference 3 1) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA2583 + difference 1 3) (sourceB2583 + difference 3 1) sourceC2583) = raw18601 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw18601; decide +kernel
    rw [ha]
    exact (canonical18601 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2583 + difference 1 4) (sourceB2583 + difference 4 1) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA2583 + difference 1 4) (sourceB2583 + difference 4 1) sourceC2583) = raw18602 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw18602; decide +kernel
    rw [ha]
    exact (canonical18602 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2583 + difference 1 5) (sourceB2583 + difference 5 1) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA2583 + difference 1 5) (sourceB2583 + difference 5 1) sourceC2583) = raw35773 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35773; decide +kernel
    rw [ha]
    exact (canonical35773 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2583 + difference 2 0) (sourceB2583 + difference 0 2) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4677) := by
    have ha : (tripleCharges (sourceA2583 + difference 2 0) (sourceB2583 + difference 0 2) sourceC2583) = raw35774 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35774; decide +kernel
    rw [ha]
    exact (canonical35774 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2583 + difference 2 1) (sourceB2583 + difference 1 2) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4964) := by
    have ha : (tripleCharges (sourceA2583 + difference 2 1) (sourceB2583 + difference 1 2) sourceC2583) = raw35775 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35775; decide +kernel
    rw [ha]
    exact (canonical35775 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2583 + difference 2 3) (sourceB2583 + difference 3 2) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA2583 + difference 2 3) (sourceB2583 + difference 3 2) sourceC2583) = raw35776 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35776; decide +kernel
    rw [ha]
    exact (canonical35776 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2583 + difference 2 4) (sourceB2583 + difference 4 2) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA2583 + difference 2 4) (sourceB2583 + difference 4 2) sourceC2583) = raw35777 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35777; decide +kernel
    rw [ha]
    exact (canonical35777 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2583 + difference 2 5) (sourceB2583 + difference 5 2) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5383) := by
    have ha : (tripleCharges (sourceA2583 + difference 2 5) (sourceB2583 + difference 5 2) sourceC2583) = raw18584 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw18584; decide +kernel
    rw [ha]
    exact (canonical18584 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2583 + difference 3 0) (sourceB2583 + difference 0 3) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4666) := by
    have ha : (tripleCharges (sourceA2583 + difference 3 0) (sourceB2583 + difference 0 3) sourceC2583) = raw35778 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35778; decide +kernel
    rw [ha]
    exact (canonical35778 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2583 + difference 3 1) (sourceB2583 + difference 1 3) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4958) := by
    have ha : (tripleCharges (sourceA2583 + difference 3 1) (sourceB2583 + difference 1 3) sourceC2583) = raw35779 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35779; decide +kernel
    rw [ha]
    exact (canonical35779 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2583 + difference 3 2) (sourceB2583 + difference 2 3) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5373) := by
    have ha : (tripleCharges (sourceA2583 + difference 3 2) (sourceB2583 + difference 2 3) sourceC2583) = raw35780 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35780; decide +kernel
    rw [ha]
    exact (canonical35780 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2583 + difference 3 4) (sourceB2583 + difference 4 3) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5377) := by
    have ha : (tripleCharges (sourceA2583 + difference 3 4) (sourceB2583 + difference 4 3) sourceC2583) = raw35781 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35781; decide +kernel
    rw [ha]
    exact (canonical35781 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2583 + difference 3 5) (sourceB2583 + difference 5 3) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA2583 + difference 3 5) (sourceB2583 + difference 5 3) sourceC2583) = raw18589 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw18589; decide +kernel
    rw [ha]
    exact (canonical18589 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2583 + difference 4 0) (sourceB2583 + difference 0 4) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4666) := by
    have ha : (tripleCharges (sourceA2583 + difference 4 0) (sourceB2583 + difference 0 4) sourceC2583) = raw35782 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35782; decide +kernel
    rw [ha]
    exact (canonical35782 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2583 + difference 4 1) (sourceB2583 + difference 1 4) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4958) := by
    have ha : (tripleCharges (sourceA2583 + difference 4 1) (sourceB2583 + difference 1 4) sourceC2583) = raw35783 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35783; decide +kernel
    rw [ha]
    exact (canonical35783 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2583 + difference 4 2) (sourceB2583 + difference 2 4) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5373) := by
    have ha : (tripleCharges (sourceA2583 + difference 4 2) (sourceB2583 + difference 2 4) sourceC2583) = raw35784 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35784; decide +kernel
    rw [ha]
    exact (canonical35784 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2583 + difference 4 3) (sourceB2583 + difference 3 4) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5377) := by
    have ha : (tripleCharges (sourceA2583 + difference 4 3) (sourceB2583 + difference 3 4) sourceC2583) = raw35785 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35785; decide +kernel
    rw [ha]
    exact (canonical35785 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2583 + difference 4 5) (sourceB2583 + difference 5 4) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA2583 + difference 4 5) (sourceB2583 + difference 5 4) sourceC2583) = raw18594 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw18594; decide +kernel
    rw [ha]
    exact (canonical18594 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2583 + difference 5 0) (sourceB2583 + difference 0 5) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4663) := by
    have ha : (tripleCharges (sourceA2583 + difference 5 0) (sourceB2583 + difference 0 5) sourceC2583) = raw35786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35786; decide +kernel
    rw [ha]
    exact (canonical35786 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2583 + difference 5 1) (sourceB2583 + difference 1 5) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4956) := by
    have ha : (tripleCharges (sourceA2583 + difference 5 1) (sourceB2583 + difference 1 5) sourceC2583) = raw35787 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35787; decide +kernel
    rw [ha]
    exact (canonical35787 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2583 + difference 5 2) (sourceB2583 + difference 2 5) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5114) := by
    have ha : (tripleCharges (sourceA2583 + difference 5 2) (sourceB2583 + difference 2 5) sourceC2583) = raw35788 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35788; decide +kernel
    rw [ha]
    exact (canonical35788 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2583 + difference 5 3) (sourceB2583 + difference 3 5) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA2583 + difference 5 3) (sourceB2583 + difference 3 5) sourceC2583) = raw35789 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35789; decide +kernel
    rw [ha]
    exact (canonical35789 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2583 + difference 5 4) (sourceB2583 + difference 4 5) sourceC2583) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA2583 + difference 5 4) (sourceB2583 + difference 4 5) sourceC2583) = raw35790 := by
      apply Matrix.ext; unfold tripleCharges sourceA2583 sourceB2583 sourceC2583 difference raw35790; decide +kernel
    rw [ha]
    exact (canonical35790 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2583 sourceB2583 sourceC2583
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2583, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2067 : Integer.Sparse.reindex keyMap MixedData.row2067 = numericRow2067 := by decide +kernel

theorem numericCheck2067 (x : Master → ℝ) : Integer.Sparse.eval numericRow2067 x =
    (4 : ℝ) * reducedSource2067 x := by
  norm_num [numericRow2067, reducedSource2067, Integer.Sparse.eval, Sparse.eval, nodeValue4663, nodeValue4666, nodeValue4677, nodeValue4851, nodeValue4956, nodeValue4958, nodeValue4964, nodeValue5114, nodeValue5129, nodeValue5137, nodeValue5373, nodeValue5377, nodeValue5379, nodeValue5380, nodeValue5383, nodeValue5396, nodeValue5422, nodeValue5424, nodeValue5427, nodeValue5430, nodeValue5447]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2067 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2067 (mixedVector B) = 0 := by
  have h4663 : mixedVector B (Sum.inr 4663) = Sparse.eval nodeValue4663 (mixedVector B) := by
    change mixedMoment B node4663 node4663Labels = _
    exact sound4663 B hB hF
  have h4666 : mixedVector B (Sum.inr 4666) = Sparse.eval nodeValue4666 (mixedVector B) := by
    change mixedMoment B node4666 node4666Labels = _
    exact sound4666 B hB hF
  have h4677 : mixedVector B (Sum.inr 4677) = Sparse.eval nodeValue4677 (mixedVector B) := by
    change mixedMoment B node4677 node4677Labels = _
    exact sound4677 B hB hF
  have h4851 : mixedVector B (Sum.inr 4851) = Sparse.eval nodeValue4851 (mixedVector B) := by
    change mixedMoment B node4851 node4851Labels = _
    exact sound4851 B hB hF
  have h4956 : mixedVector B (Sum.inr 4956) = Sparse.eval nodeValue4956 (mixedVector B) := by
    change mixedMoment B node4956 node4956Labels = _
    exact sound4956 B hB hF
  have h4958 : mixedVector B (Sum.inr 4958) = Sparse.eval nodeValue4958 (mixedVector B) := by
    change mixedMoment B node4958 node4958Labels = _
    exact sound4958 B hB hF
  have h4964 : mixedVector B (Sum.inr 4964) = Sparse.eval nodeValue4964 (mixedVector B) := by
    change mixedMoment B node4964 node4964Labels = _
    exact sound4964 B hB hF
  have h5114 : mixedVector B (Sum.inr 5114) = Sparse.eval nodeValue5114 (mixedVector B) := by
    change mixedMoment B node5114 node5114Labels = _
    exact sound5114 B hB hF
  have h5129 : mixedVector B (Sum.inr 5129) = Sparse.eval nodeValue5129 (mixedVector B) := by
    change mixedMoment B node5129 node5129Labels = _
    exact sound5129 B hB hF
  have h5137 : mixedVector B (Sum.inr 5137) = Sparse.eval nodeValue5137 (mixedVector B) := by
    change mixedMoment B node5137 node5137Labels = _
    exact sound5137 B hB hF
  have h5373 : mixedVector B (Sum.inr 5373) = Sparse.eval nodeValue5373 (mixedVector B) := by
    change mixedMoment B node5373 node5373Labels = _
    exact sound5373 B hB hF
  have h5377 : mixedVector B (Sum.inr 5377) = Sparse.eval nodeValue5377 (mixedVector B) := by
    change mixedMoment B node5377 node5377Labels = _
    exact sound5377 B hB hF
  have h5379 : mixedVector B (Sum.inr 5379) = Sparse.eval nodeValue5379 (mixedVector B) := by
    change mixedMoment B node5379 node5379Labels = _
    exact sound5379 B hB hF
  have h5380 : mixedVector B (Sum.inr 5380) = Sparse.eval nodeValue5380 (mixedVector B) := by
    change mixedMoment B node5380 node5380Labels = _
    exact sound5380 B hB hF
  have h5383 : mixedVector B (Sum.inr 5383) = Sparse.eval nodeValue5383 (mixedVector B) := by
    change mixedMoment B node5383 node5383Labels = _
    exact sound5383 B hB hF
  have h5396 : mixedVector B (Sum.inr 5396) = Sparse.eval nodeValue5396 (mixedVector B) := by
    change mixedMoment B node5396 node5396Labels = _
    exact sound5396 B hB hF
  have h5422 : mixedVector B (Sum.inr 5422) = Sparse.eval nodeValue5422 (mixedVector B) := by
    change mixedMoment B node5422 node5422Labels = _
    exact sound5422 B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5427 : mixedVector B (Sum.inr 5427) = Sparse.eval nodeValue5427 (mixedVector B) := by
    change mixedMoment B node5427 node5427Labels = _
    exact sound5427 B hB hF
  have h5430 : mixedVector B (Sum.inr 5430) = Sparse.eval nodeValue5430 (mixedVector B) := by
    change mixedMoment B node5430 node5430Labels = _
    exact sound5430 B hB hF
  have h5447 : mixedVector B (Sum.inr 5447) = Sparse.eval nodeValue5447 (mixedVector B) := by
    change mixedMoment B node5447 node5447Labels = _
    exact sound5447 B hB hF
  simpa only [sourceForm2583, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4663, h4666, h4677, h4851, h4956, h4958, h4964, h5114, h5129, h5137, h5373, h5377, h5379, h5380, h5383, h5396, h5422, h5424, h5427, h5430, h5447, reducedSource2067] using sourceEq2583 B hB

theorem rowSound2067_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2067 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2067, numericCheck2067, reducedZero2067 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2067_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2067_e_oai
