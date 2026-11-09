-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:46:57.564463+00:00
-- url     : https://prove2.me/submissions/f274ac78-c0c5-4d9e-b63c-a78811f418a8

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
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

theorem rowFourier_zero_first {p : ℕ} (H : CMatrix) (a : Fin (p + 1) → ℤ)
    (ha : a 0 = 0) (ρ : Fin (p + 1) ↪ Coord) :
    rowFourier H ρ a = rowFourier H (Sampling.dropFirst ρ) (fun i => a i.succ) := by
  simp only [rowFourier, Fin.prod_univ_succ, ha, zpow_zero, one_mul]
  rfl

theorem mixedMoment_zero_first_row {p n l : ℕ} (hp : p < 6) (B : Fin 7 → Basis)
    (A : Matrix (Fin (p + 1)) (Fin n) ℤ) (label : Fin n → Fin l)
    (hA : ∀ j, A 0 j = 0) :
    mixedMoment B A label = mixedMoment B (fun i j => A i.succ j) label := by
  apply average_congr
  intro r
  have h (ρ : Fin (p + 1) ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B A label r ρ τ =
        mixedIntegrand B (fun i j => A i.succ j) label r (Sampling.dropFirst ρ) τ := by
    apply Finset.prod_congr rfl
    intro j _
    exact rowFourier_zero_first _ (fun i => A i j) (hA j) ρ
  simp_rw [h]
  exact Sampling.average_dropFirst hp
    (fun ρ : Fin p ↪ Coord => average (fun τ : Fin l ↪ Coord =>
      (mixedIntegrand B (fun i j => A i.succ j) label r ρ τ).re))

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

theorem delete_zero_row {p n l : ℕ} (hp : p < 6) (B : Fin 7 → Basis)
    (A : Matrix (Fin (p + 1)) (Fin n) ℤ) (label : Fin n → Fin l)
    (ρ : Equiv.Perm (Fin (p + 1))) (hz : ∀ j, A (ρ 0) j = 0) :
    mixedMoment B A label = mixedMoment B (fun i j => A (ρ i.succ) j) label := by
  rw [← mixedMoment_row_permutation B A label ρ]
  exact mixedMoment_zero_first_row hp B _ label hz

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical138
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17708 raw17708Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw17708 raw17708Labels = mixedMoment B raw17708step0 raw17708step0Labels := by
      have hz : ∀ j, raw17708 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17708step0 = (fun i j => raw17708 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17708step0 raw17708; decide +kernel
      have hl : raw17708step0Labels = raw17708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17708 raw17708Labels permutation346 hz
    mixedMoment B raw17708step0 raw17708step0Labels = mixedMoment B raw17708step1 raw17708step1Labels := by
      have ha : raw17708step1 = (fun i j => raw17708step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17708step1 raw17708step0; decide +kernel
      have hl : raw17708step1Labels = raw17708step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17708step0 raw17708step0Labels permutation32 permutation3
    mixedMoment B raw17708step1 raw17708step1Labels = mixedMoment B raw17708step2 raw17708step2Labels := by
      have ha : raw17708step2 = raw17708step1 := by apply Matrix.ext; unfold raw17708step2 raw17708step1; decide +kernel
      have hl : raw17708step1Labels = labelEmbedding6 ∘ raw17708step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17708step1 raw17708step1Labels raw17708step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

theorem canonical17713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17713 raw17713Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw17713 raw17713Labels = mixedMoment B raw17713step0 raw17713step0Labels := by
      have ha : raw17713step0 = (fun i j => raw17713 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17713step0 raw17713; decide +kernel
      have hl : raw17713step0Labels = raw17713Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17713 raw17713Labels permutation160 permutation3
    mixedMoment B raw17713step0 raw17713step0Labels = mixedMoment B raw17713step1 raw17713step1Labels := by
      have ha : raw17713step1 = raw17713step0 := by apply Matrix.ext; unfold raw17713step1 raw17713step0; decide +kernel
      have hl : raw17713step0Labels = labelEmbedding6 ∘ raw17713step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17713step0 raw17713step0Labels raw17713step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5145 node5145Labels := by rfl

theorem canonical17718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17718 raw17718Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw17718 raw17718Labels = mixedMoment B raw17718step0 raw17718step0Labels := by
      have hz : ∀ j, raw17718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17718step0 = (fun i j => raw17718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17718step0 raw17718; decide +kernel
      have hl : raw17718step0Labels = raw17718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17718 raw17718Labels permutation346 hz
    mixedMoment B raw17718step0 raw17718step0Labels = mixedMoment B raw17718step1 raw17718step1Labels := by
      have ha : raw17718step1 = (fun i j => raw17718step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17718step1 raw17718step0; decide +kernel
      have hl : raw17718step1Labels = raw17718step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17718step0 raw17718step0Labels permutation34 permutation3
    mixedMoment B raw17718step1 raw17718step1Labels = mixedMoment B raw17718step2 raw17718step2Labels := by
      have ha : raw17718step2 = raw17718step1 := by apply Matrix.ext; unfold raw17718step2 raw17718step1; decide +kernel
      have hl : raw17718step1Labels = labelEmbedding6 ∘ raw17718step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17718step1 raw17718step1Labels raw17718step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5164 node5164Labels := by rfl

theorem canonical17724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17724 raw17724Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw17724 raw17724Labels = mixedMoment B raw17724step0 raw17724step0Labels := by
      have hz : ∀ j, raw17724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17724step0 = (fun i j => raw17724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17724step0 raw17724; decide +kernel
      have hl : raw17724step0Labels = raw17724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17724 raw17724Labels permutation346 hz
    mixedMoment B raw17724step0 raw17724step0Labels = mixedMoment B raw17724step1 raw17724step1Labels := by
      have ha : raw17724step1 = (fun i j => raw17724step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17724step1 raw17724step0; decide +kernel
      have hl : raw17724step1Labels = raw17724step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17724step0 raw17724step0Labels permutation126 permutation2
    mixedMoment B raw17724step1 raw17724step1Labels = mixedMoment B raw17724step2 raw17724step2Labels := by
      have ha : raw17724step2 = -raw17724step1 := by apply Matrix.ext; change ∀ i j, raw17724step2 i j = -(raw17724step1 i j); unfold raw17724step2 raw17724step1; decide +kernel
      have hl : raw17724step2Labels = raw17724step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5356 node5356Labels := by rfl

theorem canonical17725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17725 raw17725Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw17725 raw17725Labels = mixedMoment B raw17725step0 raw17725step0Labels := by
      have ha : raw17725step0 = (fun i j => raw17725 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17725step0 raw17725; decide +kernel
      have hl : raw17725step0Labels = raw17725Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17725 raw17725Labels permutation589 permutation2
    mixedMoment B raw17725step0 raw17725step0Labels = mixedMoment B raw17725step1 raw17725step1Labels := by
      have ha : raw17725step1 = -raw17725step0 := by apply Matrix.ext; change ∀ i j, raw17725step1 i j = -(raw17725step0 i j); unfold raw17725step1 raw17725step0; decide +kernel
      have hl : raw17725step1Labels = raw17725step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5352 node5352Labels := by rfl

theorem canonical17726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17726 raw17726Labels = mixedMoment B node5369 node5369Labels := by
  calc
    mixedMoment B raw17726 raw17726Labels = mixedMoment B raw17726step0 raw17726step0Labels := by
      have hz : ∀ j, raw17726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17726step0 = (fun i j => raw17726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17726step0 raw17726; decide +kernel
      have hl : raw17726step0Labels = raw17726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17726 raw17726Labels permutation346 hz
    mixedMoment B raw17726step0 raw17726step0Labels = mixedMoment B raw17726step1 raw17726step1Labels := by
      have ha : raw17726step1 = (fun i j => raw17726step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17726step1 raw17726step0; decide +kernel
      have hl : raw17726step1Labels = raw17726step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17726step0 raw17726step0Labels permutation125 permutation2
    mixedMoment B raw17726step1 raw17726step1Labels = mixedMoment B raw17726step2 raw17726step2Labels := by
      have ha : raw17726step2 = -raw17726step1 := by apply Matrix.ext; change ∀ i j, raw17726step2 i j = -(raw17726step1 i j); unfold raw17726step2 raw17726step1; decide +kernel
      have hl : raw17726step2Labels = raw17726step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5369 node5369Labels := by rfl

theorem canonical17727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17727 raw17727Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw17727 raw17727Labels = mixedMoment B raw17727step0 raw17727step0Labels := by
      have hz : ∀ j, raw17727 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17727step0 = (fun i j => raw17727 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17727step0 raw17727; decide +kernel
      have hl : raw17727step0Labels = raw17727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17727 raw17727Labels permutation346 hz
    mixedMoment B raw17727step0 raw17727step0Labels = mixedMoment B raw17727step1 raw17727step1Labels := by
      have ha : raw17727step1 = (fun i j => raw17727step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17727step1 raw17727step0; decide +kernel
      have hl : raw17727step1Labels = raw17727step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17727step0 raw17727step0Labels permutation127 permutation2
    mixedMoment B raw17727step1 raw17727step1Labels = mixedMoment B raw17727step2 raw17727step2Labels := by
      have ha : raw17727step2 = -raw17727step1 := by apply Matrix.ext; change ∀ i j, raw17727step2 i j = -(raw17727step1 i j); unfold raw17727step2 raw17727step1; decide +kernel
      have hl : raw17727step2Labels = raw17727step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5410 node5410Labels := by rfl

theorem canonical17728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17728 raw17728Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw17728 raw17728Labels = mixedMoment B raw17728step0 raw17728step0Labels := by
      have hz : ∀ j, raw17728 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17728step0 = (fun i j => raw17728 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17728step0 raw17728; decide +kernel
      have hl : raw17728step0Labels = raw17728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17728 raw17728Labels permutation346 hz
    mixedMoment B raw17728step0 raw17728step0Labels = mixedMoment B raw17728step1 raw17728step1Labels := by
      have ha : raw17728step1 = (fun i j => raw17728step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17728step1 raw17728step0; decide +kernel
      have hl : raw17728step1Labels = raw17728step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17728step0 raw17728step0Labels permutation32 permutation3
    mixedMoment B raw17728step1 raw17728step1Labels = mixedMoment B raw17728step2 raw17728step2Labels := by
      have ha : raw17728step2 = raw17728step1 := by apply Matrix.ext; unfold raw17728step2 raw17728step1; decide +kernel
      have hl : raw17728step1Labels = labelEmbedding6 ∘ raw17728step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17728step1 raw17728step1Labels raw17728step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5147 node5147Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1917 raw1917Labels = mixedMoment B node4948 node4948Labels := by
  calc
    mixedMoment B raw1917 raw1917Labels = mixedMoment B raw1917step0 raw1917step0Labels := by
      have ha : raw1917step0 = (fun i j => raw1917 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1917step0 raw1917; decide +kernel
      have hl : raw1917step0Labels = raw1917Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1917 raw1917Labels permutation32 permutation4
    mixedMoment B raw1917step0 raw1917step0Labels = mixedMoment B raw1917step1 raw1917step1Labels := by
      have ha : raw1917step1 = raw1917step0 := by apply Matrix.ext; unfold raw1917step1 raw1917step0; decide +kernel
      have hl : raw1917step0Labels = labelEmbedding7 ∘ raw1917step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1917step0 raw1917step0Labels raw1917step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4948 node4948Labels := by rfl

theorem canonical1918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1918 raw1918Labels = mixedMoment B node2339 node2339Labels := by
  calc
    mixedMoment B raw1918 raw1918Labels = mixedMoment B raw1918step0 raw1918step0Labels := by
      have ha : raw1918step0 = (fun i j => raw1918 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1918step0 raw1918; decide +kernel
      have hl : raw1918step0Labels = raw1918Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1918 raw1918Labels permutation32 permutation4
    _ = mixedMoment B node2339 node2339Labels := by rfl

theorem canonical1919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1919 raw1919Labels = mixedMoment B node3420 node3420Labels := by
  calc
    mixedMoment B raw1919 raw1919Labels = mixedMoment B raw1919step0 raw1919step0Labels := by
      have ha : raw1919step0 = (fun i j => raw1919 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1919step0 raw1919; decide +kernel
      have hl : raw1919step0Labels = raw1919Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1919 raw1919Labels permutation32 permutation6
    mixedMoment B raw1919step0 raw1919step0Labels = mixedMoment B raw1919step1 raw1919step1Labels := by
      have ha : raw1919step1 = -raw1919step0 := by apply Matrix.ext; change ∀ i j, raw1919step1 i j = -(raw1919step0 i j); unfold raw1919step1 raw1919step0; decide +kernel
      have hl : raw1919step1Labels = raw1919step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1919step1 raw1919step1Labels = mixedMoment B raw1919step2 raw1919step2Labels := by
      have ha : raw1919step2 = raw1919step1 := by apply Matrix.ext; unfold raw1919step2 raw1919step1; decide +kernel
      have hl : raw1919step1Labels = labelEmbedding1 ∘ raw1919step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1919step1 raw1919step1Labels raw1919step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3420 node3420Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1950 raw1950Labels = mixedMoment B node4970 node4970Labels := by
  calc
    mixedMoment B raw1950 raw1950Labels = mixedMoment B raw1950step0 raw1950step0Labels := by
      have ha : raw1950step0 = (fun i j => raw1950 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1950step0 raw1950; decide +kernel
      have hl : raw1950step0Labels = raw1950Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1950 raw1950Labels permutation32 permutation5
    mixedMoment B raw1950step0 raw1950step0Labels = mixedMoment B raw1950step1 raw1950step1Labels := by
      have ha : raw1950step1 = raw1950step0 := by apply Matrix.ext; unfold raw1950step1 raw1950step0; decide +kernel
      have hl : raw1950step0Labels = labelEmbedding8 ∘ raw1950step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1950step0 raw1950step0Labels raw1950step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4970 node4970Labels := by rfl

theorem canonical1951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1951 raw1951Labels = mixedMoment B node2815 node2815Labels := by
  calc
    mixedMoment B raw1951 raw1951Labels = mixedMoment B raw1951step0 raw1951step0Labels := by
      have ha : raw1951step0 = (fun i j => raw1951 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1951step0 raw1951; decide +kernel
      have hl : raw1951step0Labels = raw1951Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1951 raw1951Labels permutation32 permutation4
    _ = mixedMoment B node2815 node2815Labels := by rfl

theorem canonical1952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1952 raw1952Labels = mixedMoment B node3588 node3588Labels := by
  calc
    mixedMoment B raw1952 raw1952Labels = mixedMoment B raw1952step0 raw1952step0Labels := by
      have ha : raw1952step0 = (fun i j => raw1952 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1952step0 raw1952; decide +kernel
      have hl : raw1952step0Labels = raw1952Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1952 raw1952Labels permutation32 permutation3
    mixedMoment B raw1952step0 raw1952step0Labels = mixedMoment B raw1952step1 raw1952step1Labels := by
      have ha : raw1952step1 = -raw1952step0 := by apply Matrix.ext; change ∀ i j, raw1952step1 i j = -(raw1952step0 i j); unfold raw1952step1 raw1952step0; decide +kernel
      have hl : raw1952step1Labels = raw1952step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1952step1 raw1952step1Labels = mixedMoment B raw1952step2 raw1952step2Labels := by
      have ha : raw1952step2 = raw1952step1 := by apply Matrix.ext; unfold raw1952step2 raw1952step1; decide +kernel
      have hl : raw1952step1Labels = labelEmbedding1 ∘ raw1952step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1952step1 raw1952step1Labels raw1952step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3588 node3588Labels := by rfl

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

theorem canonical2103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2103 raw2103Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw2103 raw2103Labels = mixedMoment B raw2103step0 raw2103step0Labels := by
      have ha : raw2103step0 = (fun i j => raw2103 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2103step0 raw2103; decide +kernel
      have hl : raw2103step0Labels = raw2103Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2103 raw2103Labels permutation32 permutation4
    mixedMoment B raw2103step0 raw2103step0Labels = mixedMoment B raw2103step1 raw2103step1Labels := by
      have ha : raw2103step1 = raw2103step0 := by apply Matrix.ext; unfold raw2103step1 raw2103step0; decide +kernel
      have hl : raw2103step0Labels = labelEmbedding7 ∘ raw2103step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2103step0 raw2103step0Labels raw2103step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

theorem canonical2104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2104 raw2104Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw2104 raw2104Labels = mixedMoment B raw2104step0 raw2104step0Labels := by
      have ha : raw2104step0 = (fun i j => raw2104 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2104step0 raw2104; decide +kernel
      have hl : raw2104step0Labels = raw2104Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2104 raw2104Labels permutation32 permutation4
    _ = mixedMoment B node2485 node2485Labels := by rfl

theorem canonical2105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2105 raw2105Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw2105 raw2105Labels = mixedMoment B raw2105step0 raw2105step0Labels := by
      have ha : raw2105step0 = (fun i j => raw2105 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2105step0 raw2105; decide +kernel
      have hl : raw2105step0Labels = raw2105Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2105 raw2105Labels permutation32 permutation6
    mixedMoment B raw2105step0 raw2105step0Labels = mixedMoment B raw2105step1 raw2105step1Labels := by
      have ha : raw2105step1 = -raw2105step0 := by apply Matrix.ext; change ∀ i j, raw2105step1 i j = -(raw2105step0 i j); unfold raw2105step1 raw2105step0; decide +kernel
      have hl : raw2105step1Labels = raw2105step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2105step1 raw2105step1Labels = mixedMoment B raw2105step2 raw2105step2Labels := by
      have ha : raw2105step2 = raw2105step1 := by apply Matrix.ext; unfold raw2105step2 raw2105step1; decide +kernel
      have hl : raw2105step1Labels = labelEmbedding1 ∘ raw2105step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2105step1 raw2105step1Labels raw2105step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

theorem canonical2142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2142 raw2142Labels = mixedMoment B node5117 node5117Labels := by
  calc
    mixedMoment B raw2142 raw2142Labels = mixedMoment B raw2142step0 raw2142step0Labels := by
      have ha : raw2142step0 = (fun i j => raw2142 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2142step0 raw2142; decide +kernel
      have hl : raw2142step0Labels = raw2142Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2142 raw2142Labels permutation152 permutation5
    mixedMoment B raw2142step0 raw2142step0Labels = mixedMoment B raw2142step1 raw2142step1Labels := by
      have ha : raw2142step1 = raw2142step0 := by apply Matrix.ext; unfold raw2142step1 raw2142step0; decide +kernel
      have hl : raw2142step0Labels = labelEmbedding8 ∘ raw2142step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2142step0 raw2142step0Labels raw2142step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5117 node5117Labels := by rfl

theorem canonical2143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2143 raw2143Labels = mixedMoment B node2893 node2893Labels := by
  calc
    mixedMoment B raw2143 raw2143Labels = mixedMoment B raw2143step0 raw2143step0Labels := by
      have ha : raw2143step0 = (fun i j => raw2143 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2143step0 raw2143; decide +kernel
      have hl : raw2143step0Labels = raw2143Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2143 raw2143Labels permutation153 permutation4
    _ = mixedMoment B node2893 node2893Labels := by rfl

theorem canonical2144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2144 raw2144Labels = mixedMoment B node3599 node3599Labels := by
  calc
    mixedMoment B raw2144 raw2144Labels = mixedMoment B raw2144step0 raw2144step0Labels := by
      have ha : raw2144step0 = (fun i j => raw2144 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2144step0 raw2144; decide +kernel
      have hl : raw2144step0Labels = raw2144Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2144 raw2144Labels permutation154 permutation3
    mixedMoment B raw2144step0 raw2144step0Labels = mixedMoment B raw2144step1 raw2144step1Labels := by
      have ha : raw2144step1 = -raw2144step0 := by apply Matrix.ext; change ∀ i j, raw2144step1 i j = -(raw2144step0 i j); unfold raw2144step1 raw2144step0; decide +kernel
      have hl : raw2144step1Labels = raw2144step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2144step1 raw2144step1Labels = mixedMoment B raw2144step2 raw2144step2Labels := by
      have ha : raw2144step2 = raw2144step1 := by apply Matrix.ext; unfold raw2144step2 raw2144step1; decide +kernel
      have hl : raw2144step1Labels = labelEmbedding1 ∘ raw2144step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2144step1 raw2144step1Labels raw2144step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3599 node3599Labels := by rfl

theorem canonical2175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2175 raw2175Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw2175 raw2175Labels = mixedMoment B raw2175step0 raw2175step0Labels := by
      have ha : raw2175step0 = (fun i j => raw2175 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2175step0 raw2175; decide +kernel
      have hl : raw2175step0Labels = raw2175Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2175 raw2175Labels permutation152 permutation5
    mixedMoment B raw2175step0 raw2175step0Labels = mixedMoment B raw2175step1 raw2175step1Labels := by
      have ha : raw2175step1 = raw2175step0 := by apply Matrix.ext; unfold raw2175step1 raw2175step0; decide +kernel
      have hl : raw2175step0Labels = labelEmbedding8 ∘ raw2175step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2175step0 raw2175step0Labels raw2175step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical2176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2176 raw2176Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw2176 raw2176Labels = mixedMoment B raw2176step0 raw2176step0Labels := by
      have ha : raw2176step0 = (fun i j => raw2176 (permutation154 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2176step0 raw2176; decide +kernel
      have hl : raw2176step0Labels = raw2176Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2176 raw2176Labels permutation154 permutation4
    _ = mixedMoment B node2924 node2924Labels := by rfl

theorem canonical2177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2177 raw2177Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw2177 raw2177Labels = mixedMoment B raw2177step0 raw2177step0Labels := by
      have ha : raw2177step0 = (fun i j => raw2177 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2177step0 raw2177; decide +kernel
      have hl : raw2177step0Labels = raw2177Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2177 raw2177Labels permutation162 permutation3
    mixedMoment B raw2177step0 raw2177step0Labels = mixedMoment B raw2177step1 raw2177step1Labels := by
      have ha : raw2177step1 = -raw2177step0 := by apply Matrix.ext; change ∀ i j, raw2177step1 i j = -(raw2177step0 i j); unfold raw2177step1 raw2177step0; decide +kernel
      have hl : raw2177step1Labels = raw2177step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2177step1 raw2177step1Labels = mixedMoment B raw2177step2 raw2177step2Labels := by
      have ha : raw2177step2 = raw2177step1 := by apply Matrix.ext; unfold raw2177step2 raw2177step1; decide +kernel
      have hl : raw2177step1Labels = labelEmbedding1 ∘ raw2177step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2177step1 raw2177step1Labels raw2177step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

theorem canonical2178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2178 raw2178Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw2178 raw2178Labels = mixedMoment B raw2178step0 raw2178step0Labels := by
      have ha : raw2178step0 = (fun i j => raw2178 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2178step0 raw2178; decide +kernel
      have hl : raw2178step0Labels = raw2178Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2178 raw2178Labels permutation32 permutation5
    mixedMoment B raw2178step0 raw2178step0Labels = mixedMoment B raw2178step1 raw2178step1Labels := by
      have ha : raw2178step1 = raw2178step0 := by apply Matrix.ext; unfold raw2178step1 raw2178step0; decide +kernel
      have hl : raw2178step0Labels = labelEmbedding8 ∘ raw2178step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2178step0 raw2178step0Labels raw2178step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

theorem canonical2179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2179 raw2179Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw2179 raw2179Labels = mixedMoment B raw2179step0 raw2179step0Labels := by
      have ha : raw2179step0 = (fun i j => raw2179 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2179step0 raw2179; decide +kernel
      have hl : raw2179step0Labels = raw2179Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2179 raw2179Labels permutation33 permutation4
    _ = mixedMoment B node2931 node2931Labels := by rfl

theorem canonical2180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2180 raw2180Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw2180 raw2180Labels = mixedMoment B raw2180step0 raw2180step0Labels := by
      have ha : raw2180step0 = (fun i j => raw2180 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2180step0 raw2180; decide +kernel
      have hl : raw2180step0Labels = raw2180Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2180 raw2180Labels permutation34 permutation3
    mixedMoment B raw2180step0 raw2180step0Labels = mixedMoment B raw2180step1 raw2180step1Labels := by
      have ha : raw2180step1 = -raw2180step0 := by apply Matrix.ext; change ∀ i j, raw2180step1 i j = -(raw2180step0 i j); unfold raw2180step1 raw2180step0; decide +kernel
      have hl : raw2180step1Labels = raw2180step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2180step1 raw2180step1Labels = mixedMoment B raw2180step2 raw2180step2Labels := by
      have ha : raw2180step2 = raw2180step1 := by apply Matrix.ext; unfold raw2180step2 raw2180step1; decide +kernel
      have hl : raw2180step1Labels = labelEmbedding1 ∘ raw2180step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2180step1 raw2180step1Labels raw2180step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3612 node3612Labels := by rfl

theorem canonical2202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2202 raw2202Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw2202 raw2202Labels = mixedMoment B raw2202step0 raw2202step0Labels := by
      have ha : raw2202step0 = (fun i j => raw2202 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2202step0 raw2202; decide +kernel
      have hl : raw2202step0Labels = raw2202Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2202 raw2202Labels permutation32 permutation5
    mixedMoment B raw2202step0 raw2202step0Labels = mixedMoment B raw2202step1 raw2202step1Labels := by
      have ha : raw2202step1 = raw2202step0 := by apply Matrix.ext; unfold raw2202step1 raw2202step0; decide +kernel
      have hl : raw2202step0Labels = labelEmbedding8 ∘ raw2202step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2202step0 raw2202step0Labels raw2202step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

theorem canonical2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2203 raw2203Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw2203 raw2203Labels = mixedMoment B raw2203step0 raw2203step0Labels := by
      have ha : raw2203step0 = (fun i j => raw2203 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2203step0 raw2203; decide +kernel
      have hl : raw2203step0Labels = raw2203Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2203 raw2203Labels permutation34 permutation4
    _ = mixedMoment B node2954 node2954Labels := by rfl

theorem canonical2204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2204 raw2204Labels = mixedMoment B node3606 node3606Labels := by
  calc
    mixedMoment B raw2204 raw2204Labels = mixedMoment B raw2204step0 raw2204step0Labels := by
      have ha : raw2204step0 = (fun i j => raw2204 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2204step0 raw2204; decide +kernel
      have hl : raw2204step0Labels = raw2204Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2204 raw2204Labels permutation33 permutation3
    mixedMoment B raw2204step0 raw2204step0Labels = mixedMoment B raw2204step1 raw2204step1Labels := by
      have ha : raw2204step1 = -raw2204step0 := by apply Matrix.ext; change ∀ i j, raw2204step1 i j = -(raw2204step0 i j); unfold raw2204step1 raw2204step0; decide +kernel
      have hl : raw2204step1Labels = raw2204step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2204step1 raw2204step1Labels = mixedMoment B raw2204step2 raw2204step2Labels := by
      have ha : raw2204step2 = raw2204step1 := by apply Matrix.ext; unfold raw2204step2 raw2204step1; decide +kernel
      have hl : raw2204step1Labels = labelEmbedding1 ∘ raw2204step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2204step1 raw2204step1Labels raw2204step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3606 node3606Labels := by rfl

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

theorem canonical2394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2394 raw2394Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw2394 raw2394Labels = mixedMoment B raw2394step0 raw2394step0Labels := by
      have ha : raw2394step0 = (fun i j => raw2394 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2394step0 raw2394; decide +kernel
      have hl : raw2394step0Labels = raw2394Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2394 raw2394Labels permutation152 permutation4
    mixedMoment B raw2394step0 raw2394step0Labels = mixedMoment B raw2394step1 raw2394step1Labels := by
      have ha : raw2394step1 = raw2394step0 := by apply Matrix.ext; unfold raw2394step1 raw2394step0; decide +kernel
      have hl : raw2394step0Labels = labelEmbedding7 ∘ raw2394step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2394step0 raw2394step0Labels raw2394step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

theorem canonical2395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2395 raw2395Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw2395 raw2395Labels = mixedMoment B raw2395step0 raw2395step0Labels := by
      have ha : raw2395step0 = (fun i j => raw2395 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2395step0 raw2395; decide +kernel
      have hl : raw2395step0Labels = raw2395Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2395 raw2395Labels permutation152 permutation4
    _ = mixedMoment B node3690 node3690Labels := by rfl

theorem canonical2396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2396 raw2396Labels = mixedMoment B node3764 node3764Labels := by
  calc
    mixedMoment B raw2396 raw2396Labels = mixedMoment B raw2396step0 raw2396step0Labels := by
      have ha : raw2396step0 = (fun i j => raw2396 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2396step0 raw2396; decide +kernel
      have hl : raw2396step0Labels = raw2396Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2396 raw2396Labels permutation158 permutation6
    mixedMoment B raw2396step0 raw2396step0Labels = mixedMoment B raw2396step1 raw2396step1Labels := by
      have ha : raw2396step1 = -raw2396step0 := by apply Matrix.ext; change ∀ i j, raw2396step1 i j = -(raw2396step0 i j); unfold raw2396step1 raw2396step0; decide +kernel
      have hl : raw2396step1Labels = raw2396step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2396step1 raw2396step1Labels = mixedMoment B raw2396step2 raw2396step2Labels := by
      have ha : raw2396step2 = raw2396step1 := by apply Matrix.ext; unfold raw2396step2 raw2396step1; decide +kernel
      have hl : raw2396step1Labels = labelEmbedding1 ∘ raw2396step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2396step1 raw2396step1Labels raw2396step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3764 node3764Labels := by rfl

theorem canonical2403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2403 raw2403Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw2403 raw2403Labels = mixedMoment B raw2403step0 raw2403step0Labels := by
      have ha : raw2403step0 = (fun i j => raw2403 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2403step0 raw2403; decide +kernel
      have hl : raw2403step0Labels = raw2403Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2403 raw2403Labels permutation32 permutation4
    mixedMoment B raw2403step0 raw2403step0Labels = mixedMoment B raw2403step1 raw2403step1Labels := by
      have ha : raw2403step1 = raw2403step0 := by apply Matrix.ext; unfold raw2403step1 raw2403step0; decide +kernel
      have hl : raw2403step0Labels = labelEmbedding7 ∘ raw2403step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2403step0 raw2403step0Labels raw2403step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

theorem canonical2404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2404 raw2404Labels = mixedMoment B node3694 node3694Labels := by
  calc
    mixedMoment B raw2404 raw2404Labels = mixedMoment B raw2404step0 raw2404step0Labels := by
      have ha : raw2404step0 = (fun i j => raw2404 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2404step0 raw2404; decide +kernel
      have hl : raw2404step0Labels = raw2404Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2404 raw2404Labels permutation32 permutation4
    _ = mixedMoment B node3694 node3694Labels := by rfl

theorem canonical2405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2405 raw2405Labels = mixedMoment B node3773 node3773Labels := by
  calc
    mixedMoment B raw2405 raw2405Labels = mixedMoment B raw2405step0 raw2405step0Labels := by
      have ha : raw2405step0 = (fun i j => raw2405 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2405step0 raw2405; decide +kernel
      have hl : raw2405step0Labels = raw2405Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2405 raw2405Labels permutation32 permutation6
    mixedMoment B raw2405step0 raw2405step0Labels = mixedMoment B raw2405step1 raw2405step1Labels := by
      have ha : raw2405step1 = -raw2405step0 := by apply Matrix.ext; change ∀ i j, raw2405step1 i j = -(raw2405step0 i j); unfold raw2405step1 raw2405step0; decide +kernel
      have hl : raw2405step1Labels = raw2405step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2405step1 raw2405step1Labels = mixedMoment B raw2405step2 raw2405step2Labels := by
      have ha : raw2405step2 = raw2405step1 := by apply Matrix.ext; unfold raw2405step2 raw2405step1; decide +kernel
      have hl : raw2405step1Labels = labelEmbedding1 ∘ raw2405step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2405step1 raw2405step1Labels raw2405step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3773 node3773Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2589 raw2589Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw2589 raw2589Labels = mixedMoment B raw2589step0 raw2589step0Labels := by
      have ha : raw2589step0 = (fun i j => raw2589 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2589step0 raw2589; decide +kernel
      have hl : raw2589step0Labels = raw2589Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2589 raw2589Labels permutation32 permutation4
    mixedMoment B raw2589step0 raw2589step0Labels = mixedMoment B raw2589step1 raw2589step1Labels := by
      have ha : raw2589step1 = raw2589step0 := by apply Matrix.ext; unfold raw2589step1 raw2589step0; decide +kernel
      have hl : raw2589step0Labels = labelEmbedding7 ∘ raw2589step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2589step0 raw2589step0Labels raw2589step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical2590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2590 raw2590Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw2590 raw2590Labels = mixedMoment B raw2590step0 raw2590step0Labels := by
      have ha : raw2590step0 = (fun i j => raw2590 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2590step0 raw2590; decide +kernel
      have hl : raw2590step0Labels = raw2590Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2590 raw2590Labels permutation32 permutation4
    _ = mixedMoment B node3958 node3958Labels := by rfl

theorem canonical2591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2591 raw2591Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw2591 raw2591Labels = mixedMoment B raw2591step0 raw2591step0Labels := by
      have ha : raw2591step0 = (fun i j => raw2591 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2591step0 raw2591; decide +kernel
      have hl : raw2591step0Labels = raw2591Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2591 raw2591Labels permutation56 permutation6
    mixedMoment B raw2591step0 raw2591step0Labels = mixedMoment B raw2591step1 raw2591step1Labels := by
      have ha : raw2591step1 = -raw2591step0 := by apply Matrix.ext; change ∀ i j, raw2591step1 i j = -(raw2591step0 i j); unfold raw2591step1 raw2591step0; decide +kernel
      have hl : raw2591step1Labels = raw2591step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2591step1 raw2591step1Labels = mixedMoment B raw2591step2 raw2591step2Labels := by
      have ha : raw2591step2 = raw2591step1 := by apply Matrix.ext; unfold raw2591step2 raw2591step1; decide +kernel
      have hl : raw2591step1Labels = labelEmbedding1 ∘ raw2591step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2591step1 raw2591step1Labels raw2591step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical232
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29735 raw29735Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw29735 raw29735Labels = mixedMoment B raw29735step0 raw29735step0Labels := by
      have hz : ∀ j, raw29735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29735step0 = (fun i j => raw29735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29735step0 raw29735; decide +kernel
      have hl : raw29735step0Labels = raw29735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29735 raw29735Labels permutation346 hz
    mixedMoment B raw29735step0 raw29735step0Labels = mixedMoment B raw29735step1 raw29735step1Labels := by
      have ha : raw29735step1 = (fun i j => raw29735step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29735step1 raw29735step0; decide +kernel
      have hl : raw29735step1Labels = raw29735step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29735step0 raw29735step0Labels permutation151 permutation2
    mixedMoment B raw29735step1 raw29735step1Labels = mixedMoment B raw29735step2 raw29735step2Labels := by
      have ha : raw29735step2 = -raw29735step1 := by apply Matrix.ext; change ∀ i j, raw29735step2 i j = -(raw29735step1 i j); unfold raw29735step2 raw29735step1; decide +kernel
      have hl : raw29735step2Labels = raw29735step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical29736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29736 raw29736Labels = mixedMoment B node4444 node4444Labels := by
  calc
    mixedMoment B raw29736 raw29736Labels = mixedMoment B raw29736step0 raw29736step0Labels := by
      have hz : ∀ j, raw29736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29736step0 = (fun i j => raw29736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29736step0 raw29736; decide +kernel
      have hl : raw29736step0Labels = raw29736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29736 raw29736Labels permutation346 hz
    mixedMoment B raw29736step0 raw29736step0Labels = mixedMoment B raw29736step1 raw29736step1Labels := by
      have ha : raw29736step1 = (fun i j => raw29736step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29736step1 raw29736step0; decide +kernel
      have hl : raw29736step1Labels = raw29736step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29736step0 raw29736step0Labels permutation32 permutation3
    mixedMoment B raw29736step1 raw29736step1Labels = mixedMoment B raw29736step2 raw29736step2Labels := by
      have ha : raw29736step2 = raw29736step1 := by apply Matrix.ext; unfold raw29736step2 raw29736step1; decide +kernel
      have hl : raw29736step1Labels = labelEmbedding6 ∘ raw29736step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29736step1 raw29736step1Labels raw29736step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4444 node4444Labels := by rfl

theorem canonical29737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29737 raw29737Labels = mixedMoment B node5067 node5067Labels := by
  calc
    mixedMoment B raw29737 raw29737Labels = mixedMoment B raw29737step0 raw29737step0Labels := by
      have ha : raw29737step0 = (fun i j => raw29737 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29737step0 raw29737; decide +kernel
      have hl : raw29737step0Labels = raw29737Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29737 raw29737Labels permutation176 permutation3
    mixedMoment B raw29737step0 raw29737step0Labels = mixedMoment B raw29737step1 raw29737step1Labels := by
      have ha : raw29737step1 = raw29737step0 := by apply Matrix.ext; unfold raw29737step1 raw29737step0; decide +kernel
      have hl : raw29737step0Labels = labelEmbedding6 ∘ raw29737step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29737step0 raw29737step0Labels raw29737step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5067 node5067Labels := by rfl

theorem canonical29738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29738 raw29738Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw29738 raw29738Labels = mixedMoment B raw29738step0 raw29738step0Labels := by
      have hz : ∀ j, raw29738 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29738step0 = (fun i j => raw29738 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29738step0 raw29738; decide +kernel
      have hl : raw29738step0Labels = raw29738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29738 raw29738Labels permutation346 hz
    mixedMoment B raw29738step0 raw29738step0Labels = mixedMoment B raw29738step1 raw29738step1Labels := by
      have ha : raw29738step1 = (fun i j => raw29738step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29738step1 raw29738step0; decide +kernel
      have hl : raw29738step1Labels = raw29738step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29738step0 raw29738step0Labels permutation38 permutation3
    mixedMoment B raw29738step1 raw29738step1Labels = mixedMoment B raw29738step2 raw29738step2Labels := by
      have ha : raw29738step2 = raw29738step1 := by apply Matrix.ext; unfold raw29738step2 raw29738step1; decide +kernel
      have hl : raw29738step1Labels = labelEmbedding6 ∘ raw29738step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29738step1 raw29738step1Labels raw29738step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

theorem canonical29739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29739 raw29739Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw29739 raw29739Labels = mixedMoment B raw29739step0 raw29739step0Labels := by
      have hz : ∀ j, raw29739 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29739step0 = (fun i j => raw29739 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29739step0 raw29739; decide +kernel
      have hl : raw29739step0Labels = raw29739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29739 raw29739Labels permutation346 hz
    mixedMoment B raw29739step0 raw29739step0Labels = mixedMoment B raw29739step1 raw29739step1Labels := by
      have ha : raw29739step1 = (fun i j => raw29739step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29739step1 raw29739step0; decide +kernel
      have hl : raw29739step1Labels = raw29739step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29739step0 raw29739step0Labels permutation33 permutation3
    mixedMoment B raw29739step1 raw29739step1Labels = mixedMoment B raw29739step2 raw29739step2Labels := by
      have ha : raw29739step2 = raw29739step1 := by apply Matrix.ext; unfold raw29739step2 raw29739step1; decide +kernel
      have hl : raw29739step1Labels = labelEmbedding6 ∘ raw29739step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29739step1 raw29739step1Labels raw29739step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical29740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29740 raw29740Labels = mixedMoment B node4332 node4332Labels := by
  calc
    mixedMoment B raw29740 raw29740Labels = mixedMoment B raw29740step0 raw29740step0Labels := by
      have ha : raw29740step0 = (fun i j => raw29740 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29740step0 raw29740; decide +kernel
      have hl : raw29740step0Labels = raw29740Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29740 raw29740Labels permutation158 permutation3
    mixedMoment B raw29740step0 raw29740step0Labels = mixedMoment B raw29740step1 raw29740step1Labels := by
      have ha : raw29740step1 = raw29740step0 := by apply Matrix.ext; unfold raw29740step1 raw29740step0; decide +kernel
      have hl : raw29740step0Labels = labelEmbedding6 ∘ raw29740step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29740step0 raw29740step0Labels raw29740step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4332 node4332Labels := by rfl

theorem canonical29741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29741 raw29741Labels = mixedMoment B node4933 node4933Labels := by
  calc
    mixedMoment B raw29741 raw29741Labels = mixedMoment B raw29741step0 raw29741step0Labels := by
      have ha : raw29741step0 = (fun i j => raw29741 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29741step0 raw29741; decide +kernel
      have hl : raw29741step0Labels = raw29741Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29741 raw29741Labels permutation158 permutation3
    mixedMoment B raw29741step0 raw29741step0Labels = mixedMoment B raw29741step1 raw29741step1Labels := by
      have ha : raw29741step1 = raw29741step0 := by apply Matrix.ext; unfold raw29741step1 raw29741step0; decide +kernel
      have hl : raw29741step0Labels = labelEmbedding6 ∘ raw29741step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29741step0 raw29741step0Labels raw29741step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4933 node4933Labels := by rfl

theorem canonical29742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29742 raw29742Labels = mixedMoment B node5117 node5117Labels := by
  calc
    mixedMoment B raw29742 raw29742Labels = mixedMoment B raw29742step0 raw29742step0Labels := by
      have ha : raw29742step0 = (fun i j => raw29742 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29742step0 raw29742; decide +kernel
      have hl : raw29742step0Labels = raw29742Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29742 raw29742Labels permutation158 permutation3
    mixedMoment B raw29742step0 raw29742step0Labels = mixedMoment B raw29742step1 raw29742step1Labels := by
      have ha : raw29742step1 = raw29742step0 := by apply Matrix.ext; unfold raw29742step1 raw29742step0; decide +kernel
      have hl : raw29742step0Labels = labelEmbedding6 ∘ raw29742step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29742step0 raw29742step0Labels raw29742step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5117 node5117Labels := by rfl

theorem canonical29743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29743 raw29743Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw29743 raw29743Labels = mixedMoment B raw29743step0 raw29743step0Labels := by
      have ha : raw29743step0 = (fun i j => raw29743 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29743step0 raw29743; decide +kernel
      have hl : raw29743step0Labels = raw29743Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29743 raw29743Labels permutation162 permutation3
    mixedMoment B raw29743step0 raw29743step0Labels = mixedMoment B raw29743step1 raw29743step1Labels := by
      have ha : raw29743step1 = raw29743step0 := by apply Matrix.ext; unfold raw29743step1 raw29743step0; decide +kernel
      have hl : raw29743step0Labels = labelEmbedding6 ∘ raw29743step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29743step0 raw29743step0Labels raw29743step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

theorem canonical29744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29744 raw29744Labels = mixedMoment B node4357 node4357Labels := by
  calc
    mixedMoment B raw29744 raw29744Labels = mixedMoment B raw29744step0 raw29744step0Labels := by
      have hz : ∀ j, raw29744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29744step0 = (fun i j => raw29744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29744step0 raw29744; decide +kernel
      have hl : raw29744step0Labels = raw29744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29744 raw29744Labels permutation346 hz
    mixedMoment B raw29744step0 raw29744step0Labels = mixedMoment B raw29744step1 raw29744step1Labels := by
      have ha : raw29744step1 = (fun i j => raw29744step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29744step1 raw29744step0; decide +kernel
      have hl : raw29744step1Labels = raw29744step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29744step0 raw29744step0Labels permutation32 permutation3
    mixedMoment B raw29744step1 raw29744step1Labels = mixedMoment B raw29744step2 raw29744step2Labels := by
      have ha : raw29744step2 = raw29744step1 := by apply Matrix.ext; unfold raw29744step2 raw29744step1; decide +kernel
      have hl : raw29744step1Labels = labelEmbedding6 ∘ raw29744step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29744step1 raw29744step1Labels raw29744step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4357 node4357Labels := by rfl

theorem canonical29745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29745 raw29745Labels = mixedMoment B node4951 node4951Labels := by
  calc
    mixedMoment B raw29745 raw29745Labels = mixedMoment B raw29745step0 raw29745step0Labels := by
      have hz : ∀ j, raw29745 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29745step0 = (fun i j => raw29745 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29745step0 raw29745; decide +kernel
      have hl : raw29745step0Labels = raw29745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29745 raw29745Labels permutation346 hz
    mixedMoment B raw29745step0 raw29745step0Labels = mixedMoment B raw29745step1 raw29745step1Labels := by
      have ha : raw29745step1 = (fun i j => raw29745step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29745step1 raw29745step0; decide +kernel
      have hl : raw29745step1Labels = raw29745step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29745step0 raw29745step0Labels permutation32 permutation3
    mixedMoment B raw29745step1 raw29745step1Labels = mixedMoment B raw29745step2 raw29745step2Labels := by
      have ha : raw29745step2 = raw29745step1 := by apply Matrix.ext; unfold raw29745step2 raw29745step1; decide +kernel
      have hl : raw29745step1Labels = labelEmbedding6 ∘ raw29745step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29745step1 raw29745step1Labels raw29745step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4951 node4951Labels := by rfl

theorem canonical29746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29746 raw29746Labels = mixedMoment B node5040 node5040Labels := by
  calc
    mixedMoment B raw29746 raw29746Labels = mixedMoment B raw29746step0 raw29746step0Labels := by
      have ha : raw29746step0 = (fun i j => raw29746 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29746step0 raw29746; decide +kernel
      have hl : raw29746step0Labels = raw29746Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29746 raw29746Labels permutation176 permutation3
    mixedMoment B raw29746step0 raw29746step0Labels = mixedMoment B raw29746step1 raw29746step1Labels := by
      have ha : raw29746step1 = raw29746step0 := by apply Matrix.ext; unfold raw29746step1 raw29746step0; decide +kernel
      have hl : raw29746step0Labels = labelEmbedding6 ∘ raw29746step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29746step0 raw29746step0Labels raw29746step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5040 node5040Labels := by rfl

theorem canonical29747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29747 raw29747Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw29747 raw29747Labels = mixedMoment B raw29747step0 raw29747step0Labels := by
      have hz : ∀ j, raw29747 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29747step0 = (fun i j => raw29747 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29747step0 raw29747; decide +kernel
      have hl : raw29747step0Labels = raw29747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29747 raw29747Labels permutation346 hz
    mixedMoment B raw29747step0 raw29747step0Labels = mixedMoment B raw29747step1 raw29747step1Labels := by
      have ha : raw29747step1 = (fun i j => raw29747step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29747step1 raw29747step0; decide +kernel
      have hl : raw29747step1Labels = raw29747step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29747step0 raw29747step0Labels permutation36 permutation3
    mixedMoment B raw29747step1 raw29747step1Labels = mixedMoment B raw29747step2 raw29747step2Labels := by
      have ha : raw29747step2 = raw29747step1 := by apply Matrix.ext; unfold raw29747step2 raw29747step1; decide +kernel
      have hl : raw29747step1Labels = labelEmbedding6 ∘ raw29747step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29747step1 raw29747step1Labels raw29747step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

theorem canonical29748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29748 raw29748Labels = mixedMoment B node4335 node4335Labels := by
  calc
    mixedMoment B raw29748 raw29748Labels = mixedMoment B raw29748step0 raw29748step0Labels := by
      have hz : ∀ j, raw29748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29748step0 = (fun i j => raw29748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29748step0 raw29748; decide +kernel
      have hl : raw29748step0Labels = raw29748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29748 raw29748Labels permutation346 hz
    mixedMoment B raw29748step0 raw29748step0Labels = mixedMoment B raw29748step1 raw29748step1Labels := by
      have ha : raw29748step1 = (fun i j => raw29748step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29748step1 raw29748step0; decide +kernel
      have hl : raw29748step1Labels = raw29748step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29748step0 raw29748step0Labels permutation33 permutation3
    mixedMoment B raw29748step1 raw29748step1Labels = mixedMoment B raw29748step2 raw29748step2Labels := by
      have ha : raw29748step2 = raw29748step1 := by apply Matrix.ext; unfold raw29748step2 raw29748step1; decide +kernel
      have hl : raw29748step1Labels = labelEmbedding6 ∘ raw29748step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29748step1 raw29748step1Labels raw29748step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4335 node4335Labels := by rfl

theorem canonical29749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29749 raw29749Labels = mixedMoment B node4935 node4935Labels := by
  calc
    mixedMoment B raw29749 raw29749Labels = mixedMoment B raw29749step0 raw29749step0Labels := by
      have hz : ∀ j, raw29749 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29749step0 = (fun i j => raw29749 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29749step0 raw29749; decide +kernel
      have hl : raw29749step0Labels = raw29749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29749 raw29749Labels permutation346 hz
    mixedMoment B raw29749step0 raw29749step0Labels = mixedMoment B raw29749step1 raw29749step1Labels := by
      have ha : raw29749step1 = (fun i j => raw29749step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29749step1 raw29749step0; decide +kernel
      have hl : raw29749step1Labels = raw29749step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29749step0 raw29749step0Labels permutation127 permutation2
    mixedMoment B raw29749step1 raw29749step1Labels = mixedMoment B raw29749step2 raw29749step2Labels := by
      have ha : raw29749step2 = -raw29749step1 := by apply Matrix.ext; change ∀ i j, raw29749step2 i j = -(raw29749step1 i j); unfold raw29749step2 raw29749step1; decide +kernel
      have hl : raw29749step2Labels = raw29749step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4935 node4935Labels := by rfl

theorem canonical29750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29750 raw29750Labels = mixedMoment B node4930 node4930Labels := by
  calc
    mixedMoment B raw29750 raw29750Labels = mixedMoment B raw29750step0 raw29750step0Labels := by
      have ha : raw29750step0 = (fun i j => raw29750 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29750step0 raw29750; decide +kernel
      have hl : raw29750step0Labels = raw29750Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29750 raw29750Labels permutation589 permutation2
    mixedMoment B raw29750step0 raw29750step0Labels = mixedMoment B raw29750step1 raw29750step1Labels := by
      have ha : raw29750step1 = -raw29750step0 := by apply Matrix.ext; change ∀ i j, raw29750step1 i j = -(raw29750step0 i j); unfold raw29750step1 raw29750step0; decide +kernel
      have hl : raw29750step1Labels = raw29750step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4930 node4930Labels := by rfl

theorem canonical29751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29751 raw29751Labels = mixedMoment B node4948 node4948Labels := by
  calc
    mixedMoment B raw29751 raw29751Labels = mixedMoment B raw29751step0 raw29751step0Labels := by
      have hz : ∀ j, raw29751 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29751step0 = (fun i j => raw29751 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29751step0 raw29751; decide +kernel
      have hl : raw29751step0Labels = raw29751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29751 raw29751Labels permutation346 hz
    mixedMoment B raw29751step0 raw29751step0Labels = mixedMoment B raw29751step1 raw29751step1Labels := by
      have ha : raw29751step1 = (fun i j => raw29751step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29751step1 raw29751step0; decide +kernel
      have hl : raw29751step1Labels = raw29751step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29751step0 raw29751step0Labels permutation125 permutation2
    mixedMoment B raw29751step1 raw29751step1Labels = mixedMoment B raw29751step2 raw29751step2Labels := by
      have ha : raw29751step2 = -raw29751step1 := by apply Matrix.ext; change ∀ i j, raw29751step2 i j = -(raw29751step1 i j); unfold raw29751step2 raw29751step1; decide +kernel
      have hl : raw29751step2Labels = raw29751step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4948 node4948Labels := by rfl

theorem canonical29752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29752 raw29752Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw29752 raw29752Labels = mixedMoment B raw29752step0 raw29752step0Labels := by
      have hz : ∀ j, raw29752 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29752step0 = (fun i j => raw29752 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29752step0 raw29752; decide +kernel
      have hl : raw29752step0Labels = raw29752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29752 raw29752Labels permutation346 hz
    mixedMoment B raw29752step0 raw29752step0Labels = mixedMoment B raw29752step1 raw29752step1Labels := by
      have ha : raw29752step1 = (fun i j => raw29752step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29752step1 raw29752step0; decide +kernel
      have hl : raw29752step1Labels = raw29752step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29752step0 raw29752step0Labels permutation127 permutation2
    mixedMoment B raw29752step1 raw29752step1Labels = mixedMoment B raw29752step2 raw29752step2Labels := by
      have ha : raw29752step2 = -raw29752step1 := by apply Matrix.ext; change ∀ i j, raw29752step2 i j = -(raw29752step1 i j); unfold raw29752step2 raw29752step1; decide +kernel
      have hl : raw29752step2Labels = raw29752step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5078 node5078Labels := by rfl

theorem canonical29753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29753 raw29753Labels = mixedMoment B node4334 node4334Labels := by
  calc
    mixedMoment B raw29753 raw29753Labels = mixedMoment B raw29753step0 raw29753step0Labels := by
      have hz : ∀ j, raw29753 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29753step0 = (fun i j => raw29753 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29753step0 raw29753; decide +kernel
      have hl : raw29753step0Labels = raw29753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29753 raw29753Labels permutation346 hz
    mixedMoment B raw29753step0 raw29753step0Labels = mixedMoment B raw29753step1 raw29753step1Labels := by
      have ha : raw29753step1 = (fun i j => raw29753step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29753step1 raw29753step0; decide +kernel
      have hl : raw29753step1Labels = raw29753step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29753step0 raw29753step0Labels permutation32 permutation3
    mixedMoment B raw29753step1 raw29753step1Labels = mixedMoment B raw29753step2 raw29753step2Labels := by
      have ha : raw29753step2 = raw29753step1 := by apply Matrix.ext; unfold raw29753step2 raw29753step1; decide +kernel
      have hl : raw29753step1Labels = labelEmbedding6 ∘ raw29753step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29753step1 raw29753step1Labels raw29753step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4334 node4334Labels := by rfl

theorem canonical29754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29754 raw29754Labels = mixedMoment B node4934 node4934Labels := by
  calc
    mixedMoment B raw29754 raw29754Labels = mixedMoment B raw29754step0 raw29754step0Labels := by
      have hz : ∀ j, raw29754 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29754step0 = (fun i j => raw29754 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29754step0 raw29754; decide +kernel
      have hl : raw29754step0Labels = raw29754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29754 raw29754Labels permutation346 hz
    mixedMoment B raw29754step0 raw29754step0Labels = mixedMoment B raw29754step1 raw29754step1Labels := by
      have ha : raw29754step1 = (fun i j => raw29754step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29754step1 raw29754step0; decide +kernel
      have hl : raw29754step1Labels = raw29754step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29754step0 raw29754step0Labels permutation32 permutation3
    mixedMoment B raw29754step1 raw29754step1Labels = mixedMoment B raw29754step2 raw29754step2Labels := by
      have ha : raw29754step2 = raw29754step1 := by apply Matrix.ext; unfold raw29754step2 raw29754step1; decide +kernel
      have hl : raw29754step1Labels = labelEmbedding6 ∘ raw29754step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29754step1 raw29754step1Labels raw29754step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4934 node4934Labels := by rfl

theorem canonical29755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29755 raw29755Labels = mixedMoment B node4954 node4954Labels := by
  calc
    mixedMoment B raw29755 raw29755Labels = mixedMoment B raw29755step0 raw29755step0Labels := by
      have ha : raw29755step0 = (fun i j => raw29755 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29755step0 raw29755; decide +kernel
      have hl : raw29755step0Labels = raw29755Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29755 raw29755Labels permutation686 permutation3
    mixedMoment B raw29755step0 raw29755step0Labels = mixedMoment B raw29755step1 raw29755step1Labels := by
      have ha : raw29755step1 = -raw29755step0 := by apply Matrix.ext; change ∀ i j, raw29755step1 i j = -(raw29755step0 i j); unfold raw29755step1 raw29755step0; decide +kernel
      have hl : raw29755step1Labels = raw29755step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29755step1 raw29755step1Labels = mixedMoment B raw29755step2 raw29755step2Labels := by
      have ha : raw29755step2 = raw29755step1 := by apply Matrix.ext; unfold raw29755step2 raw29755step1; decide +kernel
      have hl : raw29755step1Labels = labelEmbedding6 ∘ raw29755step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29755step1 raw29755step1Labels raw29755step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4954 node4954Labels := by rfl

theorem canonical29756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29756 raw29756Labels = mixedMoment B node4970 node4970Labels := by
  calc
    mixedMoment B raw29756 raw29756Labels = mixedMoment B raw29756step0 raw29756step0Labels := by
      have hz : ∀ j, raw29756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29756step0 = (fun i j => raw29756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29756step0 raw29756; decide +kernel
      have hl : raw29756step0Labels = raw29756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29756 raw29756Labels permutation346 hz
    mixedMoment B raw29756step0 raw29756step0Labels = mixedMoment B raw29756step1 raw29756step1Labels := by
      have ha : raw29756step1 = (fun i j => raw29756step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29756step1 raw29756step0; decide +kernel
      have hl : raw29756step1Labels = raw29756step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29756step0 raw29756step0Labels permutation149 permutation3
    mixedMoment B raw29756step1 raw29756step1Labels = mixedMoment B raw29756step2 raw29756step2Labels := by
      have ha : raw29756step2 = -raw29756step1 := by apply Matrix.ext; change ∀ i j, raw29756step2 i j = -(raw29756step1 i j); unfold raw29756step2 raw29756step1; decide +kernel
      have hl : raw29756step2Labels = raw29756step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29756step2 raw29756step2Labels = mixedMoment B raw29756step3 raw29756step3Labels := by
      have ha : raw29756step3 = raw29756step2 := by apply Matrix.ext; unfold raw29756step3 raw29756step2; decide +kernel
      have hl : raw29756step2Labels = labelEmbedding6 ∘ raw29756step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29756step2 raw29756step2Labels raw29756step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4970 node4970Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4948 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4948 node4948Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2339 node2339Labels + mixedMoment B node3420 node3420Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1917 singletonSmall4948
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4948) = raw1917Labels := by decide +kernel
  rw [hl, canonical1917 B hB] at h
  have hc0 : mixedMoment B raw1917 (Fin.cases (0 : Fin 2) singletonSmall4948) =
      mixedMoment B node2339 node2339Labels := by
    have ha : raw1917 = raw1918 := by apply Matrix.ext; unfold raw1917 raw1918; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4948 = raw1918Labels := by decide +kernel
    rw [ha, hj, canonical1918 B hB]
  have hc1 : mixedMoment B raw1917 (Fin.cases (1 : Fin 2) singletonSmall4948) =
      mixedMoment B node3420 node3420Labels := by
    have ha : raw1917 = raw1919 := by apply Matrix.ext; unfold raw1917 raw1919; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4948 = raw1919Labels := by decide +kernel
    rw [ha, hj, canonical1919 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4970 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4970 node4970Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2815 node2815Labels + mixedMoment B node3588 node3588Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1950 singletonSmall4970
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4970) = raw1950Labels := by decide +kernel
  rw [hl, canonical1950 B hB] at h
  have hc0 : mixedMoment B raw1950 (Fin.cases (0 : Fin 2) singletonSmall4970) =
      mixedMoment B node2815 node2815Labels := by
    have ha : raw1950 = raw1951 := by apply Matrix.ext; unfold raw1950 raw1951; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4970 = raw1951Labels := by decide +kernel
    rw [ha, hj, canonical1951 B hB]
  have hc1 : mixedMoment B raw1950 (Fin.cases (1 : Fin 2) singletonSmall4970) =
      mixedMoment B node3588 node3588Labels := by
    have ha : raw1950 = raw1952 := by apply Matrix.ext; unfold raw1950 raw1952; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4970 = raw1952Labels := by decide +kernel
    rw [ha, hj, canonical1952 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton5078 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5078 node5078Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2485 node2485Labels + mixedMoment B node3481 node3481Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2103 singletonSmall5078
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5078) = raw2103Labels := by decide +kernel
  rw [hl, canonical2103 B hB] at h
  have hc0 : mixedMoment B raw2103 (Fin.cases (0 : Fin 2) singletonSmall5078) =
      mixedMoment B node2485 node2485Labels := by
    have ha : raw2103 = raw2104 := by apply Matrix.ext; unfold raw2103 raw2104; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5078 = raw2104Labels := by decide +kernel
    rw [ha, hj, canonical2104 B hB]
  have hc1 : mixedMoment B raw2103 (Fin.cases (1 : Fin 2) singletonSmall5078) =
      mixedMoment B node3481 node3481Labels := by
    have ha : raw2103 = raw2105 := by apply Matrix.ext; unfold raw2103 raw2105; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5078 = raw2105Labels := by decide +kernel
    rw [ha, hj, canonical2105 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5117 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5117 node5117Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2893 node2893Labels + mixedMoment B node3599 node3599Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2142 singletonSmall5117
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5117) = raw2142Labels := by decide +kernel
  rw [hl, canonical2142 B hB] at h
  have hc0 : mixedMoment B raw2142 (Fin.cases (0 : Fin 2) singletonSmall5117) =
      mixedMoment B node2893 node2893Labels := by
    have ha : raw2142 = raw2143 := by apply Matrix.ext; unfold raw2142 raw2143; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5117 = raw2143Labels := by decide +kernel
    rw [ha, hj, canonical2143 B hB]
  have hc1 : mixedMoment B raw2142 (Fin.cases (1 : Fin 2) singletonSmall5117) =
      mixedMoment B node3599 node3599Labels := by
    have ha : raw2142 = raw2144 := by apply Matrix.ext; unfold raw2142 raw2144; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5117 = raw2144Labels := by decide +kernel
    rw [ha, hj, canonical2144 B hB]
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

theorem singleton5149 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5149 node5149Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2924 node2924Labels + mixedMoment B node3605 node3605Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2175 singletonSmall5149
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5149) = raw2175Labels := by decide +kernel
  rw [hl, canonical2175 B hB] at h
  have hc0 : mixedMoment B raw2175 (Fin.cases (0 : Fin 2) singletonSmall5149) =
      mixedMoment B node2924 node2924Labels := by
    have ha : raw2175 = raw2176 := by apply Matrix.ext; unfold raw2175 raw2176; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5149 = raw2176Labels := by decide +kernel
    rw [ha, hj, canonical2176 B hB]
  have hc1 : mixedMoment B raw2175 (Fin.cases (1 : Fin 2) singletonSmall5149) =
      mixedMoment B node3605 node3605Labels := by
    have ha : raw2175 = raw2177 := by apply Matrix.ext; unfold raw2175 raw2177; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5149 = raw2177Labels := by decide +kernel
    rw [ha, hj, canonical2177 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5152 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5152 node5152Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2931 node2931Labels + mixedMoment B node3612 node3612Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2178 singletonSmall5152
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5152) = raw2178Labels := by decide +kernel
  rw [hl, canonical2178 B hB] at h
  have hc0 : mixedMoment B raw2178 (Fin.cases (0 : Fin 2) singletonSmall5152) =
      mixedMoment B node2931 node2931Labels := by
    have ha : raw2178 = raw2179 := by apply Matrix.ext; unfold raw2178 raw2179; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5152 = raw2179Labels := by decide +kernel
    rw [ha, hj, canonical2179 B hB]
  have hc1 : mixedMoment B raw2178 (Fin.cases (1 : Fin 2) singletonSmall5152) =
      mixedMoment B node3612 node3612Labels := by
    have ha : raw2178 = raw2180 := by apply Matrix.ext; unfold raw2178 raw2180; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5152 = raw2180Labels := by decide +kernel
    rw [ha, hj, canonical2180 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5170 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5170 node5170Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2954 node2954Labels + mixedMoment B node3606 node3606Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2202 singletonSmall5170
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5170) = raw2202Labels := by decide +kernel
  rw [hl, canonical2202 B hB] at h
  have hc0 : mixedMoment B raw2202 (Fin.cases (0 : Fin 2) singletonSmall5170) =
      mixedMoment B node2954 node2954Labels := by
    have ha : raw2202 = raw2203 := by apply Matrix.ext; unfold raw2202 raw2203; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5170 = raw2203Labels := by decide +kernel
    rw [ha, hj, canonical2203 B hB]
  have hc1 : mixedMoment B raw2202 (Fin.cases (1 : Fin 2) singletonSmall5170) =
      mixedMoment B node3606 node3606Labels := by
    have ha : raw2202 = raw2204 := by apply Matrix.ext; unfold raw2202 raw2204; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5170 = raw2204Labels := by decide +kernel
    rw [ha, hj, canonical2204 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton5352 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5352 node5352Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3690 node3690Labels + mixedMoment B node3764 node3764Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2394 singletonSmall5352
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5352) = raw2394Labels := by decide +kernel
  rw [hl, canonical2394 B hB] at h
  have hc0 : mixedMoment B raw2394 (Fin.cases (0 : Fin 2) singletonSmall5352) =
      mixedMoment B node3690 node3690Labels := by
    have ha : raw2394 = raw2395 := by apply Matrix.ext; unfold raw2394 raw2395; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5352 = raw2395Labels := by decide +kernel
    rw [ha, hj, canonical2395 B hB]
  have hc1 : mixedMoment B raw2394 (Fin.cases (1 : Fin 2) singletonSmall5352) =
      mixedMoment B node3764 node3764Labels := by
    have ha : raw2394 = raw2396 := by apply Matrix.ext; unfold raw2394 raw2396; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5352 = raw2396Labels := by decide +kernel
    rw [ha, hj, canonical2396 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5356 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5356 node5356Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3694 node3694Labels + mixedMoment B node3773 node3773Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2403 singletonSmall5356
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5356) = raw2403Labels := by decide +kernel
  rw [hl, canonical2403 B hB] at h
  have hc0 : mixedMoment B raw2403 (Fin.cases (0 : Fin 2) singletonSmall5356) =
      mixedMoment B node3694 node3694Labels := by
    have ha : raw2403 = raw2404 := by apply Matrix.ext; unfold raw2403 raw2404; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5356 = raw2404Labels := by decide +kernel
    rw [ha, hj, canonical2404 B hB]
  have hc1 : mixedMoment B raw2403 (Fin.cases (1 : Fin 2) singletonSmall5356) =
      mixedMoment B node3773 node3773Labels := by
    have ha : raw2403 = raw2405 := by apply Matrix.ext; unfold raw2403 raw2405; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5356 = raw2405Labels := by decide +kernel
    rw [ha, hj, canonical2405 B hB]
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

theorem singleton5473 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5473 node5473Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3958 node3958Labels + mixedMoment B node3961 node3961Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2589 singletonSmall5473
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5473) = raw2589Labels := by decide +kernel
  rw [hl, canonical2589 B hB] at h
  have hc0 : mixedMoment B raw2589 (Fin.cases (0 : Fin 2) singletonSmall5473) =
      mixedMoment B node3958 node3958Labels := by
    have ha : raw2589 = raw2590 := by apply Matrix.ext; unfold raw2589 raw2590; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5473 = raw2590Labels := by decide +kernel
    rw [ha, hj, canonical2590 B hB]
  have hc1 : mixedMoment B raw2589 (Fin.cases (1 : Fin 2) singletonSmall5473) =
      mixedMoment B node3961 node3961Labels := by
    have ha : raw2589 = raw2591 := by apply Matrix.ext; unfold raw2589 raw2591; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5473 = raw2591Labels := by decide +kernel
    rw [ha, hj, canonical2591 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2339 node2339Labels = Sparse.eval nodeValue2339 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2339) = mixedMoment B node2339 node2339Labels := rfl
  simpa [nodeValue2339, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2485 node2485Labels = Sparse.eval nodeValue2485 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2485) = mixedMoment B node2485 node2485Labels := rfl
  simpa [nodeValue2485, Sparse.eval] using hc.symm

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

theorem sound2815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2815 node2815Labels = Sparse.eval nodeValue2815 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2815) = mixedMoment B node2815 node2815Labels := rfl
  simpa [nodeValue2815, Sparse.eval] using hc.symm

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

theorem sound2893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2893 node2893Labels = Sparse.eval nodeValue2893 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2893) = mixedMoment B node2893 node2893Labels := rfl
  simpa [nodeValue2893, Sparse.eval] using hc.symm

theorem sound2924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2924 node2924Labels = Sparse.eval nodeValue2924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2924) = mixedMoment B node2924 node2924Labels := rfl
  simpa [nodeValue2924, Sparse.eval] using hc.symm

theorem sound2931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2931 node2931Labels = Sparse.eval nodeValue2931 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2931) = mixedMoment B node2931 node2931Labels := rfl
  simpa [nodeValue2931, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2954 node2954Labels = Sparse.eval nodeValue2954 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2954) = mixedMoment B node2954 node2954Labels := rfl
  simpa [nodeValue2954, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3420 node3420Labels = Sparse.eval nodeValue3420 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3420) = mixedMoment B node3420 node3420Labels := rfl
  simpa [nodeValue3420, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3481 node3481Labels = Sparse.eval nodeValue3481 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3481) = mixedMoment B node3481 node3481Labels := rfl
  simpa [nodeValue3481, Sparse.eval] using hc.symm

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

theorem sound3588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3588 node3588Labels = Sparse.eval nodeValue3588 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3588) = mixedMoment B node3588 node3588Labels := rfl
  simpa [nodeValue3588, Sparse.eval] using hc.symm

theorem sound3599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3599 node3599Labels = Sparse.eval nodeValue3599 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3599) = mixedMoment B node3599 node3599Labels := rfl
  simpa [nodeValue3599, Sparse.eval] using hc.symm

theorem sound3605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3605 node3605Labels = Sparse.eval nodeValue3605 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3605) = mixedMoment B node3605 node3605Labels := rfl
  simpa [nodeValue3605, Sparse.eval] using hc.symm

theorem sound3606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3606 node3606Labels = Sparse.eval nodeValue3606 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3606) = mixedMoment B node3606 node3606Labels := rfl
  simpa [nodeValue3606, Sparse.eval] using hc.symm

theorem sound3612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3612 node3612Labels = Sparse.eval nodeValue3612 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3612) = mixedMoment B node3612 node3612Labels := rfl
  simpa [nodeValue3612, Sparse.eval] using hc.symm

theorem sound3625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3625 node3625Labels = Sparse.eval nodeValue3625 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3625) = mixedMoment B node3625 node3625Labels := rfl
  simpa [nodeValue3625, Sparse.eval] using hc.symm

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

theorem sound3690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3690 node3690Labels = Sparse.eval nodeValue3690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3690) = mixedMoment B node3690 node3690Labels := rfl
  simpa [nodeValue3690, Sparse.eval] using hc.symm

theorem sound3694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3694 node3694Labels = Sparse.eval nodeValue3694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3694) = mixedMoment B node3694 node3694Labels := rfl
  simpa [nodeValue3694, Sparse.eval] using hc.symm

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

theorem sound3764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3764 node3764Labels = Sparse.eval nodeValue3764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3764) = mixedMoment B node3764 node3764Labels := rfl
  simpa [nodeValue3764, Sparse.eval] using hc.symm

theorem sound3773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3773 node3773Labels = Sparse.eval nodeValue3773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3773) = mixedMoment B node3773 node3773Labels := rfl
  simpa [nodeValue3773, Sparse.eval] using hc.symm

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

theorem sound3958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3958 node3958Labels = Sparse.eval nodeValue3958 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3958) = mixedMoment B node3958 node3958Labels := rfl
  simpa [nodeValue3958, Sparse.eval] using hc.symm

theorem sound3961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3961 node3961Labels = Sparse.eval nodeValue3961 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3961) = mixedMoment B node3961 node3961Labels := rfl
  simpa [nodeValue3961, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4332 node4332Labels = Sparse.eval nodeValue4332 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4332) = mixedMoment B node4332 node4332Labels := rfl
  simpa [nodeValue4332, Sparse.eval] using hc.symm

theorem sound4334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4334 node4334Labels = Sparse.eval nodeValue4334 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4334) = mixedMoment B node4334 node4334Labels := rfl
  simpa [nodeValue4334, Sparse.eval] using hc.symm

theorem sound4335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4335 node4335Labels = Sparse.eval nodeValue4335 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4335) = mixedMoment B node4335 node4335Labels := rfl
  simpa [nodeValue4335, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4357 node4357Labels = Sparse.eval nodeValue4357 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4357) = mixedMoment B node4357 node4357Labels := rfl
  simpa [nodeValue4357, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4444 node4444Labels = Sparse.eval nodeValue4444 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4444) = mixedMoment B node4444 node4444Labels := rfl
  simpa [nodeValue4444, Sparse.eval] using hc.symm

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

theorem sound4930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4930 node4930Labels = Sparse.eval nodeValue4930 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4930) = mixedMoment B node4930 node4930Labels := rfl
  simpa [nodeValue4930, Sparse.eval] using hc.symm

theorem sound4933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4933 node4933Labels = Sparse.eval nodeValue4933 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4933) = mixedMoment B node4933 node4933Labels := rfl
  simpa [nodeValue4933, Sparse.eval] using hc.symm

theorem sound4934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4934 node4934Labels = Sparse.eval nodeValue4934 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4934) = mixedMoment B node4934 node4934Labels := rfl
  simpa [nodeValue4934, Sparse.eval] using hc.symm

theorem sound4935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4935 node4935Labels = Sparse.eval nodeValue4935 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4935) = mixedMoment B node4935 node4935Labels := rfl
  simpa [nodeValue4935, Sparse.eval] using hc.symm

theorem sound4948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4948 node4948Labels = Sparse.eval nodeValue4948 (mixedVector B) := by
  have h := singleton4948 B _hB
  rw [sound2339 B _hB _hF, sound3420 B _hB _hF] at h
  norm_num [nodeValue4948, nodeValue2339, nodeValue3420, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4951 node4951Labels = Sparse.eval nodeValue4951 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4951) = mixedMoment B node4951 node4951Labels := rfl
  simpa [nodeValue4951, Sparse.eval] using hc.symm

theorem sound4954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4954 node4954Labels = Sparse.eval nodeValue4954 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4954) = mixedMoment B node4954 node4954Labels := rfl
  simpa [nodeValue4954, Sparse.eval] using hc.symm

theorem sound4970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4970 node4970Labels = Sparse.eval nodeValue4970 (mixedVector B) := by
  have h := singleton4970 B _hB
  rw [sound2815 B _hB _hF, sound3588 B _hB _hF] at h
  norm_num [nodeValue4970, nodeValue2815, nodeValue3588, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5040 node5040Labels = Sparse.eval nodeValue5040 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5040) = mixedMoment B node5040 node5040Labels := rfl
  simpa [nodeValue5040, Sparse.eval] using hc.symm

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

theorem sound5067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5067 node5067Labels = Sparse.eval nodeValue5067 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5067) = mixedMoment B node5067 node5067Labels := rfl
  simpa [nodeValue5067, Sparse.eval] using hc.symm

theorem sound5078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5078 node5078Labels = Sparse.eval nodeValue5078 (mixedVector B) := by
  have h := singleton5078 B _hB
  rw [sound2485 B _hB _hF, sound3481 B _hB _hF] at h
  norm_num [nodeValue5078, nodeValue2485, nodeValue3481, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5117 node5117Labels = Sparse.eval nodeValue5117 (mixedVector B) := by
  have h := singleton5117 B _hB
  rw [sound2893 B _hB _hF, sound3599 B _hB _hF] at h
  norm_num [nodeValue5117, nodeValue2893, nodeValue3599, Sparse.eval] at h ⊢
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

theorem sound5145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5145 node5145Labels = Sparse.eval nodeValue5145 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5145) = mixedMoment B node5145 node5145Labels := rfl
  simpa [nodeValue5145, Sparse.eval] using hc.symm

theorem sound5147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5147 node5147Labels = Sparse.eval nodeValue5147 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5147) = mixedMoment B node5147 node5147Labels := rfl
  simpa [nodeValue5147, Sparse.eval] using hc.symm

theorem sound5149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5149 node5149Labels = Sparse.eval nodeValue5149 (mixedVector B) := by
  have h := singleton5149 B _hB
  rw [sound2924 B _hB _hF, sound3605 B _hB _hF] at h
  norm_num [nodeValue5149, nodeValue2924, nodeValue3605, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5152 node5152Labels = Sparse.eval nodeValue5152 (mixedVector B) := by
  have h := singleton5152 B _hB
  rw [sound2931 B _hB _hF, sound3612 B _hB _hF] at h
  norm_num [nodeValue5152, nodeValue2931, nodeValue3612, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5164 node5164Labels = Sparse.eval nodeValue5164 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5164) = mixedMoment B node5164 node5164Labels := rfl
  simpa [nodeValue5164, Sparse.eval] using hc.symm

theorem sound5170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5170 node5170Labels = Sparse.eval nodeValue5170 (mixedVector B) := by
  have h := singleton5170 B _hB
  rw [sound2954 B _hB _hF, sound3606 B _hB _hF] at h
  norm_num [nodeValue5170, nodeValue2954, nodeValue3606, Sparse.eval] at h ⊢
  linarith only [h]

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5369 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5369 node5369Labels = 0 := by
  exact mixedMoment_order_one B hB node5369 node5369Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5352 node5352Labels = Sparse.eval nodeValue5352 (mixedVector B) := by
  have h := singleton5352 B _hB
  rw [sound3690 B _hB _hF, sound3764 B _hB _hF] at h
  norm_num [nodeValue5352, nodeValue3690, nodeValue3764, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5356 node5356Labels = Sparse.eval nodeValue5356 (mixedVector B) := by
  have h := singleton5356 B _hB
  rw [sound3694 B _hB _hF, sound3773 B _hB _hF] at h
  norm_num [nodeValue5356, nodeValue3694, nodeValue3773, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5369 node5369Labels = Sparse.eval nodeValue5369 (mixedVector B) := by
  simpa only [nodeValue5369, Sparse.eval_nil] using zero5369 B _hB _hF

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

theorem zero5410 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5410 node5410Labels = 0 := by
  exact mixedMoment_order_one B hB node5410 node5410Labels 1
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

theorem sound5410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5410 node5410Labels = Sparse.eval nodeValue5410 (mixedVector B) := by
  simpa only [nodeValue5410, Sparse.eval_nil] using zero5410 B _hB _hF

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

theorem sound5473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5473 node5473Labels = Sparse.eval nodeValue5473 (mixedVector B) := by
  have h := singleton5473 B _hB
  rw [sound3958 B _hB _hF, sound3961 B _hB _hF] at h
  norm_num [nodeValue5473, nodeValue3958, nodeValue3961, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources67
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2152 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2152 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2152 + difference 0 1) (sourceB2152 + difference 1 0) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2152 + difference 0 1) (sourceB2152 + difference 1 0) sourceC2152) = raw17724 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw17724; decide +kernel
    rw [ha]
    exact (canonical17724 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2152 + difference 0 2) (sourceB2152 + difference 2 0) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2152 + difference 0 2) (sourceB2152 + difference 2 0) sourceC2152) = raw17725 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw17725; decide +kernel
    rw [ha]
    exact (canonical17725 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2152 + difference 0 3) (sourceB2152 + difference 3 0) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5369) := by
    have ha : (tripleCharges (sourceA2152 + difference 0 3) (sourceB2152 + difference 3 0) sourceC2152) = raw17726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw17726; decide +kernel
    rw [ha]
    exact (canonical17726 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2152 + difference 0 4) (sourceB2152 + difference 4 0) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA2152 + difference 0 4) (sourceB2152 + difference 4 0) sourceC2152) = raw29735 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29735; decide +kernel
    rw [ha]
    exact (canonical29735 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2152 + difference 0 5) (sourceB2152 + difference 5 0) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA2152 + difference 0 5) (sourceB2152 + difference 5 0) sourceC2152) = raw17727 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw17727; decide +kernel
    rw [ha]
    exact (canonical17727 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2152 + difference 1 0) (sourceB2152 + difference 0 1) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4444) := by
    have ha : (tripleCharges (sourceA2152 + difference 1 0) (sourceB2152 + difference 0 1) sourceC2152) = raw29736 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29736; decide +kernel
    rw [ha]
    exact (canonical29736 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2152 + difference 1 2) (sourceB2152 + difference 2 1) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5067) := by
    have ha : (tripleCharges (sourceA2152 + difference 1 2) (sourceB2152 + difference 2 1) sourceC2152) = raw29737 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29737; decide +kernel
    rw [ha]
    exact (canonical29737 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2152 + difference 1 3) (sourceB2152 + difference 3 1) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2152 + difference 1 3) (sourceB2152 + difference 3 1) sourceC2152) = raw29738 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29738; decide +kernel
    rw [ha]
    exact (canonical29738 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2152 + difference 1 4) (sourceB2152 + difference 4 1) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA2152 + difference 1 4) (sourceB2152 + difference 4 1) sourceC2152) = raw17708 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw17708; decide +kernel
    rw [ha]
    exact (canonical17708 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2152 + difference 1 5) (sourceB2152 + difference 5 1) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA2152 + difference 1 5) (sourceB2152 + difference 5 1) sourceC2152) = raw29739 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29739; decide +kernel
    rw [ha]
    exact (canonical29739 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2152 + difference 2 0) (sourceB2152 + difference 0 2) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4332) := by
    have ha : (tripleCharges (sourceA2152 + difference 2 0) (sourceB2152 + difference 0 2) sourceC2152) = raw29740 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29740; decide +kernel
    rw [ha]
    exact (canonical29740 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2152 + difference 2 1) (sourceB2152 + difference 1 2) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4933) := by
    have ha : (tripleCharges (sourceA2152 + difference 2 1) (sourceB2152 + difference 1 2) sourceC2152) = raw29741 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29741; decide +kernel
    rw [ha]
    exact (canonical29741 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2152 + difference 2 3) (sourceB2152 + difference 3 2) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5117) := by
    have ha : (tripleCharges (sourceA2152 + difference 2 3) (sourceB2152 + difference 3 2) sourceC2152) = raw29742 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29742; decide +kernel
    rw [ha]
    exact (canonical29742 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2152 + difference 2 4) (sourceB2152 + difference 4 2) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA2152 + difference 2 4) (sourceB2152 + difference 4 2) sourceC2152) = raw17713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw17713; decide +kernel
    rw [ha]
    exact (canonical17713 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2152 + difference 2 5) (sourceB2152 + difference 5 2) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2152 + difference 2 5) (sourceB2152 + difference 5 2) sourceC2152) = raw29743 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29743; decide +kernel
    rw [ha]
    exact (canonical29743 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2152 + difference 3 0) (sourceB2152 + difference 0 3) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4357) := by
    have ha : (tripleCharges (sourceA2152 + difference 3 0) (sourceB2152 + difference 0 3) sourceC2152) = raw29744 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29744; decide +kernel
    rw [ha]
    exact (canonical29744 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2152 + difference 3 1) (sourceB2152 + difference 1 3) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4951) := by
    have ha : (tripleCharges (sourceA2152 + difference 3 1) (sourceB2152 + difference 1 3) sourceC2152) = raw29745 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29745; decide +kernel
    rw [ha]
    exact (canonical29745 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2152 + difference 3 2) (sourceB2152 + difference 2 3) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5040) := by
    have ha : (tripleCharges (sourceA2152 + difference 3 2) (sourceB2152 + difference 2 3) sourceC2152) = raw29746 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29746; decide +kernel
    rw [ha]
    exact (canonical29746 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2152 + difference 3 4) (sourceB2152 + difference 4 3) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA2152 + difference 3 4) (sourceB2152 + difference 4 3) sourceC2152) = raw17718 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw17718; decide +kernel
    rw [ha]
    exact (canonical17718 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2152 + difference 3 5) (sourceB2152 + difference 5 3) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA2152 + difference 3 5) (sourceB2152 + difference 5 3) sourceC2152) = raw29747 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29747; decide +kernel
    rw [ha]
    exact (canonical29747 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2152 + difference 4 0) (sourceB2152 + difference 0 4) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4335) := by
    have ha : (tripleCharges (sourceA2152 + difference 4 0) (sourceB2152 + difference 0 4) sourceC2152) = raw29748 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29748; decide +kernel
    rw [ha]
    exact (canonical29748 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2152 + difference 4 1) (sourceB2152 + difference 1 4) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4935) := by
    have ha : (tripleCharges (sourceA2152 + difference 4 1) (sourceB2152 + difference 1 4) sourceC2152) = raw29749 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29749; decide +kernel
    rw [ha]
    exact (canonical29749 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2152 + difference 4 2) (sourceB2152 + difference 2 4) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4930) := by
    have ha : (tripleCharges (sourceA2152 + difference 4 2) (sourceB2152 + difference 2 4) sourceC2152) = raw29750 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29750; decide +kernel
    rw [ha]
    exact (canonical29750 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2152 + difference 4 3) (sourceB2152 + difference 3 4) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4948) := by
    have ha : (tripleCharges (sourceA2152 + difference 4 3) (sourceB2152 + difference 3 4) sourceC2152) = raw29751 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29751; decide +kernel
    rw [ha]
    exact (canonical29751 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2152 + difference 4 5) (sourceB2152 + difference 5 4) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA2152 + difference 4 5) (sourceB2152 + difference 5 4) sourceC2152) = raw29752 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29752; decide +kernel
    rw [ha]
    exact (canonical29752 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2152 + difference 5 0) (sourceB2152 + difference 0 5) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4334) := by
    have ha : (tripleCharges (sourceA2152 + difference 5 0) (sourceB2152 + difference 0 5) sourceC2152) = raw29753 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29753; decide +kernel
    rw [ha]
    exact (canonical29753 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2152 + difference 5 1) (sourceB2152 + difference 1 5) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4934) := by
    have ha : (tripleCharges (sourceA2152 + difference 5 1) (sourceB2152 + difference 1 5) sourceC2152) = raw29754 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29754; decide +kernel
    rw [ha]
    exact (canonical29754 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2152 + difference 5 2) (sourceB2152 + difference 2 5) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4954) := by
    have ha : (tripleCharges (sourceA2152 + difference 5 2) (sourceB2152 + difference 2 5) sourceC2152) = raw29755 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29755; decide +kernel
    rw [ha]
    exact (canonical29755 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2152 + difference 5 3) (sourceB2152 + difference 3 5) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4970) := by
    have ha : (tripleCharges (sourceA2152 + difference 5 3) (sourceB2152 + difference 3 5) sourceC2152) = raw29756 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29756; decide +kernel
    rw [ha]
    exact (canonical29756 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2152 + difference 5 4) (sourceB2152 + difference 4 5) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA2152 + difference 5 4) (sourceB2152 + difference 4 5) sourceC2152) = raw17728 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw17728; decide +kernel
    rw [ha]
    exact (canonical17728 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2152 sourceB2152 sourceC2152
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2152, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1795 : Integer.Sparse.reindex keyMap MixedData.row1795 = numericRow1795 := by decide +kernel

theorem numericCheck1795 (x : Master → ℝ) : Integer.Sparse.eval numericRow1795 x =
    (4 : ℝ) * reducedSource1795 x := by
  norm_num [numericRow1795, reducedSource1795, Integer.Sparse.eval, Sparse.eval, nodeValue4332, nodeValue4334, nodeValue4335, nodeValue4357, nodeValue4444, nodeValue4930, nodeValue4933, nodeValue4934, nodeValue4935, nodeValue4948, nodeValue4951, nodeValue4954, nodeValue4970, nodeValue5040, nodeValue5067, nodeValue5078, nodeValue5117, nodeValue5145, nodeValue5147, nodeValue5149, nodeValue5152, nodeValue5164, nodeValue5170, nodeValue5282, nodeValue5284, nodeValue5352, nodeValue5356, nodeValue5369, nodeValue5410, nodeValue5473]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1795 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1795 (mixedVector B) = 0 := by
  have h4332 : mixedVector B (Sum.inr 4332) = Sparse.eval nodeValue4332 (mixedVector B) := by
    change mixedMoment B node4332 node4332Labels = _
    exact sound4332 B hB hF
  have h4334 : mixedVector B (Sum.inr 4334) = Sparse.eval nodeValue4334 (mixedVector B) := by
    change mixedMoment B node4334 node4334Labels = _
    exact sound4334 B hB hF
  have h4335 : mixedVector B (Sum.inr 4335) = Sparse.eval nodeValue4335 (mixedVector B) := by
    change mixedMoment B node4335 node4335Labels = _
    exact sound4335 B hB hF
  have h4357 : mixedVector B (Sum.inr 4357) = Sparse.eval nodeValue4357 (mixedVector B) := by
    change mixedMoment B node4357 node4357Labels = _
    exact sound4357 B hB hF
  have h4444 : mixedVector B (Sum.inr 4444) = Sparse.eval nodeValue4444 (mixedVector B) := by
    change mixedMoment B node4444 node4444Labels = _
    exact sound4444 B hB hF
  have h4930 : mixedVector B (Sum.inr 4930) = Sparse.eval nodeValue4930 (mixedVector B) := by
    change mixedMoment B node4930 node4930Labels = _
    exact sound4930 B hB hF
  have h4933 : mixedVector B (Sum.inr 4933) = Sparse.eval nodeValue4933 (mixedVector B) := by
    change mixedMoment B node4933 node4933Labels = _
    exact sound4933 B hB hF
  have h4934 : mixedVector B (Sum.inr 4934) = Sparse.eval nodeValue4934 (mixedVector B) := by
    change mixedMoment B node4934 node4934Labels = _
    exact sound4934 B hB hF
  have h4935 : mixedVector B (Sum.inr 4935) = Sparse.eval nodeValue4935 (mixedVector B) := by
    change mixedMoment B node4935 node4935Labels = _
    exact sound4935 B hB hF
  have h4948 : mixedVector B (Sum.inr 4948) = Sparse.eval nodeValue4948 (mixedVector B) := by
    change mixedMoment B node4948 node4948Labels = _
    exact sound4948 B hB hF
  have h4951 : mixedVector B (Sum.inr 4951) = Sparse.eval nodeValue4951 (mixedVector B) := by
    change mixedMoment B node4951 node4951Labels = _
    exact sound4951 B hB hF
  have h4954 : mixedVector B (Sum.inr 4954) = Sparse.eval nodeValue4954 (mixedVector B) := by
    change mixedMoment B node4954 node4954Labels = _
    exact sound4954 B hB hF
  have h4970 : mixedVector B (Sum.inr 4970) = Sparse.eval nodeValue4970 (mixedVector B) := by
    change mixedMoment B node4970 node4970Labels = _
    exact sound4970 B hB hF
  have h5040 : mixedVector B (Sum.inr 5040) = Sparse.eval nodeValue5040 (mixedVector B) := by
    change mixedMoment B node5040 node5040Labels = _
    exact sound5040 B hB hF
  have h5067 : mixedVector B (Sum.inr 5067) = Sparse.eval nodeValue5067 (mixedVector B) := by
    change mixedMoment B node5067 node5067Labels = _
    exact sound5067 B hB hF
  have h5078 : mixedVector B (Sum.inr 5078) = Sparse.eval nodeValue5078 (mixedVector B) := by
    change mixedMoment B node5078 node5078Labels = _
    exact sound5078 B hB hF
  have h5117 : mixedVector B (Sum.inr 5117) = Sparse.eval nodeValue5117 (mixedVector B) := by
    change mixedMoment B node5117 node5117Labels = _
    exact sound5117 B hB hF
  have h5145 : mixedVector B (Sum.inr 5145) = Sparse.eval nodeValue5145 (mixedVector B) := by
    change mixedMoment B node5145 node5145Labels = _
    exact sound5145 B hB hF
  have h5147 : mixedVector B (Sum.inr 5147) = Sparse.eval nodeValue5147 (mixedVector B) := by
    change mixedMoment B node5147 node5147Labels = _
    exact sound5147 B hB hF
  have h5149 : mixedVector B (Sum.inr 5149) = Sparse.eval nodeValue5149 (mixedVector B) := by
    change mixedMoment B node5149 node5149Labels = _
    exact sound5149 B hB hF
  have h5152 : mixedVector B (Sum.inr 5152) = Sparse.eval nodeValue5152 (mixedVector B) := by
    change mixedMoment B node5152 node5152Labels = _
    exact sound5152 B hB hF
  have h5164 : mixedVector B (Sum.inr 5164) = Sparse.eval nodeValue5164 (mixedVector B) := by
    change mixedMoment B node5164 node5164Labels = _
    exact sound5164 B hB hF
  have h5170 : mixedVector B (Sum.inr 5170) = Sparse.eval nodeValue5170 (mixedVector B) := by
    change mixedMoment B node5170 node5170Labels = _
    exact sound5170 B hB hF
  have h5282 : mixedVector B (Sum.inr 5282) = Sparse.eval nodeValue5282 (mixedVector B) := by
    change mixedMoment B node5282 node5282Labels = _
    exact sound5282 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5352 : mixedVector B (Sum.inr 5352) = Sparse.eval nodeValue5352 (mixedVector B) := by
    change mixedMoment B node5352 node5352Labels = _
    exact sound5352 B hB hF
  have h5356 : mixedVector B (Sum.inr 5356) = Sparse.eval nodeValue5356 (mixedVector B) := by
    change mixedMoment B node5356 node5356Labels = _
    exact sound5356 B hB hF
  have h5369 : mixedVector B (Sum.inr 5369) = Sparse.eval nodeValue5369 (mixedVector B) := by
    change mixedMoment B node5369 node5369Labels = _
    exact sound5369 B hB hF
  have h5410 : mixedVector B (Sum.inr 5410) = Sparse.eval nodeValue5410 (mixedVector B) := by
    change mixedMoment B node5410 node5410Labels = _
    exact sound5410 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  simpa only [sourceForm2152, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4332, h4334, h4335, h4357, h4444, h4930, h4933, h4934, h4935, h4948, h4951, h4954, h4970, h5040, h5067, h5078, h5117, h5145, h5147, h5149, h5152, h5164, h5170, h5282, h5284, h5352, h5356, h5369, h5410, h5473, reducedSource1795] using sourceEq2152 B hB

theorem rowSound1795_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1795 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1795, numericCheck1795, reducedZero1795 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795_e_oai
