-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2097_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T23:27:35.56242+00:00
-- url     : https://prove2.me/submissions/a0b8032d-dceb-4a6d-9c79-4939dda2808e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E100
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

theorem mixedMoment_zero_first_factor {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin (n + 1)) ℤ) (label : Fin (n + 1) → Fin l)
    (hA : ∀ i, A i 0 = 0) :
    mixedMoment B A label = mixedMoment B (fun i j => A i j.succ) (fun j => label j.succ) := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  unfold mixedIntegrand
  rw [Fin.prod_univ_succ]
  have hz : (fun i => A i 0) = 0 := funext hA
  rw [hz, rowFourier_zero, one_mul]

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

theorem delete_zero_factor {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin (n + 1)) ℤ) (label : Fin (n + 1) → Fin l)
    (σ : Equiv.Perm (Fin (n + 1))) (hz : ∀ i, A i (σ 0) = 0) :
    mixedMoment B A label =
      mixedMoment B (fun i j => A i (σ j.succ)) (fun j => label (σ j.succ)) := by
  rw [← mixedMoment_factor_permutation B A label σ]
  exact mixedMoment_zero_first_factor B _ _ hz

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1992 raw1992Labels = mixedMoment B node4986 node4986Labels := by
  calc
    mixedMoment B raw1992 raw1992Labels = mixedMoment B raw1992step0 raw1992step0Labels := by
      have ha : raw1992step0 = (fun i j => raw1992 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1992step0 raw1992; decide +kernel
      have hl : raw1992step0Labels = raw1992Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1992 raw1992Labels permutation152 permutation4
    mixedMoment B raw1992step0 raw1992step0Labels = mixedMoment B raw1992step1 raw1992step1Labels := by
      have ha : raw1992step1 = raw1992step0 := by apply Matrix.ext; unfold raw1992step1 raw1992step0; decide +kernel
      have hl : raw1992step0Labels = labelEmbedding7 ∘ raw1992step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1992step0 raw1992step0Labels raw1992step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4986 node4986Labels := by rfl

theorem canonical1993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1993 raw1993Labels = mixedMoment B node2371 node2371Labels := by
  calc
    mixedMoment B raw1993 raw1993Labels = mixedMoment B raw1993step0 raw1993step0Labels := by
      have ha : raw1993step0 = (fun i j => raw1993 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1993step0 raw1993; decide +kernel
      have hl : raw1993step0Labels = raw1993Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1993 raw1993Labels permutation152 permutation4
    _ = mixedMoment B node2371 node2371Labels := by rfl

theorem canonical1994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1994 raw1994Labels = mixedMoment B node3335 node3335Labels := by
  calc
    mixedMoment B raw1994 raw1994Labels = mixedMoment B raw1994step0 raw1994step0Labels := by
      have ha : raw1994step0 = (fun i j => raw1994 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1994step0 raw1994; decide +kernel
      have hl : raw1994step0Labels = raw1994Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1994 raw1994Labels permutation152 permutation6
    mixedMoment B raw1994step0 raw1994step0Labels = mixedMoment B raw1994step1 raw1994step1Labels := by
      have ha : raw1994step1 = -raw1994step0 := by apply Matrix.ext; change ∀ i j, raw1994step1 i j = -(raw1994step0 i j); unfold raw1994step1 raw1994step0; decide +kernel
      have hl : raw1994step1Labels = raw1994step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1994step1 raw1994step1Labels = mixedMoment B raw1994step2 raw1994step2Labels := by
      have ha : raw1994step2 = raw1994step1 := by apply Matrix.ext; unfold raw1994step2 raw1994step1; decide +kernel
      have hl : raw1994step1Labels = labelEmbedding1 ∘ raw1994step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1994step1 raw1994step1Labels raw1994step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3335 node3335Labels := by rfl

theorem canonical1995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1995 raw1995Labels = mixedMoment B node4987 node4987Labels := by
  calc
    mixedMoment B raw1995 raw1995Labels = mixedMoment B raw1995step0 raw1995step0Labels := by
      have ha : raw1995step0 = (fun i j => raw1995 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1995step0 raw1995; decide +kernel
      have hl : raw1995step0Labels = raw1995Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1995 raw1995Labels permutation152 permutation4
    mixedMoment B raw1995step0 raw1995step0Labels = mixedMoment B raw1995step1 raw1995step1Labels := by
      have ha : raw1995step1 = raw1995step0 := by apply Matrix.ext; unfold raw1995step1 raw1995step0; decide +kernel
      have hl : raw1995step0Labels = labelEmbedding7 ∘ raw1995step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1995step0 raw1995step0Labels raw1995step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4987 node4987Labels := by rfl

theorem canonical1996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1996 raw1996Labels = mixedMoment B node2372 node2372Labels := by
  calc
    mixedMoment B raw1996 raw1996Labels = mixedMoment B raw1996step0 raw1996step0Labels := by
      have ha : raw1996step0 = (fun i j => raw1996 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1996step0 raw1996; decide +kernel
      have hl : raw1996step0Labels = raw1996Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1996 raw1996Labels permutation152 permutation4
    _ = mixedMoment B node2372 node2372Labels := by rfl

theorem canonical1997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1997 raw1997Labels = mixedMoment B node3336 node3336Labels := by
  calc
    mixedMoment B raw1997 raw1997Labels = mixedMoment B raw1997step0 raw1997step0Labels := by
      have ha : raw1997step0 = (fun i j => raw1997 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1997step0 raw1997; decide +kernel
      have hl : raw1997step0Labels = raw1997Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1997 raw1997Labels permutation152 permutation6
    mixedMoment B raw1997step0 raw1997step0Labels = mixedMoment B raw1997step1 raw1997step1Labels := by
      have ha : raw1997step1 = -raw1997step0 := by apply Matrix.ext; change ∀ i j, raw1997step1 i j = -(raw1997step0 i j); unfold raw1997step1 raw1997step0; decide +kernel
      have hl : raw1997step1Labels = raw1997step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1997step1 raw1997step1Labels = mixedMoment B raw1997step2 raw1997step2Labels := by
      have ha : raw1997step2 = raw1997step1 := by apply Matrix.ext; unfold raw1997step2 raw1997step1; decide +kernel
      have hl : raw1997step1Labels = labelEmbedding1 ∘ raw1997step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1997step1 raw1997step1Labels raw1997step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3336 node3336Labels := by rfl

theorem canonical2043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2043 raw2043Labels = mixedMoment B node5030 node5030Labels := by
  calc
    mixedMoment B raw2043 raw2043Labels = mixedMoment B raw2043step0 raw2043step0Labels := by
      have ha : raw2043step0 = (fun i j => raw2043 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2043step0 raw2043; decide +kernel
      have hl : raw2043step0Labels = raw2043Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2043 raw2043Labels permutation152 permutation4
    mixedMoment B raw2043step0 raw2043step0Labels = mixedMoment B raw2043step1 raw2043step1Labels := by
      have ha : raw2043step1 = raw2043step0 := by apply Matrix.ext; unfold raw2043step1 raw2043step0; decide +kernel
      have hl : raw2043step0Labels = labelEmbedding7 ∘ raw2043step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2043step0 raw2043step0Labels raw2043step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5030 node5030Labels := by rfl

theorem canonical2044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2044 raw2044Labels = mixedMoment B node2419 node2419Labels := by
  calc
    mixedMoment B raw2044 raw2044Labels = mixedMoment B raw2044step0 raw2044step0Labels := by
      have ha : raw2044step0 = (fun i j => raw2044 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2044step0 raw2044; decide +kernel
      have hl : raw2044step0Labels = raw2044Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2044 raw2044Labels permutation152 permutation4
    _ = mixedMoment B node2419 node2419Labels := by rfl

theorem canonical2045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2045 raw2045Labels = mixedMoment B node3425 node3425Labels := by
  calc
    mixedMoment B raw2045 raw2045Labels = mixedMoment B raw2045step0 raw2045step0Labels := by
      have ha : raw2045step0 = (fun i j => raw2045 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2045step0 raw2045; decide +kernel
      have hl : raw2045step0Labels = raw2045Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2045 raw2045Labels permutation154 permutation6
    mixedMoment B raw2045step0 raw2045step0Labels = mixedMoment B raw2045step1 raw2045step1Labels := by
      have ha : raw2045step1 = -raw2045step0 := by apply Matrix.ext; change ∀ i j, raw2045step1 i j = -(raw2045step0 i j); unfold raw2045step1 raw2045step0; decide +kernel
      have hl : raw2045step1Labels = raw2045step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2045step1 raw2045step1Labels = mixedMoment B raw2045step2 raw2045step2Labels := by
      have ha : raw2045step2 = raw2045step1 := by apply Matrix.ext; unfold raw2045step2 raw2045step1; decide +kernel
      have hl : raw2045step1Labels = labelEmbedding1 ∘ raw2045step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2045step1 raw2045step1Labels raw2045step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3425 node3425Labels := by rfl

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

theorem canonical2082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2082 raw2082Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw2082 raw2082Labels = mixedMoment B raw2082step0 raw2082step0Labels := by
      have ha : raw2082step0 = (fun i j => raw2082 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2082step0 raw2082; decide +kernel
      have hl : raw2082step0Labels = raw2082Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2082 raw2082Labels permutation152 permutation4
    mixedMoment B raw2082step0 raw2082step0Labels = mixedMoment B raw2082step1 raw2082step1Labels := by
      have ha : raw2082step1 = raw2082step0 := by apply Matrix.ext; unfold raw2082step1 raw2082step0; decide +kernel
      have hl : raw2082step0Labels = labelEmbedding7 ∘ raw2082step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2082step0 raw2082step0Labels raw2082step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

theorem canonical2083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2083 raw2083Labels = mixedMoment B node2459 node2459Labels := by
  calc
    mixedMoment B raw2083 raw2083Labels = mixedMoment B raw2083step0 raw2083step0Labels := by
      have ha : raw2083step0 = (fun i j => raw2083 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2083step0 raw2083; decide +kernel
      have hl : raw2083step0Labels = raw2083Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2083 raw2083Labels permutation152 permutation4
    _ = mixedMoment B node2459 node2459Labels := by rfl

theorem canonical2084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2084 raw2084Labels = mixedMoment B node3429 node3429Labels := by
  calc
    mixedMoment B raw2084 raw2084Labels = mixedMoment B raw2084step0 raw2084step0Labels := by
      have ha : raw2084step0 = (fun i j => raw2084 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2084step0 raw2084; decide +kernel
      have hl : raw2084step0Labels = raw2084Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2084 raw2084Labels permutation152 permutation6
    mixedMoment B raw2084step0 raw2084step0Labels = mixedMoment B raw2084step1 raw2084step1Labels := by
      have ha : raw2084step1 = -raw2084step0 := by apply Matrix.ext; change ∀ i j, raw2084step1 i j = -(raw2084step0 i j); unfold raw2084step1 raw2084step0; decide +kernel
      have hl : raw2084step1Labels = raw2084step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2084step1 raw2084step1Labels = mixedMoment B raw2084step2 raw2084step2Labels := by
      have ha : raw2084step2 = raw2084step1 := by apply Matrix.ext; unfold raw2084step2 raw2084step1; decide +kernel
      have hl : raw2084step1Labels = labelEmbedding1 ∘ raw2084step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2084step1 raw2084step1Labels raw2084step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3429 node3429Labels := by rfl

theorem canonical2154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2154 raw2154Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw2154 raw2154Labels = mixedMoment B raw2154step0 raw2154step0Labels := by
      have ha : raw2154step0 = (fun i j => raw2154 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2154step0 raw2154; decide +kernel
      have hl : raw2154step0Labels = raw2154Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2154 raw2154Labels permutation152 permutation4
    mixedMoment B raw2154step0 raw2154step0Labels = mixedMoment B raw2154step1 raw2154step1Labels := by
      have ha : raw2154step1 = raw2154step0 := by apply Matrix.ext; unfold raw2154step1 raw2154step0; decide +kernel
      have hl : raw2154step0Labels = labelEmbedding7 ∘ raw2154step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2154step0 raw2154step0Labels raw2154step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

theorem canonical2155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2155 raw2155Labels = mixedMoment B node2536 node2536Labels := by
  calc
    mixedMoment B raw2155 raw2155Labels = mixedMoment B raw2155step0 raw2155step0Labels := by
      have ha : raw2155step0 = (fun i j => raw2155 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2155step0 raw2155; decide +kernel
      have hl : raw2155step0Labels = raw2155Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2155 raw2155Labels permutation152 permutation4
    _ = mixedMoment B node2536 node2536Labels := by rfl

theorem canonical2156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2156 raw2156Labels = mixedMoment B node3370 node3370Labels := by
  calc
    mixedMoment B raw2156 raw2156Labels = mixedMoment B raw2156step0 raw2156step0Labels := by
      have ha : raw2156step0 = (fun i j => raw2156 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2156step0 raw2156; decide +kernel
      have hl : raw2156step0Labels = raw2156Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2156 raw2156Labels permutation176 permutation6
    mixedMoment B raw2156step0 raw2156step0Labels = mixedMoment B raw2156step1 raw2156step1Labels := by
      have ha : raw2156step1 = -raw2156step0 := by apply Matrix.ext; change ∀ i j, raw2156step1 i j = -(raw2156step0 i j); unfold raw2156step1 raw2156step0; decide +kernel
      have hl : raw2156step1Labels = raw2156step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2156step1 raw2156step1Labels = mixedMoment B raw2156step2 raw2156step2Labels := by
      have ha : raw2156step2 = raw2156step1 := by apply Matrix.ext; unfold raw2156step2 raw2156step1; decide +kernel
      have hl : raw2156step1Labels = labelEmbedding1 ∘ raw2156step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2156step1 raw2156step1Labels raw2156step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3370 node3370Labels := by rfl

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

theorem canonical2364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2364 raw2364Labels = mixedMoment B node5333 node5333Labels := by
  calc
    mixedMoment B raw2364 raw2364Labels = mixedMoment B raw2364step0 raw2364step0Labels := by
      have ha : raw2364step0 = (fun i j => raw2364 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2364step0 raw2364; decide +kernel
      have hl : raw2364step0Labels = raw2364Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2364 raw2364Labels permutation152 permutation4
    mixedMoment B raw2364step0 raw2364step0Labels = mixedMoment B raw2364step1 raw2364step1Labels := by
      have ha : raw2364step1 = raw2364step0 := by apply Matrix.ext; unfold raw2364step1 raw2364step0; decide +kernel
      have hl : raw2364step0Labels = labelEmbedding7 ∘ raw2364step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2364step0 raw2364step0Labels raw2364step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5333 node5333Labels := by rfl

theorem canonical2365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2365 raw2365Labels = mixedMoment B node3668 node3668Labels := by
  calc
    mixedMoment B raw2365 raw2365Labels = mixedMoment B raw2365step0 raw2365step0Labels := by
      have ha : raw2365step0 = (fun i j => raw2365 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2365step0 raw2365; decide +kernel
      have hl : raw2365step0Labels = raw2365Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2365 raw2365Labels permutation152 permutation4
    _ = mixedMoment B node3668 node3668Labels := by rfl

theorem canonical2366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2366 raw2366Labels = mixedMoment B node3677 node3677Labels := by
  calc
    mixedMoment B raw2366 raw2366Labels = mixedMoment B raw2366step0 raw2366step0Labels := by
      have ha : raw2366step0 = (fun i j => raw2366 (permutation664 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2366step0 raw2366; decide +kernel
      have hl : raw2366step0Labels = raw2366Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2366 raw2366Labels permutation664 permutation6
    mixedMoment B raw2366step0 raw2366step0Labels = mixedMoment B raw2366step1 raw2366step1Labels := by
      have ha : raw2366step1 = raw2366step0 := by apply Matrix.ext; unfold raw2366step1 raw2366step0; decide +kernel
      have hl : raw2366step0Labels = labelEmbedding1 ∘ raw2366step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2366step0 raw2366step0Labels raw2366step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3677 node3677Labels := by rfl

theorem canonical2382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2382 raw2382Labels = mixedMoment B node5344 node5344Labels := by
  calc
    mixedMoment B raw2382 raw2382Labels = mixedMoment B raw2382step0 raw2382step0Labels := by
      have ha : raw2382step0 = (fun i j => raw2382 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2382step0 raw2382; decide +kernel
      have hl : raw2382step0Labels = raw2382Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2382 raw2382Labels permutation152 permutation4
    mixedMoment B raw2382step0 raw2382step0Labels = mixedMoment B raw2382step1 raw2382step1Labels := by
      have ha : raw2382step1 = raw2382step0 := by apply Matrix.ext; unfold raw2382step1 raw2382step0; decide +kernel
      have hl : raw2382step0Labels = labelEmbedding7 ∘ raw2382step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2382step0 raw2382step0Labels raw2382step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5344 node5344Labels := by rfl

theorem canonical2383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2383 raw2383Labels = mixedMoment B node3681 node3681Labels := by
  calc
    mixedMoment B raw2383 raw2383Labels = mixedMoment B raw2383step0 raw2383step0Labels := by
      have ha : raw2383step0 = (fun i j => raw2383 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2383step0 raw2383; decide +kernel
      have hl : raw2383step0Labels = raw2383Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2383 raw2383Labels permutation152 permutation4
    _ = mixedMoment B node3681 node3681Labels := by rfl

theorem canonical2384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2384 raw2384Labels = mixedMoment B node3681 node3681Labels := by
  calc
    mixedMoment B raw2384 raw2384Labels = mixedMoment B raw2384step0 raw2384step0Labels := by
      have ha : raw2384step0 = (fun i j => raw2384 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2384step0 raw2384; decide +kernel
      have hl : raw2384step0Labels = raw2384Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2384 raw2384Labels permutation688 permutation6
    mixedMoment B raw2384step0 raw2384step0Labels = mixedMoment B raw2384step1 raw2384step1Labels := by
      have ha : raw2384step1 = raw2384step0 := by apply Matrix.ext; unfold raw2384step1 raw2384step0; decide +kernel
      have hl : raw2384step0Labels = labelEmbedding1 ∘ raw2384step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2384step0 raw2384step0Labels raw2384step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3681 node3681Labels := by rfl

theorem canonical2385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2385 raw2385Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw2385 raw2385Labels = mixedMoment B raw2385step0 raw2385step0Labels := by
      have ha : raw2385step0 = (fun i j => raw2385 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2385step0 raw2385; decide +kernel
      have hl : raw2385step0Labels = raw2385Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2385 raw2385Labels permutation152 permutation4
    mixedMoment B raw2385step0 raw2385step0Labels = mixedMoment B raw2385step1 raw2385step1Labels := by
      have ha : raw2385step1 = raw2385step0 := by apply Matrix.ext; unfold raw2385step1 raw2385step0; decide +kernel
      have hl : raw2385step0Labels = labelEmbedding7 ∘ raw2385step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2385step0 raw2385step0Labels raw2385step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

theorem canonical2386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2386 raw2386Labels = mixedMoment B node3683 node3683Labels := by
  calc
    mixedMoment B raw2386 raw2386Labels = mixedMoment B raw2386step0 raw2386step0Labels := by
      have ha : raw2386step0 = (fun i j => raw2386 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2386step0 raw2386; decide +kernel
      have hl : raw2386step0Labels = raw2386Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2386 raw2386Labels permutation152 permutation4
    _ = mixedMoment B node3683 node3683Labels := by rfl

theorem canonical2387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2387 raw2387Labels = mixedMoment B node3746 node3746Labels := by
  calc
    mixedMoment B raw2387 raw2387Labels = mixedMoment B raw2387step0 raw2387step0Labels := by
      have ha : raw2387step0 = (fun i j => raw2387 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2387step0 raw2387; decide +kernel
      have hl : raw2387step0Labels = raw2387Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2387 raw2387Labels permutation153 permutation6
    mixedMoment B raw2387step0 raw2387step0Labels = mixedMoment B raw2387step1 raw2387step1Labels := by
      have ha : raw2387step1 = -raw2387step0 := by apply Matrix.ext; change ∀ i j, raw2387step1 i j = -(raw2387step0 i j); unfold raw2387step1 raw2387step0; decide +kernel
      have hl : raw2387step1Labels = raw2387step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2387step1 raw2387step1Labels = mixedMoment B raw2387step2 raw2387step2Labels := by
      have ha : raw2387step2 = raw2387step1 := by apply Matrix.ext; unfold raw2387step2 raw2387step1; decide +kernel
      have hl : raw2387step1Labels = labelEmbedding1 ∘ raw2387step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2387step1 raw2387step1Labels raw2387step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3746 node3746Labels := by rfl

theorem canonical2427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2427 raw2427Labels = mixedMoment B node5374 node5374Labels := by
  calc
    mixedMoment B raw2427 raw2427Labels = mixedMoment B raw2427step0 raw2427step0Labels := by
      have ha : raw2427step0 = (fun i j => raw2427 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2427step0 raw2427; decide +kernel
      have hl : raw2427step0Labels = raw2427Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2427 raw2427Labels permutation152 permutation4
    mixedMoment B raw2427step0 raw2427step0Labels = mixedMoment B raw2427step1 raw2427step1Labels := by
      have ha : raw2427step1 = raw2427step0 := by apply Matrix.ext; unfold raw2427step1 raw2427step0; decide +kernel
      have hl : raw2427step0Labels = labelEmbedding7 ∘ raw2427step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2427step0 raw2427step0Labels raw2427step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5374 node5374Labels := by rfl

theorem canonical2428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2428 raw2428Labels = mixedMoment B node3713 node3713Labels := by
  calc
    mixedMoment B raw2428 raw2428Labels = mixedMoment B raw2428step0 raw2428step0Labels := by
      have ha : raw2428step0 = (fun i j => raw2428 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2428step0 raw2428; decide +kernel
      have hl : raw2428step0Labels = raw2428Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2428 raw2428Labels permutation152 permutation4
    _ = mixedMoment B node3713 node3713Labels := by rfl

theorem canonical2429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2429 raw2429Labels = mixedMoment B node3713 node3713Labels := by
  calc
    mixedMoment B raw2429 raw2429Labels = mixedMoment B raw2429step0 raw2429step0Labels := by
      have ha : raw2429step0 = (fun i j => raw2429 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2429step0 raw2429; decide +kernel
      have hl : raw2429step0Labels = raw2429Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2429 raw2429Labels permutation176 permutation6
    mixedMoment B raw2429step0 raw2429step0Labels = mixedMoment B raw2429step1 raw2429step1Labels := by
      have ha : raw2429step1 = -raw2429step0 := by apply Matrix.ext; change ∀ i j, raw2429step1 i j = -(raw2429step0 i j); unfold raw2429step1 raw2429step0; decide +kernel
      have hl : raw2429step1Labels = raw2429step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2429step1 raw2429step1Labels = mixedMoment B raw2429step2 raw2429step2Labels := by
      have ha : raw2429step2 = raw2429step1 := by apply Matrix.ext; unfold raw2429step2 raw2429step1; decide +kernel
      have hl : raw2429step1Labels = labelEmbedding1 ∘ raw2429step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2429step1 raw2429step1Labels raw2429step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3713 node3713Labels := by rfl

theorem canonical2430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2430 raw2430Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw2430 raw2430Labels = mixedMoment B raw2430step0 raw2430step0Labels := by
      have ha : raw2430step0 = (fun i j => raw2430 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2430step0 raw2430; decide +kernel
      have hl : raw2430step0Labels = raw2430Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2430 raw2430Labels permutation152 permutation4
    mixedMoment B raw2430step0 raw2430step0Labels = mixedMoment B raw2430step1 raw2430step1Labels := by
      have ha : raw2430step1 = raw2430step0 := by apply Matrix.ext; unfold raw2430step1 raw2430step0; decide +kernel
      have hl : raw2430step0Labels = labelEmbedding7 ∘ raw2430step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2430step0 raw2430step0Labels raw2430step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical2431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2431 raw2431Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw2431 raw2431Labels = mixedMoment B raw2431step0 raw2431step0Labels := by
      have ha : raw2431step0 = (fun i j => raw2431 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2431step0 raw2431; decide +kernel
      have hl : raw2431step0Labels = raw2431Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2431 raw2431Labels permutation152 permutation4
    _ = mixedMoment B node3719 node3719Labels := by rfl

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

theorem canonical2432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2432 raw2432Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw2432 raw2432Labels = mixedMoment B raw2432step0 raw2432step0Labels := by
      have ha : raw2432step0 = (fun i j => raw2432 (permutation686 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2432step0 raw2432; decide +kernel
      have hl : raw2432step0Labels = raw2432Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2432 raw2432Labels permutation686 permutation6
    mixedMoment B raw2432step0 raw2432step0Labels = mixedMoment B raw2432step1 raw2432step1Labels := by
      have ha : raw2432step1 = raw2432step0 := by apply Matrix.ext; unfold raw2432step1 raw2432step0; decide +kernel
      have hl : raw2432step0Labels = labelEmbedding1 ∘ raw2432step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2432step0 raw2432step0Labels raw2432step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3795 node3795Labels := by rfl

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

theorem canonical2457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2457 raw2457Labels = mixedMoment B node5391 node5391Labels := by
  calc
    mixedMoment B raw2457 raw2457Labels = mixedMoment B raw2457step0 raw2457step0Labels := by
      have ha : raw2457step0 = (fun i j => raw2457 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2457step0 raw2457; decide +kernel
      have hl : raw2457step0Labels = raw2457Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2457 raw2457Labels permutation152 permutation4
    mixedMoment B raw2457step0 raw2457step0Labels = mixedMoment B raw2457step1 raw2457step1Labels := by
      have ha : raw2457step1 = raw2457step0 := by apply Matrix.ext; unfold raw2457step1 raw2457step0; decide +kernel
      have hl : raw2457step0Labels = labelEmbedding7 ∘ raw2457step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2457step0 raw2457step0Labels raw2457step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5391 node5391Labels := by rfl

theorem canonical2458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2458 raw2458Labels = mixedMoment B node3776 node3776Labels := by
  calc
    mixedMoment B raw2458 raw2458Labels = mixedMoment B raw2458step0 raw2458step0Labels := by
      have ha : raw2458step0 = (fun i j => raw2458 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2458step0 raw2458; decide +kernel
      have hl : raw2458step0Labels = raw2458Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2458 raw2458Labels permutation152 permutation4
    _ = mixedMoment B node3776 node3776Labels := by rfl

theorem canonical2459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2459 raw2459Labels = mixedMoment B node3778 node3778Labels := by
  calc
    mixedMoment B raw2459 raw2459Labels = mixedMoment B raw2459step0 raw2459step0Labels := by
      have ha : raw2459step0 = (fun i j => raw2459 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2459step0 raw2459; decide +kernel
      have hl : raw2459step0Labels = raw2459Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2459 raw2459Labels permutation155 permutation6
    mixedMoment B raw2459step0 raw2459step0Labels = mixedMoment B raw2459step1 raw2459step1Labels := by
      have ha : raw2459step1 = -raw2459step0 := by apply Matrix.ext; change ∀ i j, raw2459step1 i j = -(raw2459step0 i j); unfold raw2459step1 raw2459step0; decide +kernel
      have hl : raw2459step1Labels = raw2459step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2459step1 raw2459step1Labels = mixedMoment B raw2459step2 raw2459step2Labels := by
      have ha : raw2459step2 = raw2459step1 := by apply Matrix.ext; unfold raw2459step2 raw2459step1; decide +kernel
      have hl : raw2459step1Labels = labelEmbedding1 ∘ raw2459step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2459step1 raw2459step1Labels raw2459step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3778 node3778Labels := by rfl

theorem canonical2460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2460 raw2460Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw2460 raw2460Labels = mixedMoment B raw2460step0 raw2460step0Labels := by
      have ha : raw2460step0 = (fun i j => raw2460 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2460step0 raw2460; decide +kernel
      have hl : raw2460step0Labels = raw2460Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2460 raw2460Labels permutation152 permutation4
    mixedMoment B raw2460step0 raw2460step0Labels = mixedMoment B raw2460step1 raw2460step1Labels := by
      have ha : raw2460step1 = raw2460step0 := by apply Matrix.ext; unfold raw2460step1 raw2460step0; decide +kernel
      have hl : raw2460step0Labels = labelEmbedding7 ∘ raw2460step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2460step0 raw2460step0Labels raw2460step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

theorem canonical2461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2461 raw2461Labels = mixedMoment B node3779 node3779Labels := by
  calc
    mixedMoment B raw2461 raw2461Labels = mixedMoment B raw2461step0 raw2461step0Labels := by
      have ha : raw2461step0 = (fun i j => raw2461 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2461step0 raw2461; decide +kernel
      have hl : raw2461step0Labels = raw2461Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2461 raw2461Labels permutation152 permutation4
    _ = mixedMoment B node3779 node3779Labels := by rfl

theorem canonical2462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2462 raw2462Labels = mixedMoment B node3797 node3797Labels := by
  calc
    mixedMoment B raw2462 raw2462Labels = mixedMoment B raw2462step0 raw2462step0Labels := by
      have ha : raw2462step0 = (fun i j => raw2462 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2462step0 raw2462; decide +kernel
      have hl : raw2462step0Labels = raw2462Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2462 raw2462Labels permutation152 permutation6
    mixedMoment B raw2462step0 raw2462step0Labels = mixedMoment B raw2462step1 raw2462step1Labels := by
      have ha : raw2462step1 = -raw2462step0 := by apply Matrix.ext; change ∀ i j, raw2462step1 i j = -(raw2462step0 i j); unfold raw2462step1 raw2462step0; decide +kernel
      have hl : raw2462step1Labels = raw2462step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2462step1 raw2462step1Labels = mixedMoment B raw2462step2 raw2462step2Labels := by
      have ha : raw2462step2 = raw2462step1 := by apply Matrix.ext; unfold raw2462step2 raw2462step1; decide +kernel
      have hl : raw2462step1Labels = labelEmbedding1 ∘ raw2462step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2462step1 raw2462step1Labels raw2462step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3797 node3797Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical284
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical36355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36355 raw36355Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw36355 raw36355Labels = mixedMoment B raw36355step0 raw36355step0Labels := by
      have ha : raw36355step0 = (fun i j => raw36355 (permutation267 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36355step0 raw36355; decide +kernel
      have hl : raw36355step0Labels = raw36355Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36355 raw36355Labels permutation267 permutation6
    mixedMoment B raw36355step0 raw36355step0Labels = mixedMoment B raw36355step1 raw36355step1Labels := by
      have ha : raw36355step1 = raw36355step0 := by apply Matrix.ext; unfold raw36355step1 raw36355step0; decide +kernel
      have hl : raw36355step0Labels = labelEmbedding9 ∘ raw36355step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36355step0 raw36355step0Labels raw36355step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical36363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36363 raw36363Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw36363 raw36363Labels = mixedMoment B raw36363step0 raw36363step0Labels := by
      have hz : ∀ j, raw36363 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36363step0 = (fun i j => raw36363 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36363step0 raw36363; decide +kernel
      have hl : raw36363step0Labels = raw36363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36363 raw36363Labels permutation346 hz
    mixedMoment B raw36363step0 raw36363step0Labels = mixedMoment B raw36363step1 raw36363step1Labels := by
      have ha : raw36363step1 = (fun i j => raw36363step0 (permutation58 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36363step1 raw36363step0; decide +kernel
      have hl : raw36363step1Labels = raw36363step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36363step0 raw36363step0Labels permutation58 permutation6
    mixedMoment B raw36363step1 raw36363step1Labels = mixedMoment B raw36363step2 raw36363step2Labels := by
      have ha : raw36363step2 = raw36363step1 := by apply Matrix.ext; unfold raw36363step2 raw36363step1; decide +kernel
      have hl : raw36363step1Labels = labelEmbedding9 ∘ raw36363step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36363step1 raw36363step1Labels raw36363step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5367 node5367Labels := by rfl

theorem canonical36367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36367 raw36367Labels = mixedMoment B node5344 node5344Labels := by
  calc
    mixedMoment B raw36367 raw36367Labels = mixedMoment B raw36367step0 raw36367step0Labels := by
      have ha : raw36367step0 = (fun i j => raw36367 (permutation663 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36367step0 raw36367; decide +kernel
      have hl : raw36367step0Labels = raw36367Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36367 raw36367Labels permutation663 permutation4
    mixedMoment B raw36367step0 raw36367step0Labels = mixedMoment B raw36367step1 raw36367step1Labels := by
      have ha : raw36367step1 = raw36367step0 := by apply Matrix.ext; unfold raw36367step1 raw36367step0; decide +kernel
      have hl : raw36367step0Labels = labelEmbedding7 ∘ raw36367step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36367step0 raw36367step0Labels raw36367step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5344 node5344Labels := by rfl

theorem canonical36371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36371 raw36371Labels = mixedMoment B node5345 node5345Labels := by
  calc
    mixedMoment B raw36371 raw36371Labels = mixedMoment B raw36371step0 raw36371step0Labels := by
      have ha : raw36371step0 = (fun i j => raw36371 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36371step0 raw36371; decide +kernel
      have hl : raw36371step0Labels = raw36371Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36371 raw36371Labels permutation152 permutation6
    mixedMoment B raw36371step0 raw36371step0Labels = mixedMoment B raw36371step1 raw36371step1Labels := by
      have ha : raw36371step1 = raw36371step0 := by apply Matrix.ext; unfold raw36371step1 raw36371step0; decide +kernel
      have hl : raw36371step0Labels = labelEmbedding9 ∘ raw36371step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36371step0 raw36371step0Labels raw36371step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5345 node5345Labels := by rfl

theorem canonical36373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36373 raw36373Labels = mixedMoment B node5391 node5391Labels := by
  calc
    mixedMoment B raw36373 raw36373Labels = mixedMoment B raw36373step0 raw36373step0Labels := by
      have ha : raw36373step0 = (fun i j => raw36373 (permutation663 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36373step0 raw36373; decide +kernel
      have hl : raw36373step0Labels = raw36373Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36373 raw36373Labels permutation663 permutation6
    mixedMoment B raw36373step0 raw36373step0Labels = mixedMoment B raw36373step1 raw36373step1Labels := by
      have ha : raw36373step1 = -raw36373step0 := by apply Matrix.ext; change ∀ i j, raw36373step1 i j = -(raw36373step0 i j); unfold raw36373step1 raw36373step0; decide +kernel
      have hl : raw36373step1Labels = raw36373step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36373step1 raw36373step1Labels = mixedMoment B raw36373step2 raw36373step2Labels := by
      have ha : raw36373step2 = raw36373step1 := by apply Matrix.ext; unfold raw36373step2 raw36373step1; decide +kernel
      have hl : raw36373step1Labels = labelEmbedding9 ∘ raw36373step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36373step1 raw36373step1Labels raw36373step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5391 node5391Labels := by rfl

theorem canonical36374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36374 raw36374Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw36374 raw36374Labels = mixedMoment B raw36374step0 raw36374step0Labels := by
      have ha : raw36374step0 = (fun i j => raw36374 (permutation687 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36374step0 raw36374; decide +kernel
      have hl : raw36374step0Labels = raw36374Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36374 raw36374Labels permutation687 permutation6
    mixedMoment B raw36374step0 raw36374step0Labels = mixedMoment B raw36374step1 raw36374step1Labels := by
      have ha : raw36374step1 = -raw36374step0 := by apply Matrix.ext; change ∀ i j, raw36374step1 i j = -(raw36374step0 i j); unfold raw36374step1 raw36374step0; decide +kernel
      have hl : raw36374step1Labels = raw36374step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36374step1 raw36374step1Labels = mixedMoment B raw36374step2 raw36374step2Labels := by
      have ha : raw36374step2 = raw36374step1 := by apply Matrix.ext; unfold raw36374step2 raw36374step1; decide +kernel
      have hl : raw36374step1Labels = labelEmbedding9 ∘ raw36374step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36374step1 raw36374step1Labels raw36374step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

theorem canonical36375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36375 raw36375Labels = mixedMoment B node5460 node5460Labels := by
  calc
    mixedMoment B raw36375 raw36375Labels = mixedMoment B raw36375step0 raw36375step0Labels := by
      have ha : raw36375step0 = (fun i j => raw36375 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36375step0 raw36375; decide +kernel
      have hl : raw36375step0Labels = raw36375Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36375 raw36375Labels permutation152 permutation6
    mixedMoment B raw36375step0 raw36375step0Labels = mixedMoment B raw36375step1 raw36375step1Labels := by
      have ha : raw36375step1 = raw36375step0 := by apply Matrix.ext; unfold raw36375step1 raw36375step0; decide +kernel
      have hl : raw36375step0Labels = labelEmbedding9 ∘ raw36375step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36375step0 raw36375step0Labels raw36375step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5460 node5460Labels := by rfl

theorem canonical36377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36377 raw36377Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw36377 raw36377Labels = mixedMoment B raw36377step0 raw36377step0Labels := by
      have ha : raw36377step0 = (fun i j => raw36377 (permutation663 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36377step0 raw36377; decide +kernel
      have hl : raw36377step0Labels = raw36377Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36377 raw36377Labels permutation663 permutation4
    mixedMoment B raw36377step0 raw36377step0Labels = mixedMoment B raw36377step1 raw36377step1Labels := by
      have ha : raw36377step1 = raw36377step0 := by apply Matrix.ext; unfold raw36377step1 raw36377step0; decide +kernel
      have hl : raw36377step0Labels = labelEmbedding7 ∘ raw36377step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36377step0 raw36377step0Labels raw36377step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical285
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical36523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36523 raw36523Labels = mixedMoment B node5369 node5369Labels := by
  calc
    mixedMoment B raw36523 raw36523Labels = mixedMoment B raw36523step0 raw36523step0Labels := by
      have hz : ∀ j, raw36523 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36523step0 = (fun i j => raw36523 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36523step0 raw36523; decide +kernel
      have hl : raw36523step0Labels = raw36523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36523 raw36523Labels permutation346 hz
    mixedMoment B raw36523step0 raw36523step0Labels = mixedMoment B raw36523step1 raw36523step1Labels := by
      have ha : raw36523step1 = (fun i j => raw36523step0 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36523step1 raw36523step0; decide +kernel
      have hl : raw36523step1Labels = raw36523step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36523step0 raw36523step0Labels permutation56 permutation6
    mixedMoment B raw36523step1 raw36523step1Labels = mixedMoment B raw36523step2 raw36523step2Labels := by
      have ha : raw36523step2 = raw36523step1 := by apply Matrix.ext; unfold raw36523step2 raw36523step1; decide +kernel
      have hl : raw36523step1Labels = labelEmbedding9 ∘ raw36523step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36523step1 raw36523step1Labels raw36523step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5369 node5369Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical288
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical36888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36888 raw36888Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw36888 raw36888Labels = mixedMoment B raw36888step0 raw36888step0Labels := by
      have ha : raw36888step0 = (fun i j => raw36888 (permutation289 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36888step0 raw36888; decide +kernel
      have hl : raw36888step0Labels = raw36888Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36888 raw36888Labels permutation289 permutation4
    mixedMoment B raw36888step0 raw36888step0Labels = mixedMoment B raw36888step1 raw36888step1Labels := by
      have ha : raw36888step1 = -raw36888step0 := by apply Matrix.ext; change ∀ i j, raw36888step1 i j = -(raw36888step0 i j); unfold raw36888step1 raw36888step0; decide +kernel
      have hl : raw36888step1Labels = raw36888step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36888step1 raw36888step1Labels = mixedMoment B raw36888step2 raw36888step2Labels := by
      have ha : raw36888step2 = raw36888step1 := by apply Matrix.ext; unfold raw36888step2 raw36888step1; decide +kernel
      have hl : raw36888step1Labels = labelEmbedding7 ∘ raw36888step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36888step1 raw36888step1Labels raw36888step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

theorem canonical36889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36889 raw36889Labels = mixedMoment B node5374 node5374Labels := by
  calc
    mixedMoment B raw36889 raw36889Labels = mixedMoment B raw36889step0 raw36889step0Labels := by
      have ha : raw36889step0 = (fun i j => raw36889 (permutation289 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36889step0 raw36889; decide +kernel
      have hl : raw36889step0Labels = raw36889Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36889 raw36889Labels permutation289 permutation4
    mixedMoment B raw36889step0 raw36889step0Labels = mixedMoment B raw36889step1 raw36889step1Labels := by
      have ha : raw36889step1 = -raw36889step0 := by apply Matrix.ext; change ∀ i j, raw36889step1 i j = -(raw36889step0 i j); unfold raw36889step1 raw36889step0; decide +kernel
      have hl : raw36889step1Labels = raw36889step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36889step1 raw36889step1Labels = mixedMoment B raw36889step2 raw36889step2Labels := by
      have ha : raw36889step2 = raw36889step1 := by apply Matrix.ext; unfold raw36889step2 raw36889step1; decide +kernel
      have hl : raw36889step1Labels = labelEmbedding7 ∘ raw36889step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36889step1 raw36889step1Labels raw36889step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5374 node5374Labels := by rfl

theorem canonical36890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36890 raw36890Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw36890 raw36890Labels = mixedMoment B raw36890step0 raw36890step0Labels := by
      have ha : raw36890step0 = (fun i j => raw36890 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36890step0 raw36890; decide +kernel
      have hl : raw36890step0Labels = raw36890Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36890 raw36890Labels permutation265 permutation6
    mixedMoment B raw36890step0 raw36890step0Labels = mixedMoment B raw36890step1 raw36890step1Labels := by
      have ha : raw36890step1 = raw36890step0 := by apply Matrix.ext; unfold raw36890step1 raw36890step0; decide +kernel
      have hl : raw36890step0Labels = labelEmbedding9 ∘ raw36890step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36890step0 raw36890step0Labels raw36890step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical36891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36891 raw36891Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw36891 raw36891Labels = mixedMoment B raw36891step0 raw36891step0Labels := by
      have ha : raw36891step0 = (fun i j => raw36891 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36891step0 raw36891; decide +kernel
      have hl : raw36891step0Labels = raw36891Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36891 raw36891Labels permutation265 permutation6
    mixedMoment B raw36891step0 raw36891step0Labels = mixedMoment B raw36891step1 raw36891step1Labels := by
      have ha : raw36891step1 = raw36891step0 := by apply Matrix.ext; unfold raw36891step1 raw36891step0; decide +kernel
      have hl : raw36891step0Labels = labelEmbedding9 ∘ raw36891step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36891step0 raw36891step0Labels raw36891step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5380 node5380Labels := by rfl

theorem canonical36892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36892 raw36892Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw36892 raw36892Labels = mixedMoment B raw36892step0 raw36892step0Labels := by
      have ha : raw36892step0 = (fun i j => raw36892 (permutation663 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36892step0 raw36892; decide +kernel
      have hl : raw36892step0Labels = raw36892Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36892 raw36892Labels permutation663 permutation6
    mixedMoment B raw36892step0 raw36892step0Labels = mixedMoment B raw36892step1 raw36892step1Labels := by
      have ha : raw36892step1 = -raw36892step0 := by apply Matrix.ext; change ∀ i j, raw36892step1 i j = -(raw36892step0 i j); unfold raw36892step1 raw36892step0; decide +kernel
      have hl : raw36892step1Labels = raw36892step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36892step1 raw36892step1Labels = mixedMoment B raw36892step2 raw36892step2Labels := by
      have ha : raw36892step2 = raw36892step1 := by apply Matrix.ext; unfold raw36892step2 raw36892step1; decide +kernel
      have hl : raw36892step1Labels = labelEmbedding9 ∘ raw36892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36892step1 raw36892step1Labels raw36892step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

theorem canonical36893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36893 raw36893Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw36893 raw36893Labels = mixedMoment B raw36893step0 raw36893step0Labels := by
      have hz : ∀ j, raw36893 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36893step0 = (fun i j => raw36893 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36893step0 raw36893; decide +kernel
      have hl : raw36893step0Labels = raw36893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36893 raw36893Labels permutation346 hz
    mixedMoment B raw36893step0 raw36893step0Labels = mixedMoment B raw36893step1 raw36893step1Labels := by
      have hz : ∀ i, raw36893step0 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw36893step1 = (fun i j => raw36893step0 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw36893step1 raw36893step0; decide +kernel
      have hl : raw36893step1Labels = (fun j => raw36893step0Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw36893step0 raw36893step0Labels permutation2 hz
    mixedMoment B raw36893step1 raw36893step1Labels = mixedMoment B raw36893step2 raw36893step2Labels := by
      have ha : raw36893step2 = -raw36893step1 := by apply Matrix.ext; change ∀ i j, raw36893step2 i j = -(raw36893step1 i j); unfold raw36893step2 raw36893step1; decide +kernel
      have hl : raw36893step2Labels = raw36893step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36893step2 raw36893step2Labels = mixedMoment B raw36893step3 raw36893step3Labels := by
      have ha : raw36893step3 = raw36893step2 := by apply Matrix.ext; unfold raw36893step3 raw36893step2; decide +kernel
      have hl : raw36893step2Labels = labelEmbedding3 ∘ raw36893step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36893step2 raw36893step2Labels raw36893step3Labels labelEmbedding3 hl
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical36894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36894 raw36894Labels = mixedMoment B node5017 node5017Labels := by
  calc
    mixedMoment B raw36894 raw36894Labels = mixedMoment B raw36894step0 raw36894step0Labels := by
      have hz : ∀ j, raw36894 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36894step0 = (fun i j => raw36894 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36894step0 raw36894; decide +kernel
      have hl : raw36894step0Labels = raw36894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36894 raw36894Labels permutation346 hz
    mixedMoment B raw36894step0 raw36894step0Labels = mixedMoment B raw36894step1 raw36894step1Labels := by
      have ha : raw36894step1 = (fun i j => raw36894step0 (permutation56 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36894step1 raw36894step0; decide +kernel
      have hl : raw36894step1Labels = raw36894step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36894step0 raw36894step0Labels permutation56 permutation4
    mixedMoment B raw36894step1 raw36894step1Labels = mixedMoment B raw36894step2 raw36894step2Labels := by
      have ha : raw36894step2 = -raw36894step1 := by apply Matrix.ext; change ∀ i j, raw36894step2 i j = -(raw36894step1 i j); unfold raw36894step2 raw36894step1; decide +kernel
      have hl : raw36894step2Labels = raw36894step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36894step2 raw36894step2Labels = mixedMoment B raw36894step3 raw36894step3Labels := by
      have ha : raw36894step3 = raw36894step2 := by apply Matrix.ext; unfold raw36894step3 raw36894step2; decide +kernel
      have hl : raw36894step2Labels = labelEmbedding7 ∘ raw36894step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36894step2 raw36894step2Labels raw36894step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5017 node5017Labels := by rfl

theorem canonical36895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36895 raw36895Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw36895 raw36895Labels = mixedMoment B raw36895step0 raw36895step0Labels := by
      have hz : ∀ j, raw36895 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36895step0 = (fun i j => raw36895 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36895step0 raw36895; decide +kernel
      have hl : raw36895step0Labels = raw36895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36895 raw36895Labels permutation346 hz
    mixedMoment B raw36895step0 raw36895step0Labels = mixedMoment B raw36895step1 raw36895step1Labels := by
      have ha : raw36895step1 = (fun i j => raw36895step0 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36895step1 raw36895step0; decide +kernel
      have hl : raw36895step1Labels = raw36895step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36895step0 raw36895step0Labels permutation56 permutation6
    mixedMoment B raw36895step1 raw36895step1Labels = mixedMoment B raw36895step2 raw36895step2Labels := by
      have ha : raw36895step2 = raw36895step1 := by apply Matrix.ext; unfold raw36895step2 raw36895step1; decide +kernel
      have hl : raw36895step1Labels = labelEmbedding9 ∘ raw36895step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36895step1 raw36895step1Labels raw36895step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5367 node5367Labels := by rfl

theorem canonical36896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36896 raw36896Labels = mixedMoment B node5314 node5314Labels := by
  calc
    mixedMoment B raw36896 raw36896Labels = mixedMoment B raw36896step0 raw36896step0Labels := by
      have ha : raw36896step0 = (fun i j => raw36896 (permutation154 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36896step0 raw36896; decide +kernel
      have hl : raw36896step0Labels = raw36896Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36896 raw36896Labels permutation154 permutation4
    mixedMoment B raw36896step0 raw36896step0Labels = mixedMoment B raw36896step1 raw36896step1Labels := by
      have ha : raw36896step1 = -raw36896step0 := by apply Matrix.ext; change ∀ i j, raw36896step1 i j = -(raw36896step0 i j); unfold raw36896step1 raw36896step0; decide +kernel
      have hl : raw36896step1Labels = raw36896step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36896step1 raw36896step1Labels = mixedMoment B raw36896step2 raw36896step2Labels := by
      have ha : raw36896step2 = raw36896step1 := by apply Matrix.ext; unfold raw36896step2 raw36896step1; decide +kernel
      have hl : raw36896step1Labels = labelEmbedding7 ∘ raw36896step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36896step1 raw36896step1Labels raw36896step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5314 node5314Labels := by rfl

theorem canonical36897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36897 raw36897Labels = mixedMoment B node4987 node4987Labels := by
  calc
    mixedMoment B raw36897 raw36897Labels = mixedMoment B raw36897step0 raw36897step0Labels := by
      have ha : raw36897step0 = (fun i j => raw36897 (permutation267 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36897step0 raw36897; decide +kernel
      have hl : raw36897step0Labels = raw36897Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36897 raw36897Labels permutation267 permutation4
    mixedMoment B raw36897step0 raw36897step0Labels = mixedMoment B raw36897step1 raw36897step1Labels := by
      have ha : raw36897step1 = -raw36897step0 := by apply Matrix.ext; change ∀ i j, raw36897step1 i j = -(raw36897step0 i j); unfold raw36897step1 raw36897step0; decide +kernel
      have hl : raw36897step1Labels = raw36897step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36897step1 raw36897step1Labels = mixedMoment B raw36897step2 raw36897step2Labels := by
      have ha : raw36897step2 = raw36897step1 := by apply Matrix.ext; unfold raw36897step2 raw36897step1; decide +kernel
      have hl : raw36897step1Labels = labelEmbedding7 ∘ raw36897step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36897step1 raw36897step1Labels raw36897step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4987 node4987Labels := by rfl

theorem canonical36898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36898 raw36898Labels = mixedMoment B node5333 node5333Labels := by
  calc
    mixedMoment B raw36898 raw36898Labels = mixedMoment B raw36898step0 raw36898step0Labels := by
      have ha : raw36898step0 = (fun i j => raw36898 (permutation660 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36898step0 raw36898; decide +kernel
      have hl : raw36898step0Labels = raw36898Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36898 raw36898Labels permutation660 permutation4
    mixedMoment B raw36898step0 raw36898step0Labels = mixedMoment B raw36898step1 raw36898step1Labels := by
      have ha : raw36898step1 = raw36898step0 := by apply Matrix.ext; unfold raw36898step1 raw36898step0; decide +kernel
      have hl : raw36898step0Labels = labelEmbedding7 ∘ raw36898step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36898step0 raw36898step0Labels raw36898step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5333 node5333Labels := by rfl

theorem canonical36899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36899 raw36899Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw36899 raw36899Labels = mixedMoment B raw36899step0 raw36899step0Labels := by
      have ha : raw36899step0 = (fun i j => raw36899 (permutation267 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36899step0 raw36899; decide +kernel
      have hl : raw36899step0Labels = raw36899Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36899 raw36899Labels permutation267 permutation6
    mixedMoment B raw36899step0 raw36899step0Labels = mixedMoment B raw36899step1 raw36899step1Labels := by
      have ha : raw36899step1 = raw36899step0 := by apply Matrix.ext; unfold raw36899step1 raw36899step0; decide +kernel
      have hl : raw36899step0Labels = labelEmbedding9 ∘ raw36899step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36899step0 raw36899step0Labels raw36899step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

theorem canonical36900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36900 raw36900Labels = mixedMoment B node5314 node5314Labels := by
  calc
    mixedMoment B raw36900 raw36900Labels = mixedMoment B raw36900step0 raw36900step0Labels := by
      have ha : raw36900step0 = (fun i j => raw36900 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36900step0 raw36900; decide +kernel
      have hl : raw36900step0Labels = raw36900Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36900 raw36900Labels permutation152 permutation4
    mixedMoment B raw36900step0 raw36900step0Labels = mixedMoment B raw36900step1 raw36900step1Labels := by
      have ha : raw36900step1 = -raw36900step0 := by apply Matrix.ext; change ∀ i j, raw36900step1 i j = -(raw36900step0 i j); unfold raw36900step1 raw36900step0; decide +kernel
      have hl : raw36900step1Labels = raw36900step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36900step1 raw36900step1Labels = mixedMoment B raw36900step2 raw36900step2Labels := by
      have ha : raw36900step2 = raw36900step1 := by apply Matrix.ext; unfold raw36900step2 raw36900step1; decide +kernel
      have hl : raw36900step1Labels = labelEmbedding7 ∘ raw36900step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36900step1 raw36900step1Labels raw36900step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5314 node5314Labels := by rfl

theorem canonical36901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36901 raw36901Labels = mixedMoment B node4987 node4987Labels := by
  calc
    mixedMoment B raw36901 raw36901Labels = mixedMoment B raw36901step0 raw36901step0Labels := by
      have ha : raw36901step0 = (fun i j => raw36901 (permutation265 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36901step0 raw36901; decide +kernel
      have hl : raw36901step0Labels = raw36901Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36901 raw36901Labels permutation265 permutation4
    mixedMoment B raw36901step0 raw36901step0Labels = mixedMoment B raw36901step1 raw36901step1Labels := by
      have ha : raw36901step1 = -raw36901step0 := by apply Matrix.ext; change ∀ i j, raw36901step1 i j = -(raw36901step0 i j); unfold raw36901step1 raw36901step0; decide +kernel
      have hl : raw36901step1Labels = raw36901step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36901step1 raw36901step1Labels = mixedMoment B raw36901step2 raw36901step2Labels := by
      have ha : raw36901step2 = raw36901step1 := by apply Matrix.ext; unfold raw36901step2 raw36901step1; decide +kernel
      have hl : raw36901step1Labels = labelEmbedding7 ∘ raw36901step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36901step1 raw36901step1Labels raw36901step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4987 node4987Labels := by rfl

theorem canonical36902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36902 raw36902Labels = mixedMoment B node5333 node5333Labels := by
  calc
    mixedMoment B raw36902 raw36902Labels = mixedMoment B raw36902step0 raw36902step0Labels := by
      have ha : raw36902step0 = (fun i j => raw36902 (permutation684 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36902step0 raw36902; decide +kernel
      have hl : raw36902step0Labels = raw36902Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36902 raw36902Labels permutation684 permutation4
    mixedMoment B raw36902step0 raw36902step0Labels = mixedMoment B raw36902step1 raw36902step1Labels := by
      have ha : raw36902step1 = raw36902step0 := by apply Matrix.ext; unfold raw36902step1 raw36902step0; decide +kernel
      have hl : raw36902step0Labels = labelEmbedding7 ∘ raw36902step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36902step0 raw36902step0Labels raw36902step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5333 node5333Labels := by rfl

theorem canonical36903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36903 raw36903Labels = mixedMoment B node5344 node5344Labels := by
  calc
    mixedMoment B raw36903 raw36903Labels = mixedMoment B raw36903step0 raw36903step0Labels := by
      have ha : raw36903step0 = (fun i j => raw36903 (permutation687 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36903step0 raw36903; decide +kernel
      have hl : raw36903step0Labels = raw36903Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36903 raw36903Labels permutation687 permutation4
    mixedMoment B raw36903step0 raw36903step0Labels = mixedMoment B raw36903step1 raw36903step1Labels := by
      have ha : raw36903step1 = raw36903step0 := by apply Matrix.ext; unfold raw36903step1 raw36903step0; decide +kernel
      have hl : raw36903step0Labels = labelEmbedding7 ∘ raw36903step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36903step0 raw36903step0Labels raw36903step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5344 node5344Labels := by rfl

theorem canonical36904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36904 raw36904Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw36904 raw36904Labels = mixedMoment B raw36904step0 raw36904step0Labels := by
      have ha : raw36904step0 = (fun i j => raw36904 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36904step0 raw36904; decide +kernel
      have hl : raw36904step0Labels = raw36904Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36904 raw36904Labels permutation265 permutation6
    mixedMoment B raw36904step0 raw36904step0Labels = mixedMoment B raw36904step1 raw36904step1Labels := by
      have ha : raw36904step1 = raw36904step0 := by apply Matrix.ext; unfold raw36904step1 raw36904step0; decide +kernel
      have hl : raw36904step0Labels = labelEmbedding9 ∘ raw36904step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36904step0 raw36904step0Labels raw36904step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

theorem canonical36905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36905 raw36905Labels = mixedMoment B node5025 node5025Labels := by
  calc
    mixedMoment B raw36905 raw36905Labels = mixedMoment B raw36905step0 raw36905step0Labels := by
      have ha : raw36905step0 = (fun i j => raw36905 (permutation663 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36905step0 raw36905; decide +kernel
      have hl : raw36905step0Labels = raw36905Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36905 raw36905Labels permutation663 permutation4
    mixedMoment B raw36905step0 raw36905step0Labels = mixedMoment B raw36905step1 raw36905step1Labels := by
      have ha : raw36905step1 = raw36905step0 := by apply Matrix.ext; unfold raw36905step1 raw36905step0; decide +kernel
      have hl : raw36905step0Labels = labelEmbedding7 ∘ raw36905step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36905step0 raw36905step0Labels raw36905step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5025 node5025Labels := by rfl

theorem canonical36906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36906 raw36906Labels = mixedMoment B node4986 node4986Labels := by
  calc
    mixedMoment B raw36906 raw36906Labels = mixedMoment B raw36906step0 raw36906step0Labels := by
      have ha : raw36906step0 = (fun i j => raw36906 (permutation265 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36906step0 raw36906; decide +kernel
      have hl : raw36906step0Labels = raw36906Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36906 raw36906Labels permutation265 permutation4
    mixedMoment B raw36906step0 raw36906step0Labels = mixedMoment B raw36906step1 raw36906step1Labels := by
      have ha : raw36906step1 = -raw36906step0 := by apply Matrix.ext; change ∀ i j, raw36906step1 i j = -(raw36906step0 i j); unfold raw36906step1 raw36906step0; decide +kernel
      have hl : raw36906step1Labels = raw36906step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36906step1 raw36906step1Labels = mixedMoment B raw36906step2 raw36906step2Labels := by
      have ha : raw36906step2 = raw36906step1 := by apply Matrix.ext; unfold raw36906step2 raw36906step1; decide +kernel
      have hl : raw36906step1Labels = labelEmbedding7 ∘ raw36906step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36906step1 raw36906step1Labels raw36906step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4986 node4986Labels := by rfl

theorem canonical36907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36907 raw36907Labels = mixedMoment B node5030 node5030Labels := by
  calc
    mixedMoment B raw36907 raw36907Labels = mixedMoment B raw36907step0 raw36907step0Labels := by
      have ha : raw36907step0 = (fun i j => raw36907 (permutation660 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36907step0 raw36907; decide +kernel
      have hl : raw36907step0Labels = raw36907Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36907 raw36907Labels permutation660 permutation4
    mixedMoment B raw36907step0 raw36907step0Labels = mixedMoment B raw36907step1 raw36907step1Labels := by
      have ha : raw36907step1 = raw36907step0 := by apply Matrix.ext; unfold raw36907step1 raw36907step0; decide +kernel
      have hl : raw36907step0Labels = labelEmbedding7 ∘ raw36907step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36907step0 raw36907step0Labels raw36907step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5030 node5030Labels := by rfl

theorem canonical36908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36908 raw36908Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw36908 raw36908Labels = mixedMoment B raw36908step0 raw36908step0Labels := by
      have ha : raw36908step0 = (fun i j => raw36908 (permutation687 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36908step0 raw36908; decide +kernel
      have hl : raw36908step0Labels = raw36908Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36908 raw36908Labels permutation687 permutation4
    mixedMoment B raw36908step0 raw36908step0Labels = mixedMoment B raw36908step1 raw36908step1Labels := by
      have ha : raw36908step1 = raw36908step0 := by apply Matrix.ext; unfold raw36908step1 raw36908step0; decide +kernel
      have hl : raw36908step0Labels = labelEmbedding7 ∘ raw36908step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36908step0 raw36908step0Labels raw36908step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

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

theorem singleton4986 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4986 node4986Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2371 node2371Labels + mixedMoment B node3335 node3335Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1992 singletonSmall4986
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4986) = raw1992Labels := by decide +kernel
  rw [hl, canonical1992 B hB] at h
  have hc0 : mixedMoment B raw1992 (Fin.cases (0 : Fin 2) singletonSmall4986) =
      mixedMoment B node2371 node2371Labels := by
    have ha : raw1992 = raw1993 := by apply Matrix.ext; unfold raw1992 raw1993; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4986 = raw1993Labels := by decide +kernel
    rw [ha, hj, canonical1993 B hB]
  have hc1 : mixedMoment B raw1992 (Fin.cases (1 : Fin 2) singletonSmall4986) =
      mixedMoment B node3335 node3335Labels := by
    have ha : raw1992 = raw1994 := by apply Matrix.ext; unfold raw1992 raw1994; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4986 = raw1994Labels := by decide +kernel
    rw [ha, hj, canonical1994 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4987 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4987 node4987Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2372 node2372Labels + mixedMoment B node3336 node3336Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1995 singletonSmall4987
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4987) = raw1995Labels := by decide +kernel
  rw [hl, canonical1995 B hB] at h
  have hc0 : mixedMoment B raw1995 (Fin.cases (0 : Fin 2) singletonSmall4987) =
      mixedMoment B node2372 node2372Labels := by
    have ha : raw1995 = raw1996 := by apply Matrix.ext; unfold raw1995 raw1996; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4987 = raw1996Labels := by decide +kernel
    rw [ha, hj, canonical1996 B hB]
  have hc1 : mixedMoment B raw1995 (Fin.cases (1 : Fin 2) singletonSmall4987) =
      mixedMoment B node3336 node3336Labels := by
    have ha : raw1995 = raw1997 := by apply Matrix.ext; unfold raw1995 raw1997; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4987 = raw1997Labels := by decide +kernel
    rw [ha, hj, canonical1997 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5030 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5030 node5030Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2419 node2419Labels + mixedMoment B node3425 node3425Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2043 singletonSmall5030
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5030) = raw2043Labels := by decide +kernel
  rw [hl, canonical2043 B hB] at h
  have hc0 : mixedMoment B raw2043 (Fin.cases (0 : Fin 2) singletonSmall5030) =
      mixedMoment B node2419 node2419Labels := by
    have ha : raw2043 = raw2044 := by apply Matrix.ext; unfold raw2043 raw2044; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5030 = raw2044Labels := by decide +kernel
    rw [ha, hj, canonical2044 B hB]
  have hc1 : mixedMoment B raw2043 (Fin.cases (1 : Fin 2) singletonSmall5030) =
      mixedMoment B node3425 node3425Labels := by
    have ha : raw2043 = raw2045 := by apply Matrix.ext; unfold raw2043 raw2045; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5030 = raw2045Labels := by decide +kernel
    rw [ha, hj, canonical2045 B hB]
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

theorem singleton5056 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5056 node5056Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2459 node2459Labels + mixedMoment B node3429 node3429Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2082 singletonSmall5056
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5056) = raw2082Labels := by decide +kernel
  rw [hl, canonical2082 B hB] at h
  have hc0 : mixedMoment B raw2082 (Fin.cases (0 : Fin 2) singletonSmall5056) =
      mixedMoment B node2459 node2459Labels := by
    have ha : raw2082 = raw2083 := by apply Matrix.ext; unfold raw2082 raw2083; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5056 = raw2083Labels := by decide +kernel
    rw [ha, hj, canonical2083 B hB]
  have hc1 : mixedMoment B raw2082 (Fin.cases (1 : Fin 2) singletonSmall5056) =
      mixedMoment B node3429 node3429Labels := by
    have ha : raw2082 = raw2084 := by apply Matrix.ext; unfold raw2082 raw2084; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5056 = raw2084Labels := by decide +kernel
    rw [ha, hj, canonical2084 B hB]
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

theorem singleton5123 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5123 node5123Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2536 node2536Labels + mixedMoment B node3370 node3370Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2154 singletonSmall5123
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5123) = raw2154Labels := by decide +kernel
  rw [hl, canonical2154 B hB] at h
  have hc0 : mixedMoment B raw2154 (Fin.cases (0 : Fin 2) singletonSmall5123) =
      mixedMoment B node2536 node2536Labels := by
    have ha : raw2154 = raw2155 := by apply Matrix.ext; unfold raw2154 raw2155; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5123 = raw2155Labels := by decide +kernel
    rw [ha, hj, canonical2155 B hB]
  have hc1 : mixedMoment B raw2154 (Fin.cases (1 : Fin 2) singletonSmall5123) =
      mixedMoment B node3370 node3370Labels := by
    have ha : raw2154 = raw2156 := by apply Matrix.ext; unfold raw2154 raw2156; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5123 = raw2156Labels := by decide +kernel
    rw [ha, hj, canonical2156 B hB]
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

theorem singleton5333 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5333 node5333Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3668 node3668Labels + mixedMoment B node3677 node3677Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2364 singletonSmall5333
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5333) = raw2364Labels := by decide +kernel
  rw [hl, canonical2364 B hB] at h
  have hc0 : mixedMoment B raw2364 (Fin.cases (0 : Fin 2) singletonSmall5333) =
      mixedMoment B node3668 node3668Labels := by
    have ha : raw2364 = raw2365 := by apply Matrix.ext; unfold raw2364 raw2365; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5333 = raw2365Labels := by decide +kernel
    rw [ha, hj, canonical2365 B hB]
  have hc1 : mixedMoment B raw2364 (Fin.cases (1 : Fin 2) singletonSmall5333) =
      mixedMoment B node3677 node3677Labels := by
    have ha : raw2364 = raw2366 := by apply Matrix.ext; unfold raw2364 raw2366; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5333 = raw2366Labels := by decide +kernel
    rw [ha, hj, canonical2366 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5344 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5344 node5344Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3681 node3681Labels + mixedMoment B node3681 node3681Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2382 singletonSmall5344
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5344) = raw2382Labels := by decide +kernel
  rw [hl, canonical2382 B hB] at h
  have hc0 : mixedMoment B raw2382 (Fin.cases (0 : Fin 2) singletonSmall5344) =
      mixedMoment B node3681 node3681Labels := by
    have ha : raw2382 = raw2383 := by apply Matrix.ext; unfold raw2382 raw2383; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5344 = raw2383Labels := by decide +kernel
    rw [ha, hj, canonical2383 B hB]
  have hc1 : mixedMoment B raw2382 (Fin.cases (1 : Fin 2) singletonSmall5344) =
      mixedMoment B node3681 node3681Labels := by
    have ha : raw2382 = raw2384 := by apply Matrix.ext; unfold raw2382 raw2384; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5344 = raw2384Labels := by decide +kernel
    rw [ha, hj, canonical2384 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5346 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5346 node5346Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3683 node3683Labels + mixedMoment B node3746 node3746Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2385 singletonSmall5346
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5346) = raw2385Labels := by decide +kernel
  rw [hl, canonical2385 B hB] at h
  have hc0 : mixedMoment B raw2385 (Fin.cases (0 : Fin 2) singletonSmall5346) =
      mixedMoment B node3683 node3683Labels := by
    have ha : raw2385 = raw2386 := by apply Matrix.ext; unfold raw2385 raw2386; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5346 = raw2386Labels := by decide +kernel
    rw [ha, hj, canonical2386 B hB]
  have hc1 : mixedMoment B raw2385 (Fin.cases (1 : Fin 2) singletonSmall5346) =
      mixedMoment B node3746 node3746Labels := by
    have ha : raw2385 = raw2387 := by apply Matrix.ext; unfold raw2385 raw2387; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5346 = raw2387Labels := by decide +kernel
    rw [ha, hj, canonical2387 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5374 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5374 node5374Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3713 node3713Labels + mixedMoment B node3713 node3713Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2427 singletonSmall5374
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5374) = raw2427Labels := by decide +kernel
  rw [hl, canonical2427 B hB] at h
  have hc0 : mixedMoment B raw2427 (Fin.cases (0 : Fin 2) singletonSmall5374) =
      mixedMoment B node3713 node3713Labels := by
    have ha : raw2427 = raw2428 := by apply Matrix.ext; unfold raw2427 raw2428; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5374 = raw2428Labels := by decide +kernel
    rw [ha, hj, canonical2428 B hB]
  have hc1 : mixedMoment B raw2427 (Fin.cases (1 : Fin 2) singletonSmall5374) =
      mixedMoment B node3713 node3713Labels := by
    have ha : raw2427 = raw2429 := by apply Matrix.ext; unfold raw2427 raw2429; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5374 = raw2429Labels := by decide +kernel
    rw [ha, hj, canonical2429 B hB]
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

theorem singleton5378 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5378 node5378Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3719 node3719Labels + mixedMoment B node3795 node3795Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2430 singletonSmall5378
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5378) = raw2430Labels := by decide +kernel
  rw [hl, canonical2430 B hB] at h
  have hc0 : mixedMoment B raw2430 (Fin.cases (0 : Fin 2) singletonSmall5378) =
      mixedMoment B node3719 node3719Labels := by
    have ha : raw2430 = raw2431 := by apply Matrix.ext; unfold raw2430 raw2431; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5378 = raw2431Labels := by decide +kernel
    rw [ha, hj, canonical2431 B hB]
  have hc1 : mixedMoment B raw2430 (Fin.cases (1 : Fin 2) singletonSmall5378) =
      mixedMoment B node3795 node3795Labels := by
    have ha : raw2430 = raw2432 := by apply Matrix.ext; unfold raw2430 raw2432; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5378 = raw2432Labels := by decide +kernel
    rw [ha, hj, canonical2432 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton5391 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5391 node5391Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3776 node3776Labels + mixedMoment B node3778 node3778Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2457 singletonSmall5391
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5391) = raw2457Labels := by decide +kernel
  rw [hl, canonical2457 B hB] at h
  have hc0 : mixedMoment B raw2457 (Fin.cases (0 : Fin 2) singletonSmall5391) =
      mixedMoment B node3776 node3776Labels := by
    have ha : raw2457 = raw2458 := by apply Matrix.ext; unfold raw2457 raw2458; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5391 = raw2458Labels := by decide +kernel
    rw [ha, hj, canonical2458 B hB]
  have hc1 : mixedMoment B raw2457 (Fin.cases (1 : Fin 2) singletonSmall5391) =
      mixedMoment B node3778 node3778Labels := by
    have ha : raw2457 = raw2459 := by apply Matrix.ext; unfold raw2457 raw2459; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5391 = raw2459Labels := by decide +kernel
    rw [ha, hj, canonical2459 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5393 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5393 node5393Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3779 node3779Labels + mixedMoment B node3797 node3797Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2460 singletonSmall5393
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5393) = raw2460Labels := by decide +kernel
  rw [hl, canonical2460 B hB] at h
  have hc0 : mixedMoment B raw2460 (Fin.cases (0 : Fin 2) singletonSmall5393) =
      mixedMoment B node3779 node3779Labels := by
    have ha : raw2460 = raw2461 := by apply Matrix.ext; unfold raw2460 raw2461; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5393 = raw2461Labels := by decide +kernel
    rw [ha, hj, canonical2461 B hB]
  have hc1 : mixedMoment B raw2460 (Fin.cases (1 : Fin 2) singletonSmall5393) =
      mixedMoment B node3797 node3797Labels := by
    have ha : raw2460 = raw2462 := by apply Matrix.ext; unfold raw2460 raw2462; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5393 = raw2462Labels := by decide +kernel
    rw [ha, hj, canonical2462 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5460 node5460Labels = 0 := by
  exact mixedMoment_alpha B hF node5460 node5460Labels 2 permutation152
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2371 node2371Labels = Sparse.eval nodeValue2371 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2371) = mixedMoment B node2371 node2371Labels := rfl
  simpa [nodeValue2371, Sparse.eval] using hc.symm

theorem sound2372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2372 node2372Labels = Sparse.eval nodeValue2372 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2372) = mixedMoment B node2372 node2372Labels := rfl
  simpa [nodeValue2372, Sparse.eval] using hc.symm

theorem sound2419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2419 node2419Labels = Sparse.eval nodeValue2419 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2419) = mixedMoment B node2419 node2419Labels := rfl
  simpa [nodeValue2419, Sparse.eval] using hc.symm

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

theorem sound2459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2459 node2459Labels = Sparse.eval nodeValue2459 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2459) = mixedMoment B node2459 node2459Labels := rfl
  simpa [nodeValue2459, Sparse.eval] using hc.symm

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

theorem sound2536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2536 node2536Labels = Sparse.eval nodeValue2536 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2536) = mixedMoment B node2536 node2536Labels := rfl
  simpa [nodeValue2536, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3335 node3335Labels = Sparse.eval nodeValue3335 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3335) = mixedMoment B node3335 node3335Labels := rfl
  simpa [nodeValue3335, Sparse.eval] using hc.symm

theorem sound3336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3336 node3336Labels = Sparse.eval nodeValue3336 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3336) = mixedMoment B node3336 node3336Labels := rfl
  simpa [nodeValue3336, Sparse.eval] using hc.symm

theorem sound3370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3370 node3370Labels = Sparse.eval nodeValue3370 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3370) = mixedMoment B node3370 node3370Labels := rfl
  simpa [nodeValue3370, Sparse.eval] using hc.symm

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

theorem sound3425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3425 node3425Labels = Sparse.eval nodeValue3425 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3425) = mixedMoment B node3425 node3425Labels := rfl
  simpa [nodeValue3425, Sparse.eval] using hc.symm

theorem sound3429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3429 node3429Labels = Sparse.eval nodeValue3429 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3429) = mixedMoment B node3429 node3429Labels := rfl
  simpa [nodeValue3429, Sparse.eval] using hc.symm

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

theorem sound3668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3668 node3668Labels = Sparse.eval nodeValue3668 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3668) = mixedMoment B node3668 node3668Labels := rfl
  simpa [nodeValue3668, Sparse.eval] using hc.symm

theorem sound3677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3677 node3677Labels = Sparse.eval nodeValue3677 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3677) = mixedMoment B node3677 node3677Labels := rfl
  simpa [nodeValue3677, Sparse.eval] using hc.symm

theorem sound3681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3681 node3681Labels = Sparse.eval nodeValue3681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3681) = mixedMoment B node3681 node3681Labels := rfl
  simpa [nodeValue3681, Sparse.eval] using hc.symm

theorem sound3683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3683 node3683Labels = Sparse.eval nodeValue3683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3683) = mixedMoment B node3683 node3683Labels := rfl
  simpa [nodeValue3683, Sparse.eval] using hc.symm

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

theorem sound3713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3713 node3713Labels = Sparse.eval nodeValue3713 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3713) = mixedMoment B node3713 node3713Labels := rfl
  simpa [nodeValue3713, Sparse.eval] using hc.symm

theorem sound3719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3719 node3719Labels = Sparse.eval nodeValue3719 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3719) = mixedMoment B node3719 node3719Labels := rfl
  simpa [nodeValue3719, Sparse.eval] using hc.symm

theorem sound3721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3721 node3721Labels = Sparse.eval nodeValue3721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3721) = mixedMoment B node3721 node3721Labels := rfl
  simpa [nodeValue3721, Sparse.eval] using hc.symm

theorem sound3746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3746 node3746Labels = Sparse.eval nodeValue3746 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3746) = mixedMoment B node3746 node3746Labels := rfl
  simpa [nodeValue3746, Sparse.eval] using hc.symm

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

theorem sound3776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3776 node3776Labels = Sparse.eval nodeValue3776 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3776) = mixedMoment B node3776 node3776Labels := rfl
  simpa [nodeValue3776, Sparse.eval] using hc.symm

theorem sound3778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3778 node3778Labels = Sparse.eval nodeValue3778 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3778) = mixedMoment B node3778 node3778Labels := rfl
  simpa [nodeValue3778, Sparse.eval] using hc.symm

theorem sound3779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3779 node3779Labels = Sparse.eval nodeValue3779 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3779) = mixedMoment B node3779 node3779Labels := rfl
  simpa [nodeValue3779, Sparse.eval] using hc.symm

theorem sound3795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3795 node3795Labels = Sparse.eval nodeValue3795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3795) = mixedMoment B node3795 node3795Labels := rfl
  simpa [nodeValue3795, Sparse.eval] using hc.symm

theorem sound3797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3797 node3797Labels = Sparse.eval nodeValue3797 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3797) = mixedMoment B node3797 node3797Labels := rfl
  simpa [nodeValue3797, Sparse.eval] using hc.symm

theorem sound3836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3836 node3836Labels = Sparse.eval nodeValue3836 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3836) = mixedMoment B node3836 node3836Labels := rfl
  simpa [nodeValue3836, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4088 node4088Labels = Sparse.eval nodeValue4088 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4088) = mixedMoment B node4088 node4088Labels := rfl
  simpa [nodeValue4088, Sparse.eval] using hc.symm

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

theorem sound4986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4986 node4986Labels = Sparse.eval nodeValue4986 (mixedVector B) := by
  have h := singleton4986 B _hB
  rw [sound2371 B _hB _hF, sound3335 B _hB _hF] at h
  norm_num [nodeValue4986, nodeValue2371, nodeValue3335, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4987 node4987Labels = Sparse.eval nodeValue4987 (mixedVector B) := by
  have h := singleton4987 B _hB
  rw [sound2372 B _hB _hF, sound3336 B _hB _hF] at h
  norm_num [nodeValue4987, nodeValue2372, nodeValue3336, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5017 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5017 node5017Labels = 0 := by
  exact mixedMoment_order_one B hB node5017 node5017Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5025 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5025 node5025Labels = 0 := by
  exact mixedMoment_order_one B hB node5025 node5025Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5017 node5017Labels = Sparse.eval nodeValue5017 (mixedVector B) := by
  simpa only [nodeValue5017, Sparse.eval_nil] using zero5017 B _hB _hF

theorem sound5025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5025 node5025Labels = Sparse.eval nodeValue5025 (mixedVector B) := by
  simpa only [nodeValue5025, Sparse.eval_nil] using zero5025 B _hB _hF

theorem sound5030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5030 node5030Labels = Sparse.eval nodeValue5030 (mixedVector B) := by
  have h := singleton5030 B _hB
  rw [sound2419 B _hB _hF, sound3425 B _hB _hF] at h
  norm_num [nodeValue5030, nodeValue2419, nodeValue3425, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5056 node5056Labels = Sparse.eval nodeValue5056 (mixedVector B) := by
  have h := singleton5056 B _hB
  rw [sound2459 B _hB _hF, sound3429 B _hB _hF] at h
  norm_num [nodeValue5056, nodeValue2459, nodeValue3429, Sparse.eval] at h ⊢
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

theorem sound5123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5123 node5123Labels = Sparse.eval nodeValue5123 (mixedVector B) := by
  have h := singleton5123 B _hB
  rw [sound2536 B _hB _hF, sound3370 B _hB _hF] at h
  norm_num [nodeValue5123, nodeValue2536, nodeValue3370, Sparse.eval] at h ⊢
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

theorem zero5314 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5314 node5314Labels = 0 := by
  exact mixedMoment_order_one B hB node5314 node5314Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5345 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5345 node5345Labels = 0 := by
  exact mixedMoment_order_one B hB node5345 node5345Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5367 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5367 node5367Labels = 0 := by
  exact mixedMoment_order_one B hB node5367 node5367Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5314 node5314Labels = Sparse.eval nodeValue5314 (mixedVector B) := by
  simpa only [nodeValue5314, Sparse.eval_nil] using zero5314 B _hB _hF

theorem sound5333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5333 node5333Labels = Sparse.eval nodeValue5333 (mixedVector B) := by
  have h := singleton5333 B _hB
  rw [sound3668 B _hB _hF, sound3677 B _hB _hF] at h
  norm_num [nodeValue5333, nodeValue3668, nodeValue3677, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5344 node5344Labels = Sparse.eval nodeValue5344 (mixedVector B) := by
  have h := singleton5344 B _hB
  rw [sound3681 B _hB _hF] at h
  norm_num [nodeValue5344, nodeValue3681, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5345 node5345Labels = Sparse.eval nodeValue5345 (mixedVector B) := by
  simpa only [nodeValue5345, Sparse.eval_nil] using zero5345 B _hB _hF

theorem sound5346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5346 node5346Labels = Sparse.eval nodeValue5346 (mixedVector B) := by
  have h := singleton5346 B _hB
  rw [sound3683 B _hB _hF, sound3746 B _hB _hF] at h
  norm_num [nodeValue5346, nodeValue3683, nodeValue3746, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5367 node5367Labels = Sparse.eval nodeValue5367 (mixedVector B) := by
  simpa only [nodeValue5367, Sparse.eval_nil] using zero5367 B _hB _hF

theorem sound5369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5369 node5369Labels = Sparse.eval nodeValue5369 (mixedVector B) := by
  simpa only [nodeValue5369, Sparse.eval_nil] using zero5369 B _hB _hF

theorem sound5374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5374 node5374Labels = Sparse.eval nodeValue5374 (mixedVector B) := by
  have h := singleton5374 B _hB
  rw [sound3713 B _hB _hF] at h
  norm_num [nodeValue5374, nodeValue3713, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5378 node5378Labels = Sparse.eval nodeValue5378 (mixedVector B) := by
  have h := singleton5378 B _hB
  rw [sound3719 B _hB _hF, sound3795 B _hB _hF] at h
  norm_num [nodeValue5378, nodeValue3719, nodeValue3795, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5380 node5380Labels = Sparse.eval nodeValue5380 (mixedVector B) := by
  have h := singleton5380 B _hB
  rw [sound3721 B _hB _hF, sound3836 B _hB _hF] at h
  norm_num [nodeValue5380, nodeValue3721, nodeValue3836, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5391 node5391Labels = Sparse.eval nodeValue5391 (mixedVector B) := by
  have h := singleton5391 B _hB
  rw [sound3776 B _hB _hF, sound3778 B _hB _hF] at h
  norm_num [nodeValue5391, nodeValue3776, nodeValue3778, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5393 node5393Labels = Sparse.eval nodeValue5393 (mixedVector B) := by
  have h := singleton5393 B _hB
  rw [sound3779 B _hB _hF, sound3797 B _hB _hF] at h
  norm_num [nodeValue5393, nodeValue3779, nodeValue3797, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5460 node5460Labels = Sparse.eval nodeValue5460 (mixedVector B) := by
  simpa only [nodeValue5460, Sparse.eval_nil] using zero5460 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources82
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2633 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2633 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2633 + difference 0 1) (sourceB2633 + difference 1 0) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA2633 + difference 0 1) (sourceB2633 + difference 1 0) sourceC2633) = raw36888 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36888; decide +kernel
    rw [ha]
    exact (canonical36888 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2633 + difference 0 2) (sourceB2633 + difference 2 0) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5374) := by
    have ha : (tripleCharges (sourceA2633 + difference 0 2) (sourceB2633 + difference 2 0) sourceC2633) = raw36889 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36889; decide +kernel
    rw [ha]
    exact (canonical36889 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2633 + difference 0 3) (sourceB2633 + difference 3 0) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2633 + difference 0 3) (sourceB2633 + difference 3 0) sourceC2633) = raw36890 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36890; decide +kernel
    rw [ha]
    exact (canonical36890 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2633 + difference 0 4) (sourceB2633 + difference 4 0) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2633 + difference 0 4) (sourceB2633 + difference 4 0) sourceC2633) = raw36355 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36355; decide +kernel
    rw [ha]
    exact (canonical36355 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2633 + difference 0 5) (sourceB2633 + difference 5 0) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA2633 + difference 0 5) (sourceB2633 + difference 5 0) sourceC2633) = raw36891 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36891; decide +kernel
    rw [ha]
    exact (canonical36891 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2633 + difference 1 0) (sourceB2633 + difference 0 1) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5345) := by
    have ha : (tripleCharges (sourceA2633 + difference 1 0) (sourceB2633 + difference 0 1) sourceC2633) = raw36371 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36371; decide +kernel
    rw [ha]
    exact (canonical36371 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2633 + difference 1 2) (sourceB2633 + difference 2 1) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5391) := by
    have ha : (tripleCharges (sourceA2633 + difference 1 2) (sourceB2633 + difference 2 1) sourceC2633) = raw36373 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36373; decide +kernel
    rw [ha]
    exact (canonical36373 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2633 + difference 1 3) (sourceB2633 + difference 3 1) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2633 + difference 1 3) (sourceB2633 + difference 3 1) sourceC2633) = raw36374 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36374; decide +kernel
    rw [ha]
    exact (canonical36374 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2633 + difference 1 4) (sourceB2633 + difference 4 1) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2633 + difference 1 4) (sourceB2633 + difference 4 1) sourceC2633) = raw36892 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36892; decide +kernel
    rw [ha]
    exact (canonical36892 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2633 + difference 1 5) (sourceB2633 + difference 5 1) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5460) := by
    have ha : (tripleCharges (sourceA2633 + difference 1 5) (sourceB2633 + difference 5 1) sourceC2633) = raw36375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36375; decide +kernel
    rw [ha]
    exact (canonical36375 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2633 + difference 2 0) (sourceB2633 + difference 0 2) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2633 + difference 2 0) (sourceB2633 + difference 0 2) sourceC2633) = raw36893 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36893; decide +kernel
    rw [ha]
    exact (canonical36893 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2633 + difference 2 1) (sourceB2633 + difference 1 2) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5017) := by
    have ha : (tripleCharges (sourceA2633 + difference 2 1) (sourceB2633 + difference 1 2) sourceC2633) = raw36894 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36894; decide +kernel
    rw [ha]
    exact (canonical36894 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2633 + difference 2 3) (sourceB2633 + difference 3 2) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2633 + difference 2 3) (sourceB2633 + difference 3 2) sourceC2633) = raw36895 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36895; decide +kernel
    rw [ha]
    exact (canonical36895 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2633 + difference 2 4) (sourceB2633 + difference 4 2) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2633 + difference 2 4) (sourceB2633 + difference 4 2) sourceC2633) = raw36363 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36363; decide +kernel
    rw [ha]
    exact (canonical36363 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2633 + difference 2 5) (sourceB2633 + difference 5 2) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5369) := by
    have ha : (tripleCharges (sourceA2633 + difference 2 5) (sourceB2633 + difference 5 2) sourceC2633) = raw36523 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36523; decide +kernel
    rw [ha]
    exact (canonical36523 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2633 + difference 3 0) (sourceB2633 + difference 0 3) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5314) := by
    have ha : (tripleCharges (sourceA2633 + difference 3 0) (sourceB2633 + difference 0 3) sourceC2633) = raw36896 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36896; decide +kernel
    rw [ha]
    exact (canonical36896 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2633 + difference 3 1) (sourceB2633 + difference 1 3) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4987) := by
    have ha : (tripleCharges (sourceA2633 + difference 3 1) (sourceB2633 + difference 1 3) sourceC2633) = raw36897 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36897; decide +kernel
    rw [ha]
    exact (canonical36897 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2633 + difference 3 2) (sourceB2633 + difference 2 3) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5333) := by
    have ha : (tripleCharges (sourceA2633 + difference 3 2) (sourceB2633 + difference 2 3) sourceC2633) = raw36898 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36898; decide +kernel
    rw [ha]
    exact (canonical36898 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2633 + difference 3 4) (sourceB2633 + difference 4 3) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5344) := by
    have ha : (tripleCharges (sourceA2633 + difference 3 4) (sourceB2633 + difference 4 3) sourceC2633) = raw36367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36367; decide +kernel
    rw [ha]
    exact (canonical36367 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2633 + difference 3 5) (sourceB2633 + difference 5 3) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA2633 + difference 3 5) (sourceB2633 + difference 5 3) sourceC2633) = raw36899 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36899; decide +kernel
    rw [ha]
    exact (canonical36899 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2633 + difference 4 0) (sourceB2633 + difference 0 4) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5314) := by
    have ha : (tripleCharges (sourceA2633 + difference 4 0) (sourceB2633 + difference 0 4) sourceC2633) = raw36900 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36900; decide +kernel
    rw [ha]
    exact (canonical36900 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2633 + difference 4 1) (sourceB2633 + difference 1 4) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4987) := by
    have ha : (tripleCharges (sourceA2633 + difference 4 1) (sourceB2633 + difference 1 4) sourceC2633) = raw36901 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36901; decide +kernel
    rw [ha]
    exact (canonical36901 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2633 + difference 4 2) (sourceB2633 + difference 2 4) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5333) := by
    have ha : (tripleCharges (sourceA2633 + difference 4 2) (sourceB2633 + difference 2 4) sourceC2633) = raw36902 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36902; decide +kernel
    rw [ha]
    exact (canonical36902 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2633 + difference 4 3) (sourceB2633 + difference 3 4) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5344) := by
    have ha : (tripleCharges (sourceA2633 + difference 4 3) (sourceB2633 + difference 3 4) sourceC2633) = raw36903 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36903; decide +kernel
    rw [ha]
    exact (canonical36903 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2633 + difference 4 5) (sourceB2633 + difference 5 4) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA2633 + difference 4 5) (sourceB2633 + difference 5 4) sourceC2633) = raw36904 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36904; decide +kernel
    rw [ha]
    exact (canonical36904 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2633 + difference 5 0) (sourceB2633 + difference 0 5) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5025) := by
    have ha : (tripleCharges (sourceA2633 + difference 5 0) (sourceB2633 + difference 0 5) sourceC2633) = raw36905 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36905; decide +kernel
    rw [ha]
    exact (canonical36905 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2633 + difference 5 1) (sourceB2633 + difference 1 5) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4986) := by
    have ha : (tripleCharges (sourceA2633 + difference 5 1) (sourceB2633 + difference 1 5) sourceC2633) = raw36906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36906; decide +kernel
    rw [ha]
    exact (canonical36906 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2633 + difference 5 2) (sourceB2633 + difference 2 5) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5030) := by
    have ha : (tripleCharges (sourceA2633 + difference 5 2) (sourceB2633 + difference 2 5) sourceC2633) = raw36907 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36907; decide +kernel
    rw [ha]
    exact (canonical36907 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2633 + difference 5 3) (sourceB2633 + difference 3 5) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA2633 + difference 5 3) (sourceB2633 + difference 3 5) sourceC2633) = raw36908 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36908; decide +kernel
    rw [ha]
    exact (canonical36908 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2633 + difference 5 4) (sourceB2633 + difference 4 5) sourceC2633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA2633 + difference 5 4) (sourceB2633 + difference 4 5) sourceC2633) = raw36377 := by
      apply Matrix.ext; unfold tripleCharges sourceA2633 sourceB2633 sourceC2633 difference raw36377; decide +kernel
    rw [ha]
    exact (canonical36377 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2633 sourceB2633 sourceC2633
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2633, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2097 : Integer.Sparse.reindex keyMap MixedData.row2097 = numericRow2097 := by decide +kernel

theorem numericCheck2097 (x : Master → ℝ) : Integer.Sparse.eval numericRow2097 x =
    (4 : ℝ) * reducedSource2097 x := by
  norm_num [numericRow2097, reducedSource2097, Integer.Sparse.eval, Sparse.eval, nodeValue4088, nodeValue4986, nodeValue4987, nodeValue5017, nodeValue5025, nodeValue5030, nodeValue5056, nodeValue5123, nodeValue5314, nodeValue5333, nodeValue5344, nodeValue5345, nodeValue5346, nodeValue5367, nodeValue5369, nodeValue5374, nodeValue5378, nodeValue5380, nodeValue5391, nodeValue5393, nodeValue5460] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2097 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2097 (mixedVector B) = 0 := by
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  have h4986 : mixedVector B (Sum.inr 4986) = Sparse.eval nodeValue4986 (mixedVector B) := by
    change mixedMoment B node4986 node4986Labels = _
    exact sound4986 B hB hF
  have h4987 : mixedVector B (Sum.inr 4987) = Sparse.eval nodeValue4987 (mixedVector B) := by
    change mixedMoment B node4987 node4987Labels = _
    exact sound4987 B hB hF
  have h5017 : mixedVector B (Sum.inr 5017) = Sparse.eval nodeValue5017 (mixedVector B) := by
    change mixedMoment B node5017 node5017Labels = _
    exact sound5017 B hB hF
  have h5025 : mixedVector B (Sum.inr 5025) = Sparse.eval nodeValue5025 (mixedVector B) := by
    change mixedMoment B node5025 node5025Labels = _
    exact sound5025 B hB hF
  have h5030 : mixedVector B (Sum.inr 5030) = Sparse.eval nodeValue5030 (mixedVector B) := by
    change mixedMoment B node5030 node5030Labels = _
    exact sound5030 B hB hF
  have h5056 : mixedVector B (Sum.inr 5056) = Sparse.eval nodeValue5056 (mixedVector B) := by
    change mixedMoment B node5056 node5056Labels = _
    exact sound5056 B hB hF
  have h5123 : mixedVector B (Sum.inr 5123) = Sparse.eval nodeValue5123 (mixedVector B) := by
    change mixedMoment B node5123 node5123Labels = _
    exact sound5123 B hB hF
  have h5314 : mixedVector B (Sum.inr 5314) = Sparse.eval nodeValue5314 (mixedVector B) := by
    change mixedMoment B node5314 node5314Labels = _
    exact sound5314 B hB hF
  have h5333 : mixedVector B (Sum.inr 5333) = Sparse.eval nodeValue5333 (mixedVector B) := by
    change mixedMoment B node5333 node5333Labels = _
    exact sound5333 B hB hF
  have h5344 : mixedVector B (Sum.inr 5344) = Sparse.eval nodeValue5344 (mixedVector B) := by
    change mixedMoment B node5344 node5344Labels = _
    exact sound5344 B hB hF
  have h5345 : mixedVector B (Sum.inr 5345) = Sparse.eval nodeValue5345 (mixedVector B) := by
    change mixedMoment B node5345 node5345Labels = _
    exact sound5345 B hB hF
  have h5346 : mixedVector B (Sum.inr 5346) = Sparse.eval nodeValue5346 (mixedVector B) := by
    change mixedMoment B node5346 node5346Labels = _
    exact sound5346 B hB hF
  have h5367 : mixedVector B (Sum.inr 5367) = Sparse.eval nodeValue5367 (mixedVector B) := by
    change mixedMoment B node5367 node5367Labels = _
    exact sound5367 B hB hF
  have h5369 : mixedVector B (Sum.inr 5369) = Sparse.eval nodeValue5369 (mixedVector B) := by
    change mixedMoment B node5369 node5369Labels = _
    exact sound5369 B hB hF
  have h5374 : mixedVector B (Sum.inr 5374) = Sparse.eval nodeValue5374 (mixedVector B) := by
    change mixedMoment B node5374 node5374Labels = _
    exact sound5374 B hB hF
  have h5378 : mixedVector B (Sum.inr 5378) = Sparse.eval nodeValue5378 (mixedVector B) := by
    change mixedMoment B node5378 node5378Labels = _
    exact sound5378 B hB hF
  have h5380 : mixedVector B (Sum.inr 5380) = Sparse.eval nodeValue5380 (mixedVector B) := by
    change mixedMoment B node5380 node5380Labels = _
    exact sound5380 B hB hF
  have h5391 : mixedVector B (Sum.inr 5391) = Sparse.eval nodeValue5391 (mixedVector B) := by
    change mixedMoment B node5391 node5391Labels = _
    exact sound5391 B hB hF
  have h5393 : mixedVector B (Sum.inr 5393) = Sparse.eval nodeValue5393 (mixedVector B) := by
    change mixedMoment B node5393 node5393Labels = _
    exact sound5393 B hB hF
  have h5460 : mixedVector B (Sum.inr 5460) = Sparse.eval nodeValue5460 (mixedVector B) := by
    change mixedMoment B node5460 node5460Labels = _
    exact sound5460 B hB hF
  simpa only [sourceForm2633, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4088, h4986, h4987, h5017, h5025, h5030, h5056, h5123, h5314, h5333, h5344, h5345, h5346, h5367, h5369, h5374, h5378, h5380, h5391, h5393, h5460, reducedSource2097] using sourceEq2633 B hB

theorem rowSound2097_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2097 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2097, numericCheck2097, reducedZero2097 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2097_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2097_e_oai
