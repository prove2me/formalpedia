-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:20:10.724014+00:00
-- url     : https://prove2.me/submissions/6b647be9-6fa0-4157-9b88-bc3d44a844fc

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E106
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1953 raw1953Labels = mixedMoment B node4971 node4971Labels := by
  calc
    mixedMoment B raw1953 raw1953Labels = mixedMoment B raw1953step0 raw1953step0Labels := by
      have ha : raw1953step0 = (fun i j => raw1953 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1953step0 raw1953; decide +kernel
      have hl : raw1953step0Labels = raw1953Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1953 raw1953Labels permutation152 permutation5
    mixedMoment B raw1953step0 raw1953step0Labels = mixedMoment B raw1953step1 raw1953step1Labels := by
      have ha : raw1953step1 = raw1953step0 := by apply Matrix.ext; unfold raw1953step1 raw1953step0; decide +kernel
      have hl : raw1953step0Labels = labelEmbedding8 ∘ raw1953step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1953step0 raw1953step0Labels raw1953step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4971 node4971Labels := by rfl

theorem canonical1954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1954 raw1954Labels = mixedMoment B node2807 node2807Labels := by
  calc
    mixedMoment B raw1954 raw1954Labels = mixedMoment B raw1954step0 raw1954step0Labels := by
      have ha : raw1954step0 = (fun i j => raw1954 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1954step0 raw1954; decide +kernel
      have hl : raw1954step0Labels = raw1954Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1954 raw1954Labels permutation160 permutation4
    _ = mixedMoment B node2807 node2807Labels := by rfl

theorem canonical1955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1955 raw1955Labels = mixedMoment B node3590 node3590Labels := by
  calc
    mixedMoment B raw1955 raw1955Labels = mixedMoment B raw1955step0 raw1955step0Labels := by
      have ha : raw1955step0 = (fun i j => raw1955 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1955step0 raw1955; decide +kernel
      have hl : raw1955step0Labels = raw1955Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1955 raw1955Labels permutation156 permutation3
    mixedMoment B raw1955step0 raw1955step0Labels = mixedMoment B raw1955step1 raw1955step1Labels := by
      have ha : raw1955step1 = -raw1955step0 := by apply Matrix.ext; change ∀ i j, raw1955step1 i j = -(raw1955step0 i j); unfold raw1955step1 raw1955step0; decide +kernel
      have hl : raw1955step1Labels = raw1955step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1955step1 raw1955step1Labels = mixedMoment B raw1955step2 raw1955step2Labels := by
      have ha : raw1955step2 = raw1955step1 := by apply Matrix.ext; unfold raw1955step2 raw1955step1; decide +kernel
      have hl : raw1955step1Labels = labelEmbedding1 ∘ raw1955step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1955step1 raw1955step1Labels raw1955step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3590 node3590Labels := by rfl

theorem canonical1956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1956 raw1956Labels = mixedMoment B node4972 node4972Labels := by
  calc
    mixedMoment B raw1956 raw1956Labels = mixedMoment B raw1956step0 raw1956step0Labels := by
      have ha : raw1956step0 = (fun i j => raw1956 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1956step0 raw1956; decide +kernel
      have hl : raw1956step0Labels = raw1956Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1956 raw1956Labels permutation32 permutation5
    mixedMoment B raw1956step0 raw1956step0Labels = mixedMoment B raw1956step1 raw1956step1Labels := by
      have ha : raw1956step1 = raw1956step0 := by apply Matrix.ext; unfold raw1956step1 raw1956step0; decide +kernel
      have hl : raw1956step0Labels = labelEmbedding8 ∘ raw1956step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1956step0 raw1956step0Labels raw1956step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4972 node4972Labels := by rfl

theorem canonical1957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1957 raw1957Labels = mixedMoment B node2434 node2434Labels := by
  calc
    mixedMoment B raw1957 raw1957Labels = mixedMoment B raw1957step0 raw1957step0Labels := by
      have ha : raw1957step0 = (fun i j => raw1957 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1957step0 raw1957; decide +kernel
      have hl : raw1957step0Labels = raw1957Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1957 raw1957Labels permutation145 permutation4
    mixedMoment B raw1957step0 raw1957step0Labels = mixedMoment B raw1957step1 raw1957step1Labels := by
      have ha : raw1957step1 = -raw1957step0 := by apply Matrix.ext; change ∀ i j, raw1957step1 i j = -(raw1957step0 i j); unfold raw1957step1 raw1957step0; decide +kernel
      have hl : raw1957step1Labels = raw1957step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2434 node2434Labels := by rfl

theorem canonical1958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1958 raw1958Labels = mixedMoment B node3457 node3457Labels := by
  calc
    mixedMoment B raw1958 raw1958Labels = mixedMoment B raw1958step0 raw1958step0Labels := by
      have ha : raw1958step0 = (fun i j => raw1958 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1958step0 raw1958; decide +kernel
      have hl : raw1958step0Labels = raw1958Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1958 raw1958Labels permutation144 permutation6
    mixedMoment B raw1958step0 raw1958step0Labels = mixedMoment B raw1958step1 raw1958step1Labels := by
      have ha : raw1958step1 = raw1958step0 := by apply Matrix.ext; unfold raw1958step1 raw1958step0; decide +kernel
      have hl : raw1958step0Labels = labelEmbedding1 ∘ raw1958step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1958step0 raw1958step0Labels raw1958step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3457 node3457Labels := by rfl

theorem canonical1959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1959 raw1959Labels = mixedMoment B node4973 node4973Labels := by
  calc
    mixedMoment B raw1959 raw1959Labels = mixedMoment B raw1959step0 raw1959step0Labels := by
      have ha : raw1959step0 = (fun i j => raw1959 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1959step0 raw1959; decide +kernel
      have hl : raw1959step0Labels = raw1959Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1959 raw1959Labels permutation32 permutation5
    mixedMoment B raw1959step0 raw1959step0Labels = mixedMoment B raw1959step1 raw1959step1Labels := by
      have ha : raw1959step1 = raw1959step0 := by apply Matrix.ext; unfold raw1959step1 raw1959step0; decide +kernel
      have hl : raw1959step0Labels = labelEmbedding8 ∘ raw1959step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1959step0 raw1959step0Labels raw1959step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4973 node4973Labels := by rfl

theorem canonical1960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1960 raw1960Labels = mixedMoment B node2817 node2817Labels := by
  calc
    mixedMoment B raw1960 raw1960Labels = mixedMoment B raw1960step0 raw1960step0Labels := by
      have ha : raw1960step0 = (fun i j => raw1960 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1960step0 raw1960; decide +kernel
      have hl : raw1960step0Labels = raw1960Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1960 raw1960Labels permutation33 permutation4
    _ = mixedMoment B node2817 node2817Labels := by rfl

theorem canonical1961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1961 raw1961Labels = mixedMoment B node3591 node3591Labels := by
  calc
    mixedMoment B raw1961 raw1961Labels = mixedMoment B raw1961step0 raw1961step0Labels := by
      have ha : raw1961step0 = (fun i j => raw1961 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1961step0 raw1961; decide +kernel
      have hl : raw1961step0Labels = raw1961Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1961 raw1961Labels permutation32 permutation3
    mixedMoment B raw1961step0 raw1961step0Labels = mixedMoment B raw1961step1 raw1961step1Labels := by
      have ha : raw1961step1 = -raw1961step0 := by apply Matrix.ext; change ∀ i j, raw1961step1 i j = -(raw1961step0 i j); unfold raw1961step1 raw1961step0; decide +kernel
      have hl : raw1961step1Labels = raw1961step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1961step1 raw1961step1Labels = mixedMoment B raw1961step2 raw1961step2Labels := by
      have ha : raw1961step2 = raw1961step1 := by apply Matrix.ext; unfold raw1961step2 raw1961step1; decide +kernel
      have hl : raw1961step1Labels = labelEmbedding1 ∘ raw1961step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1961step1 raw1961step1Labels raw1961step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3591 node3591Labels := by rfl

theorem canonical1965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1965 raw1965Labels = mixedMoment B node4977 node4977Labels := by
  calc
    mixedMoment B raw1965 raw1965Labels = mixedMoment B raw1965step0 raw1965step0Labels := by
      have ha : raw1965step0 = (fun i j => raw1965 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1965step0 raw1965; decide +kernel
      have hl : raw1965step0Labels = raw1965Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1965 raw1965Labels permutation32 permutation5
    mixedMoment B raw1965step0 raw1965step0Labels = mixedMoment B raw1965step1 raw1965step1Labels := by
      have ha : raw1965step1 = raw1965step0 := by apply Matrix.ext; unfold raw1965step1 raw1965step0; decide +kernel
      have hl : raw1965step0Labels = labelEmbedding8 ∘ raw1965step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1965step0 raw1965step0Labels raw1965step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4977 node4977Labels := by rfl

theorem canonical1966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1966 raw1966Labels = mixedMoment B node2813 node2813Labels := by
  calc
    mixedMoment B raw1966 raw1966Labels = mixedMoment B raw1966step0 raw1966step0Labels := by
      have ha : raw1966step0 = (fun i j => raw1966 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1966step0 raw1966; decide +kernel
      have hl : raw1966step0Labels = raw1966Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1966 raw1966Labels permutation33 permutation4
    _ = mixedMoment B node2813 node2813Labels := by rfl

theorem canonical1967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1967 raw1967Labels = mixedMoment B node3595 node3595Labels := by
  calc
    mixedMoment B raw1967 raw1967Labels = mixedMoment B raw1967step0 raw1967step0Labels := by
      have ha : raw1967step0 = (fun i j => raw1967 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1967step0 raw1967; decide +kernel
      have hl : raw1967step0Labels = raw1967Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1967 raw1967Labels permutation34 permutation3
    mixedMoment B raw1967step0 raw1967step0Labels = mixedMoment B raw1967step1 raw1967step1Labels := by
      have ha : raw1967step1 = -raw1967step0 := by apply Matrix.ext; change ∀ i j, raw1967step1 i j = -(raw1967step0 i j); unfold raw1967step1 raw1967step0; decide +kernel
      have hl : raw1967step1Labels = raw1967step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1967step1 raw1967step1Labels = mixedMoment B raw1967step2 raw1967step2Labels := by
      have ha : raw1967step2 = raw1967step1 := by apply Matrix.ext; unfold raw1967step2 raw1967step1; decide +kernel
      have hl : raw1967step1Labels = labelEmbedding1 ∘ raw1967step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1967step1 raw1967step1Labels raw1967step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3595 node3595Labels := by rfl

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

theorem canonical2133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2133 raw2133Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw2133 raw2133Labels = mixedMoment B raw2133step0 raw2133step0Labels := by
      have ha : raw2133step0 = (fun i j => raw2133 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2133step0 raw2133; decide +kernel
      have hl : raw2133step0Labels = raw2133Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2133 raw2133Labels permutation8 permutation4
    mixedMoment B raw2133step0 raw2133step0Labels = mixedMoment B raw2133step1 raw2133step1Labels := by
      have ha : raw2133step1 = raw2133step0 := by apply Matrix.ext; unfold raw2133step1 raw2133step0; decide +kernel
      have hl : raw2133step0Labels = labelEmbedding7 ∘ raw2133step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2133step0 raw2133step0Labels raw2133step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5109 node5109Labels := by rfl

theorem canonical2134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2134 raw2134Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw2134 raw2134Labels = mixedMoment B raw2134step0 raw2134step0Labels := by
      have ha : raw2134step0 = (fun i j => raw2134 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2134step0 raw2134; decide +kernel
      have hl : raw2134step0Labels = raw2134Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2134 raw2134Labels permutation8 permutation4
    _ = mixedMoment B node2519 node2519Labels := by rfl

theorem canonical2135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2135 raw2135Labels = mixedMoment B node3486 node3486Labels := by
  calc
    mixedMoment B raw2135 raw2135Labels = mixedMoment B raw2135step0 raw2135step0Labels := by
      have ha : raw2135step0 = (fun i j => raw2135 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2135step0 raw2135; decide +kernel
      have hl : raw2135step0Labels = raw2135Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2135 raw2135Labels permutation9 permutation6
    mixedMoment B raw2135step0 raw2135step0Labels = mixedMoment B raw2135step1 raw2135step1Labels := by
      have ha : raw2135step1 = -raw2135step0 := by apply Matrix.ext; change ∀ i j, raw2135step1 i j = -(raw2135step0 i j); unfold raw2135step1 raw2135step0; decide +kernel
      have hl : raw2135step1Labels = raw2135step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2135step1 raw2135step1Labels = mixedMoment B raw2135step2 raw2135step2Labels := by
      have ha : raw2135step2 = raw2135step1 := by apply Matrix.ext; unfold raw2135step2 raw2135step1; decide +kernel
      have hl : raw2135step1Labels = labelEmbedding1 ∘ raw2135step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2135step1 raw2135step1Labels raw2135step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3486 node3486Labels := by rfl

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

theorem canonical2232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2232 raw2232Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw2232 raw2232Labels = mixedMoment B raw2232step0 raw2232step0Labels := by
      have ha : raw2232step0 = (fun i j => raw2232 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2232step0 raw2232; decide +kernel
      have hl : raw2232step0Labels = raw2232Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2232 raw2232Labels permutation32 permutation5
    mixedMoment B raw2232step0 raw2232step0Labels = mixedMoment B raw2232step1 raw2232step1Labels := by
      have ha : raw2232step1 = raw2232step0 := by apply Matrix.ext; unfold raw2232step1 raw2232step0; decide +kernel
      have hl : raw2232step0Labels = labelEmbedding8 ∘ raw2232step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2232step0 raw2232step0Labels raw2232step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

theorem canonical2233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2233 raw2233Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw2233 raw2233Labels = mixedMoment B raw2233step0 raw2233step0Labels := by
      have ha : raw2233step0 = (fun i j => raw2233 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2233step0 raw2233; decide +kernel
      have hl : raw2233step0Labels = raw2233Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2233 raw2233Labels permutation34 permutation4
    _ = mixedMoment B node2881 node2881Labels := by rfl

theorem canonical2234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2234 raw2234Labels = mixedMoment B node3624 node3624Labels := by
  calc
    mixedMoment B raw2234 raw2234Labels = mixedMoment B raw2234step0 raw2234step0Labels := by
      have ha : raw2234step0 = (fun i j => raw2234 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2234step0 raw2234; decide +kernel
      have hl : raw2234step0Labels = raw2234Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2234 raw2234Labels permutation42 permutation3
    mixedMoment B raw2234step0 raw2234step0Labels = mixedMoment B raw2234step1 raw2234step1Labels := by
      have ha : raw2234step1 = -raw2234step0 := by apply Matrix.ext; change ∀ i j, raw2234step1 i j = -(raw2234step0 i j); unfold raw2234step1 raw2234step0; decide +kernel
      have hl : raw2234step1Labels = raw2234step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2234step1 raw2234step1Labels = mixedMoment B raw2234step2 raw2234step2Labels := by
      have ha : raw2234step2 = raw2234step1 := by apply Matrix.ext; unfold raw2234step2 raw2234step1; decide +kernel
      have hl : raw2234step1Labels = labelEmbedding1 ∘ raw2234step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2234step1 raw2234step1Labels raw2234step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3624 node3624Labels := by rfl

theorem canonical2235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2235 raw2235Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw2235 raw2235Labels = mixedMoment B raw2235step0 raw2235step0Labels := by
      have ha : raw2235step0 = (fun i j => raw2235 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2235step0 raw2235; decide +kernel
      have hl : raw2235step0Labels = raw2235Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2235 raw2235Labels permutation8 permutation5
    mixedMoment B raw2235step0 raw2235step0Labels = mixedMoment B raw2235step1 raw2235step1Labels := by
      have ha : raw2235step1 = raw2235step0 := by apply Matrix.ext; unfold raw2235step1 raw2235step0; decide +kernel
      have hl : raw2235step0Labels = labelEmbedding8 ∘ raw2235step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2235step0 raw2235step0Labels raw2235step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5207 node5207Labels := by rfl

theorem canonical2236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2236 raw2236Labels = mixedMoment B node2889 node2889Labels := by
  calc
    mixedMoment B raw2236 raw2236Labels = mixedMoment B raw2236step0 raw2236step0Labels := by
      have ha : raw2236step0 = (fun i j => raw2236 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2236step0 raw2236; decide +kernel
      have hl : raw2236step0Labels = raw2236Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2236 raw2236Labels permutation9 permutation4
    _ = mixedMoment B node2889 node2889Labels := by rfl

theorem canonical2237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2237 raw2237Labels = mixedMoment B node3631 node3631Labels := by
  calc
    mixedMoment B raw2237 raw2237Labels = mixedMoment B raw2237step0 raw2237step0Labels := by
      have ha : raw2237step0 = (fun i j => raw2237 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2237step0 raw2237; decide +kernel
      have hl : raw2237step0Labels = raw2237Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2237 raw2237Labels permutation10 permutation3
    mixedMoment B raw2237step0 raw2237step0Labels = mixedMoment B raw2237step1 raw2237step1Labels := by
      have ha : raw2237step1 = -raw2237step0 := by apply Matrix.ext; change ∀ i j, raw2237step1 i j = -(raw2237step0 i j); unfold raw2237step1 raw2237step0; decide +kernel
      have hl : raw2237step1Labels = raw2237step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2237step1 raw2237step1Labels = mixedMoment B raw2237step2 raw2237step2Labels := by
      have ha : raw2237step2 = raw2237step1 := by apply Matrix.ext; unfold raw2237step2 raw2237step1; decide +kernel
      have hl : raw2237step1Labels = labelEmbedding1 ∘ raw2237step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2237step1 raw2237step1Labels raw2237step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3631 node3631Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2463 raw2463Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw2463 raw2463Labels = mixedMoment B raw2463step0 raw2463step0Labels := by
      have ha : raw2463step0 = (fun i j => raw2463 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2463step0 raw2463; decide +kernel
      have hl : raw2463step0Labels = raw2463Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2463 raw2463Labels permutation152 permutation4
    mixedMoment B raw2463step0 raw2463step0Labels = mixedMoment B raw2463step1 raw2463step1Labels := by
      have ha : raw2463step1 = raw2463step0 := by apply Matrix.ext; unfold raw2463step1 raw2463step0; decide +kernel
      have hl : raw2463step0Labels = labelEmbedding7 ∘ raw2463step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2463step0 raw2463step0Labels raw2463step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

theorem canonical2464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2464 raw2464Labels = mixedMoment B node3781 node3781Labels := by
  calc
    mixedMoment B raw2464 raw2464Labels = mixedMoment B raw2464step0 raw2464step0Labels := by
      have ha : raw2464step0 = (fun i j => raw2464 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2464step0 raw2464; decide +kernel
      have hl : raw2464step0Labels = raw2464Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2464 raw2464Labels permutation152 permutation4
    _ = mixedMoment B node3781 node3781Labels := by rfl

theorem canonical2465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2465 raw2465Labels = mixedMoment B node3794 node3794Labels := by
  calc
    mixedMoment B raw2465 raw2465Labels = mixedMoment B raw2465step0 raw2465step0Labels := by
      have ha : raw2465step0 = (fun i j => raw2465 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2465step0 raw2465; decide +kernel
      have hl : raw2465step0Labels = raw2465Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2465 raw2465Labels permutation153 permutation6
    mixedMoment B raw2465step0 raw2465step0Labels = mixedMoment B raw2465step1 raw2465step1Labels := by
      have ha : raw2465step1 = -raw2465step0 := by apply Matrix.ext; change ∀ i j, raw2465step1 i j = -(raw2465step0 i j); unfold raw2465step1 raw2465step0; decide +kernel
      have hl : raw2465step1Labels = raw2465step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2465step1 raw2465step1Labels = mixedMoment B raw2465step2 raw2465step2Labels := by
      have ha : raw2465step2 = raw2465step1 := by apply Matrix.ext; unfold raw2465step2 raw2465step1; decide +kernel
      have hl : raw2465step1Labels = labelEmbedding1 ∘ raw2465step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2465step1 raw2465step1Labels raw2465step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3794 node3794Labels := by rfl

theorem canonical2517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2517 raw2517Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw2517 raw2517Labels = mixedMoment B raw2517step0 raw2517step0Labels := by
      have ha : raw2517step0 = (fun i j => raw2517 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2517step0 raw2517; decide +kernel
      have hl : raw2517step0Labels = raw2517Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2517 raw2517Labels permutation32 permutation4
    mixedMoment B raw2517step0 raw2517step0Labels = mixedMoment B raw2517step1 raw2517step1Labels := by
      have ha : raw2517step1 = raw2517step0 := by apply Matrix.ext; unfold raw2517step1 raw2517step0; decide +kernel
      have hl : raw2517step0Labels = labelEmbedding7 ∘ raw2517step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2517step0 raw2517step0Labels raw2517step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

theorem canonical2518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2518 raw2518Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw2518 raw2518Labels = mixedMoment B raw2518step0 raw2518step0Labels := by
      have ha : raw2518step0 = (fun i j => raw2518 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2518step0 raw2518; decide +kernel
      have hl : raw2518step0Labels = raw2518Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2518 raw2518Labels permutation32 permutation4
    _ = mixedMoment B node3845 node3845Labels := by rfl

theorem canonical2519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2519 raw2519Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw2519 raw2519Labels = mixedMoment B raw2519step0 raw2519step0Labels := by
      have ha : raw2519step0 = (fun i j => raw2519 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2519step0 raw2519; decide +kernel
      have hl : raw2519step0Labels = raw2519Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2519 raw2519Labels permutation39 permutation6
    mixedMoment B raw2519step0 raw2519step0Labels = mixedMoment B raw2519step1 raw2519step1Labels := by
      have ha : raw2519step1 = -raw2519step0 := by apply Matrix.ext; change ∀ i j, raw2519step1 i j = -(raw2519step0 i j); unfold raw2519step1 raw2519step0; decide +kernel
      have hl : raw2519step1Labels = raw2519step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2519step1 raw2519step1Labels = mixedMoment B raw2519step2 raw2519step2Labels := by
      have ha : raw2519step2 = raw2519step1 := by apply Matrix.ext; unfold raw2519step2 raw2519step1; decide +kernel
      have hl : raw2519step1Labels = labelEmbedding1 ∘ raw2519step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2519step1 raw2519step1Labels raw2519step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3845 node3845Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical255
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32669 raw32669Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw32669 raw32669Labels = mixedMoment B raw32669step0 raw32669step0Labels := by
      have hz : ∀ j, raw32669 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32669step0 = (fun i j => raw32669 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32669step0 raw32669; decide +kernel
      have hl : raw32669step0Labels = raw32669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32669 raw32669Labels permutation346 hz
    mixedMoment B raw32669step0 raw32669step0Labels = mixedMoment B raw32669step1 raw32669step1Labels := by
      have ha : raw32669step1 = (fun i j => raw32669step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32669step1 raw32669step0; decide +kernel
      have hl : raw32669step1Labels = raw32669step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32669step0 raw32669step0Labels permutation58 permutation2
    _ = mixedMoment B node5367 node5367Labels := by rfl

theorem canonical32670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32670 raw32670Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw32670 raw32670Labels = mixedMoment B raw32670step0 raw32670step0Labels := by
      have ha : raw32670step0 = (fun i j => raw32670 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32670step0 raw32670; decide +kernel
      have hl : raw32670step0Labels = raw32670Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32670 raw32670Labels permutation664 permutation2
    mixedMoment B raw32670step0 raw32670step0Labels = mixedMoment B raw32670step1 raw32670step1Labels := by
      have ha : raw32670step1 = -raw32670step0 := by apply Matrix.ext; change ∀ i j, raw32670step1 i j = -(raw32670step0 i j); unfold raw32670step1 raw32670step0; decide +kernel
      have hl : raw32670step1Labels = raw32670step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5395 node5395Labels := by rfl

theorem canonical32671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32671 raw32671Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw32671 raw32671Labels = mixedMoment B raw32671step0 raw32671step0Labels := by
      have hz : ∀ j, raw32671 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32671step0 = (fun i j => raw32671 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32671step0 raw32671; decide +kernel
      have hl : raw32671step0Labels = raw32671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32671 raw32671Labels permutation346 hz
    mixedMoment B raw32671step0 raw32671step0Labels = mixedMoment B raw32671step1 raw32671step1Labels := by
      have ha : raw32671step1 = (fun i j => raw32671step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32671step1 raw32671step0; decide +kernel
      have hl : raw32671step1Labels = raw32671step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32671step0 raw32671step0Labels permutation151 permutation2
    mixedMoment B raw32671step1 raw32671step1Labels = mixedMoment B raw32671step2 raw32671step2Labels := by
      have ha : raw32671step2 = -raw32671step1 := by apply Matrix.ext; change ∀ i j, raw32671step2 i j = -(raw32671step1 i j); unfold raw32671step2 raw32671step1; decide +kernel
      have hl : raw32671step2Labels = raw32671step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5428 node5428Labels := by rfl

theorem canonical32672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32672 raw32672Labels = mixedMoment B node5413 node5413Labels := by
  calc
    mixedMoment B raw32672 raw32672Labels = mixedMoment B raw32672step0 raw32672step0Labels := by
      have hz : ∀ j, raw32672 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32672step0 = (fun i j => raw32672 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32672step0 raw32672; decide +kernel
      have hl : raw32672step0Labels = raw32672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32672 raw32672Labels permutation520 hz
    mixedMoment B raw32672step0 raw32672step0Labels = mixedMoment B raw32672step1 raw32672step1Labels := by
      have hz : ∀ j, raw32672step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32672step1 = (fun i j => raw32672step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32672step1 raw32672step0; decide +kernel
      have hl : raw32672step1Labels = raw32672step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32672step0 raw32672step0Labels permutation80 hz
    mixedMoment B raw32672step1 raw32672step1Labels = mixedMoment B raw32672step2 raw32672step2Labels := by
      have ha : raw32672step2 = (fun i j => raw32672step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32672step2 raw32672step1; decide +kernel
      have hl : raw32672step2Labels = raw32672step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32672step1 raw32672step1Labels permutation31 permutation2
    mixedMoment B raw32672step2 raw32672step2Labels = mixedMoment B raw32672step3 raw32672step3Labels := by
      have ha : raw32672step3 = -raw32672step2 := by apply Matrix.ext; change ∀ i j, raw32672step3 i j = -(raw32672step2 i j); unfold raw32672step3 raw32672step2; decide +kernel
      have hl : raw32672step3Labels = raw32672step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5413 node5413Labels := by rfl

theorem canonical32673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32673 raw32673Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw32673 raw32673Labels = mixedMoment B raw32673step0 raw32673step0Labels := by
      have hz : ∀ j, raw32673 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32673step0 = (fun i j => raw32673 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32673step0 raw32673; decide +kernel
      have hl : raw32673step0Labels = raw32673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32673 raw32673Labels permutation346 hz
    mixedMoment B raw32673step0 raw32673step0Labels = mixedMoment B raw32673step1 raw32673step1Labels := by
      have ha : raw32673step1 = (fun i j => raw32673step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32673step1 raw32673step0; decide +kernel
      have hl : raw32673step1Labels = raw32673step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32673step0 raw32673step0Labels permutation58 permutation7
    mixedMoment B raw32673step1 raw32673step1Labels = mixedMoment B raw32673step2 raw32673step2Labels := by
      have ha : raw32673step2 = -raw32673step1 := by apply Matrix.ext; change ∀ i j, raw32673step2 i j = -(raw32673step1 i j); unfold raw32673step2 raw32673step1; decide +kernel
      have hl : raw32673step2Labels = raw32673step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32673step2 raw32673step2Labels = mixedMoment B raw32673step3 raw32673step3Labels := by
      have ha : raw32673step3 = raw32673step2 := by apply Matrix.ext; unfold raw32673step3 raw32673step2; decide +kernel
      have hl : raw32673step2Labels = labelEmbedding10 ∘ raw32673step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32673step2 raw32673step2Labels raw32673step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical32674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32674 raw32674Labels = mixedMoment B node4475 node4475Labels := by
  calc
    mixedMoment B raw32674 raw32674Labels = mixedMoment B raw32674step0 raw32674step0Labels := by
      have hz : ∀ j, raw32674 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32674step0 = (fun i j => raw32674 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32674step0 raw32674; decide +kernel
      have hl : raw32674step0Labels = raw32674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32674 raw32674Labels permutation346 hz
    mixedMoment B raw32674step0 raw32674step0Labels = mixedMoment B raw32674step1 raw32674step1Labels := by
      have ha : raw32674step1 = (fun i j => raw32674step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32674step1 raw32674step0; decide +kernel
      have hl : raw32674step1Labels = raw32674step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32674step0 raw32674step0Labels permutation32 permutation3
    mixedMoment B raw32674step1 raw32674step1Labels = mixedMoment B raw32674step2 raw32674step2Labels := by
      have ha : raw32674step2 = raw32674step1 := by apply Matrix.ext; unfold raw32674step2 raw32674step1; decide +kernel
      have hl : raw32674step1Labels = labelEmbedding6 ∘ raw32674step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32674step1 raw32674step1Labels raw32674step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4475 node4475Labels := by rfl

theorem canonical32675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32675 raw32675Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw32675 raw32675Labels = mixedMoment B raw32675step0 raw32675step0Labels := by
      have ha : raw32675step0 = (fun i j => raw32675 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32675step0 raw32675; decide +kernel
      have hl : raw32675step0Labels = raw32675Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32675 raw32675Labels permutation176 permutation3
    mixedMoment B raw32675step0 raw32675step0Labels = mixedMoment B raw32675step1 raw32675step1Labels := by
      have ha : raw32675step1 = raw32675step0 := by apply Matrix.ext; unfold raw32675step1 raw32675step0; decide +kernel
      have hl : raw32675step0Labels = labelEmbedding6 ∘ raw32675step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32675step0 raw32675step0Labels raw32675step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5086 node5086Labels := by rfl

theorem canonical32676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32676 raw32676Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw32676 raw32676Labels = mixedMoment B raw32676step0 raw32676step0Labels := by
      have hz : ∀ j, raw32676 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32676step0 = (fun i j => raw32676 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32676step0 raw32676; decide +kernel
      have hl : raw32676step0Labels = raw32676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32676 raw32676Labels permutation346 hz
    mixedMoment B raw32676step0 raw32676step0Labels = mixedMoment B raw32676step1 raw32676step1Labels := by
      have ha : raw32676step1 = (fun i j => raw32676step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32676step1 raw32676step0; decide +kernel
      have hl : raw32676step1Labels = raw32676step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32676step0 raw32676step0Labels permutation38 permutation3
    mixedMoment B raw32676step1 raw32676step1Labels = mixedMoment B raw32676step2 raw32676step2Labels := by
      have ha : raw32676step2 = raw32676step1 := by apply Matrix.ext; unfold raw32676step2 raw32676step1; decide +kernel
      have hl : raw32676step1Labels = labelEmbedding6 ∘ raw32676step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32676step1 raw32676step1Labels raw32676step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

theorem canonical32677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32677 raw32677Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw32677 raw32677Labels = mixedMoment B raw32677step0 raw32677step0Labels := by
      have hz : ∀ j, raw32677 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32677step0 = (fun i j => raw32677 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32677step0 raw32677; decide +kernel
      have hl : raw32677step0Labels = raw32677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32677 raw32677Labels permutation520 hz
    mixedMoment B raw32677step0 raw32677step0Labels = mixedMoment B raw32677step1 raw32677step1Labels := by
      have hz : ∀ j, raw32677step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32677step1 = (fun i j => raw32677step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32677step1 raw32677step0; decide +kernel
      have hl : raw32677step1Labels = raw32677step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32677step0 raw32677step0Labels permutation80 hz
    mixedMoment B raw32677step1 raw32677step1Labels = mixedMoment B raw32677step2 raw32677step2Labels := by
      have ha : raw32677step2 = (fun i j => raw32677step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32677step2 raw32677step1; decide +kernel
      have hl : raw32677step2Labels = raw32677step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32677step1 raw32677step1Labels permutation8 permutation3
    mixedMoment B raw32677step2 raw32677step2Labels = mixedMoment B raw32677step3 raw32677step3Labels := by
      have ha : raw32677step3 = raw32677step2 := by apply Matrix.ext; unfold raw32677step3 raw32677step2; decide +kernel
      have hl : raw32677step2Labels = labelEmbedding6 ∘ raw32677step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32677step2 raw32677step2Labels raw32677step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

theorem canonical32678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32678 raw32678Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw32678 raw32678Labels = mixedMoment B raw32678step0 raw32678step0Labels := by
      have hz : ∀ j, raw32678 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32678step0 = (fun i j => raw32678 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32678step0 raw32678; decide +kernel
      have hl : raw32678step0Labels = raw32678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32678 raw32678Labels permutation346 hz
    mixedMoment B raw32678step0 raw32678step0Labels = mixedMoment B raw32678step1 raw32678step1Labels := by
      have ha : raw32678step1 = (fun i j => raw32678step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32678step1 raw32678step0; decide +kernel
      have hl : raw32678step1Labels = raw32678step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32678step0 raw32678step0Labels permutation36 permutation3
    mixedMoment B raw32678step1 raw32678step1Labels = mixedMoment B raw32678step2 raw32678step2Labels := by
      have ha : raw32678step2 = raw32678step1 := by apply Matrix.ext; unfold raw32678step2 raw32678step1; decide +kernel
      have hl : raw32678step1Labels = labelEmbedding6 ∘ raw32678step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32678step1 raw32678step1Labels raw32678step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

theorem canonical32679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32679 raw32679Labels = mixedMoment B node4366 node4366Labels := by
  calc
    mixedMoment B raw32679 raw32679Labels = mixedMoment B raw32679step0 raw32679step0Labels := by
      have ha : raw32679step0 = (fun i j => raw32679 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32679step0 raw32679; decide +kernel
      have hl : raw32679step0Labels = raw32679Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32679 raw32679Labels permutation158 permutation3
    mixedMoment B raw32679step0 raw32679step0Labels = mixedMoment B raw32679step1 raw32679step1Labels := by
      have ha : raw32679step1 = raw32679step0 := by apply Matrix.ext; unfold raw32679step1 raw32679step0; decide +kernel
      have hl : raw32679step0Labels = labelEmbedding6 ∘ raw32679step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32679step0 raw32679step0Labels raw32679step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4366 node4366Labels := by rfl

theorem canonical32680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32680 raw32680Labels = mixedMoment B node4971 node4971Labels := by
  calc
    mixedMoment B raw32680 raw32680Labels = mixedMoment B raw32680step0 raw32680step0Labels := by
      have ha : raw32680step0 = (fun i j => raw32680 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32680step0 raw32680; decide +kernel
      have hl : raw32680step0Labels = raw32680Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32680 raw32680Labels permutation158 permutation3
    mixedMoment B raw32680step0 raw32680step0Labels = mixedMoment B raw32680step1 raw32680step1Labels := by
      have ha : raw32680step1 = raw32680step0 := by apply Matrix.ext; unfold raw32680step1 raw32680step0; decide +kernel
      have hl : raw32680step0Labels = labelEmbedding6 ∘ raw32680step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32680step0 raw32680step0Labels raw32680step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4971 node4971Labels := by rfl

theorem canonical32681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32681 raw32681Labels = mixedMoment B node5187 node5187Labels := by
  calc
    mixedMoment B raw32681 raw32681Labels = mixedMoment B raw32681step0 raw32681step0Labels := by
      have ha : raw32681step0 = (fun i j => raw32681 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32681step0 raw32681; decide +kernel
      have hl : raw32681step0Labels = raw32681Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32681 raw32681Labels permutation158 permutation3
    mixedMoment B raw32681step0 raw32681step0Labels = mixedMoment B raw32681step1 raw32681step1Labels := by
      have ha : raw32681step1 = raw32681step0 := by apply Matrix.ext; unfold raw32681step1 raw32681step0; decide +kernel
      have hl : raw32681step0Labels = labelEmbedding6 ∘ raw32681step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32681step0 raw32681step0Labels raw32681step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5187 node5187Labels := by rfl

theorem canonical32682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32682 raw32682Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw32682 raw32682Labels = mixedMoment B raw32682step0 raw32682step0Labels := by
      have hz : ∀ j, raw32682 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32682step0 = (fun i j => raw32682 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32682step0 raw32682; decide +kernel
      have hl : raw32682step0Labels = raw32682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32682 raw32682Labels permutation520 hz
    mixedMoment B raw32682step0 raw32682step0Labels = mixedMoment B raw32682step1 raw32682step1Labels := by
      have ha : raw32682step1 = (fun i j => raw32682step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32682step1 raw32682step0; decide +kernel
      have hl : raw32682step1Labels = raw32682step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32682step0 raw32682step0Labels permutation34 permutation3
    mixedMoment B raw32682step1 raw32682step1Labels = mixedMoment B raw32682step2 raw32682step2Labels := by
      have ha : raw32682step2 = raw32682step1 := by apply Matrix.ext; unfold raw32682step2 raw32682step1; decide +kernel
      have hl : raw32682step1Labels = labelEmbedding6 ∘ raw32682step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32682step1 raw32682step1Labels raw32682step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

theorem canonical32683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32683 raw32683Labels = mixedMoment B node5197 node5197Labels := by
  calc
    mixedMoment B raw32683 raw32683Labels = mixedMoment B raw32683step0 raw32683step0Labels := by
      have ha : raw32683step0 = (fun i j => raw32683 (permutation172 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32683step0 raw32683; decide +kernel
      have hl : raw32683step0Labels = raw32683Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32683 raw32683Labels permutation172 permutation3
    mixedMoment B raw32683step0 raw32683step0Labels = mixedMoment B raw32683step1 raw32683step1Labels := by
      have ha : raw32683step1 = raw32683step0 := by apply Matrix.ext; unfold raw32683step1 raw32683step0; decide +kernel
      have hl : raw32683step0Labels = labelEmbedding6 ∘ raw32683step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32683step0 raw32683step0Labels raw32683step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5197 node5197Labels := by rfl

theorem canonical32684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32684 raw32684Labels = mixedMoment B node4372 node4372Labels := by
  calc
    mixedMoment B raw32684 raw32684Labels = mixedMoment B raw32684step0 raw32684step0Labels := by
      have hz : ∀ j, raw32684 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32684step0 = (fun i j => raw32684 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32684step0 raw32684; decide +kernel
      have hl : raw32684step0Labels = raw32684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32684 raw32684Labels permutation346 hz
    mixedMoment B raw32684step0 raw32684step0Labels = mixedMoment B raw32684step1 raw32684step1Labels := by
      have ha : raw32684step1 = (fun i j => raw32684step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32684step1 raw32684step0; decide +kernel
      have hl : raw32684step1Labels = raw32684step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32684step0 raw32684step0Labels permutation35 permutation3
    mixedMoment B raw32684step1 raw32684step1Labels = mixedMoment B raw32684step2 raw32684step2Labels := by
      have ha : raw32684step2 = raw32684step1 := by apply Matrix.ext; unfold raw32684step2 raw32684step1; decide +kernel
      have hl : raw32684step1Labels = labelEmbedding6 ∘ raw32684step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32684step1 raw32684step1Labels raw32684step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4372 node4372Labels := by rfl

theorem canonical32685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32685 raw32685Labels = mixedMoment B node4977 node4977Labels := by
  calc
    mixedMoment B raw32685 raw32685Labels = mixedMoment B raw32685step0 raw32685step0Labels := by
      have hz : ∀ j, raw32685 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32685step0 = (fun i j => raw32685 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32685step0 raw32685; decide +kernel
      have hl : raw32685step0Labels = raw32685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32685 raw32685Labels permutation346 hz
    mixedMoment B raw32685step0 raw32685step0Labels = mixedMoment B raw32685step1 raw32685step1Labels := by
      have ha : raw32685step1 = (fun i j => raw32685step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32685step1 raw32685step0; decide +kernel
      have hl : raw32685step1Labels = raw32685step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32685step0 raw32685step0Labels permutation35 permutation3
    mixedMoment B raw32685step1 raw32685step1Labels = mixedMoment B raw32685step2 raw32685step2Labels := by
      have ha : raw32685step2 = raw32685step1 := by apply Matrix.ext; unfold raw32685step2 raw32685step1; decide +kernel
      have hl : raw32685step1Labels = labelEmbedding6 ∘ raw32685step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32685step1 raw32685step1Labels raw32685step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4977 node4977Labels := by rfl

theorem canonical32686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32686 raw32686Labels = mixedMoment B node5044 node5044Labels := by
  calc
    mixedMoment B raw32686 raw32686Labels = mixedMoment B raw32686step0 raw32686step0Labels := by
      have ha : raw32686step0 = (fun i j => raw32686 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32686step0 raw32686; decide +kernel
      have hl : raw32686step0Labels = raw32686Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32686 raw32686Labels permutation179 permutation3
    mixedMoment B raw32686step0 raw32686step0Labels = mixedMoment B raw32686step1 raw32686step1Labels := by
      have ha : raw32686step1 = raw32686step0 := by apply Matrix.ext; unfold raw32686step1 raw32686step0; decide +kernel
      have hl : raw32686step0Labels = labelEmbedding6 ∘ raw32686step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32686step0 raw32686step0Labels raw32686step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5044 node5044Labels := by rfl

theorem canonical32687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32687 raw32687Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw32687 raw32687Labels = mixedMoment B raw32687step0 raw32687step0Labels := by
      have hz : ∀ j, raw32687 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32687step0 = (fun i j => raw32687 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32687step0 raw32687; decide +kernel
      have hl : raw32687step0Labels = raw32687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32687 raw32687Labels permutation520 hz
    mixedMoment B raw32687step0 raw32687step0Labels = mixedMoment B raw32687step1 raw32687step1Labels := by
      have hz : ∀ j, raw32687step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32687step1 = (fun i j => raw32687step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32687step1 raw32687step0; decide +kernel
      have hl : raw32687step1Labels = raw32687step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32687step0 raw32687step0Labels permutation80 hz
    mixedMoment B raw32687step1 raw32687step1Labels = mixedMoment B raw32687step2 raw32687step2Labels := by
      have ha : raw32687step2 = (fun i j => raw32687step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32687step2 raw32687step1; decide +kernel
      have hl : raw32687step2Labels = raw32687step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32687step1 raw32687step1Labels permutation9 permutation3
    mixedMoment B raw32687step2 raw32687step2Labels = mixedMoment B raw32687step3 raw32687step3Labels := by
      have ha : raw32687step3 = raw32687step2 := by apply Matrix.ext; unfold raw32687step3 raw32687step2; decide +kernel
      have hl : raw32687step2Labels = labelEmbedding6 ∘ raw32687step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32687step2 raw32687step2Labels raw32687step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5207 node5207Labels := by rfl

theorem canonical32688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32688 raw32688Labels = mixedMoment B node5199 node5199Labels := by
  calc
    mixedMoment B raw32688 raw32688Labels = mixedMoment B raw32688step0 raw32688step0Labels := by
      have hz : ∀ j, raw32688 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32688step0 = (fun i j => raw32688 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32688step0 raw32688; decide +kernel
      have hl : raw32688step0Labels = raw32688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32688 raw32688Labels permutation346 hz
    mixedMoment B raw32688step0 raw32688step0Labels = mixedMoment B raw32688step1 raw32688step1Labels := by
      have ha : raw32688step1 = (fun i j => raw32688step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32688step1 raw32688step0; decide +kernel
      have hl : raw32688step1Labels = raw32688step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32688step0 raw32688step0Labels permutation37 permutation3
    mixedMoment B raw32688step1 raw32688step1Labels = mixedMoment B raw32688step2 raw32688step2Labels := by
      have ha : raw32688step2 = raw32688step1 := by apply Matrix.ext; unfold raw32688step2 raw32688step1; decide +kernel
      have hl : raw32688step1Labels = labelEmbedding6 ∘ raw32688step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32688step1 raw32688step1Labels raw32688step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5199 node5199Labels := by rfl

theorem canonical32689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32689 raw32689Labels = mixedMoment B node4368 node4368Labels := by
  calc
    mixedMoment B raw32689 raw32689Labels = mixedMoment B raw32689step0 raw32689step0Labels := by
      have hz : ∀ j, raw32689 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32689step0 = (fun i j => raw32689 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32689step0 raw32689; decide +kernel
      have hl : raw32689step0Labels = raw32689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32689 raw32689Labels permutation346 hz
    mixedMoment B raw32689step0 raw32689step0Labels = mixedMoment B raw32689step1 raw32689step1Labels := by
      have ha : raw32689step1 = (fun i j => raw32689step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32689step1 raw32689step0; decide +kernel
      have hl : raw32689step1Labels = raw32689step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32689step0 raw32689step0Labels permutation33 permutation3
    mixedMoment B raw32689step1 raw32689step1Labels = mixedMoment B raw32689step2 raw32689step2Labels := by
      have ha : raw32689step2 = raw32689step1 := by apply Matrix.ext; unfold raw32689step2 raw32689step1; decide +kernel
      have hl : raw32689step1Labels = labelEmbedding6 ∘ raw32689step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32689step1 raw32689step1Labels raw32689step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4368 node4368Labels := by rfl

theorem canonical32690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32690 raw32690Labels = mixedMoment B node4973 node4973Labels := by
  calc
    mixedMoment B raw32690 raw32690Labels = mixedMoment B raw32690step0 raw32690step0Labels := by
      have hz : ∀ j, raw32690 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32690step0 = (fun i j => raw32690 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32690step0 raw32690; decide +kernel
      have hl : raw32690step0Labels = raw32690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32690 raw32690Labels permutation346 hz
    mixedMoment B raw32690step0 raw32690step0Labels = mixedMoment B raw32690step1 raw32690step1Labels := by
      have ha : raw32690step1 = (fun i j => raw32690step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32690step1 raw32690step0; decide +kernel
      have hl : raw32690step1Labels = raw32690step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32690step0 raw32690step0Labels permutation33 permutation3
    mixedMoment B raw32690step1 raw32690step1Labels = mixedMoment B raw32690step2 raw32690step2Labels := by
      have ha : raw32690step2 = raw32690step1 := by apply Matrix.ext; unfold raw32690step2 raw32690step1; decide +kernel
      have hl : raw32690step1Labels = labelEmbedding6 ∘ raw32690step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32690step1 raw32690step1Labels raw32690step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4973 node4973Labels := by rfl

theorem canonical32691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32691 raw32691Labels = mixedMoment B node5042 node5042Labels := by
  calc
    mixedMoment B raw32691 raw32691Labels = mixedMoment B raw32691step0 raw32691step0Labels := by
      have ha : raw32691step0 = (fun i j => raw32691 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32691step0 raw32691; decide +kernel
      have hl : raw32691step0Labels = raw32691Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32691 raw32691Labels permutation177 permutation3
    mixedMoment B raw32691step0 raw32691step0Labels = mixedMoment B raw32691step1 raw32691step1Labels := by
      have ha : raw32691step1 = raw32691step0 := by apply Matrix.ext; unfold raw32691step1 raw32691step0; decide +kernel
      have hl : raw32691step0Labels = labelEmbedding6 ∘ raw32691step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32691step0 raw32691step0Labels raw32691step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5042 node5042Labels := by rfl

theorem canonical32692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32692 raw32692Labels = mixedMoment B node5188 node5188Labels := by
  calc
    mixedMoment B raw32692 raw32692Labels = mixedMoment B raw32692step0 raw32692step0Labels := by
      have hz : ∀ j, raw32692 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32692step0 = (fun i j => raw32692 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32692step0 raw32692; decide +kernel
      have hl : raw32692step0Labels = raw32692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32692 raw32692Labels permutation346 hz
    mixedMoment B raw32692step0 raw32692step0Labels = mixedMoment B raw32692step1 raw32692step1Labels := by
      have ha : raw32692step1 = (fun i j => raw32692step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32692step1 raw32692step0; decide +kernel
      have hl : raw32692step1Labels = raw32692step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32692step0 raw32692step0Labels permutation33 permutation3
    mixedMoment B raw32692step1 raw32692step1Labels = mixedMoment B raw32692step2 raw32692step2Labels := by
      have ha : raw32692step2 = raw32692step1 := by apply Matrix.ext; unfold raw32692step2 raw32692step1; decide +kernel
      have hl : raw32692step1Labels = labelEmbedding6 ∘ raw32692step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32692step1 raw32692step1Labels raw32692step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5188 node5188Labels := by rfl

theorem canonical32693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32693 raw32693Labels = mixedMoment B node5198 node5198Labels := by
  calc
    mixedMoment B raw32693 raw32693Labels = mixedMoment B raw32693step0 raw32693step0Labels := by
      have hz : ∀ j, raw32693 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32693step0 = (fun i j => raw32693 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32693step0 raw32693; decide +kernel
      have hl : raw32693step0Labels = raw32693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32693 raw32693Labels permutation346 hz
    mixedMoment B raw32693step0 raw32693step0Labels = mixedMoment B raw32693step1 raw32693step1Labels := by
      have ha : raw32693step1 = (fun i j => raw32693step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32693step1 raw32693step0; decide +kernel
      have hl : raw32693step1Labels = raw32693step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32693step0 raw32693step0Labels permutation36 permutation3
    mixedMoment B raw32693step1 raw32693step1Labels = mixedMoment B raw32693step2 raw32693step2Labels := by
      have ha : raw32693step2 = raw32693step1 := by apply Matrix.ext; unfold raw32693step2 raw32693step1; decide +kernel
      have hl : raw32693step1Labels = labelEmbedding6 ∘ raw32693step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32693step1 raw32693step1Labels raw32693step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5198 node5198Labels := by rfl

theorem canonical32694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32694 raw32694Labels = mixedMoment B node4367 node4367Labels := by
  calc
    mixedMoment B raw32694 raw32694Labels = mixedMoment B raw32694step0 raw32694step0Labels := by
      have hz : ∀ j, raw32694 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32694step0 = (fun i j => raw32694 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32694step0 raw32694; decide +kernel
      have hl : raw32694step0Labels = raw32694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32694 raw32694Labels permutation346 hz
    mixedMoment B raw32694step0 raw32694step0Labels = mixedMoment B raw32694step1 raw32694step1Labels := by
      have ha : raw32694step1 = (fun i j => raw32694step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32694step1 raw32694step0; decide +kernel
      have hl : raw32694step1Labels = raw32694step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32694step0 raw32694step0Labels permutation32 permutation3
    mixedMoment B raw32694step1 raw32694step1Labels = mixedMoment B raw32694step2 raw32694step2Labels := by
      have ha : raw32694step2 = raw32694step1 := by apply Matrix.ext; unfold raw32694step2 raw32694step1; decide +kernel
      have hl : raw32694step1Labels = labelEmbedding6 ∘ raw32694step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32694step1 raw32694step1Labels raw32694step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4367 node4367Labels := by rfl

theorem canonical32695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32695 raw32695Labels = mixedMoment B node4972 node4972Labels := by
  calc
    mixedMoment B raw32695 raw32695Labels = mixedMoment B raw32695step0 raw32695step0Labels := by
      have hz : ∀ j, raw32695 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32695step0 = (fun i j => raw32695 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32695step0 raw32695; decide +kernel
      have hl : raw32695step0Labels = raw32695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32695 raw32695Labels permutation346 hz
    mixedMoment B raw32695step0 raw32695step0Labels = mixedMoment B raw32695step1 raw32695step1Labels := by
      have ha : raw32695step1 = (fun i j => raw32695step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32695step1 raw32695step0; decide +kernel
      have hl : raw32695step1Labels = raw32695step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32695step0 raw32695step0Labels permutation32 permutation3
    mixedMoment B raw32695step1 raw32695step1Labels = mixedMoment B raw32695step2 raw32695step2Labels := by
      have ha : raw32695step2 = raw32695step1 := by apply Matrix.ext; unfold raw32695step2 raw32695step1; decide +kernel
      have hl : raw32695step1Labels = labelEmbedding6 ∘ raw32695step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32695step1 raw32695step1Labels raw32695step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4972 node4972Labels := by rfl

theorem canonical32696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32696 raw32696Labels = mixedMoment B node5034 node5034Labels := by
  calc
    mixedMoment B raw32696 raw32696Labels = mixedMoment B raw32696step0 raw32696step0Labels := by
      have ha : raw32696step0 = (fun i j => raw32696 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32696step0 raw32696; decide +kernel
      have hl : raw32696step0Labels = raw32696Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32696 raw32696Labels permutation664 permutation2
    mixedMoment B raw32696step0 raw32696step0Labels = mixedMoment B raw32696step1 raw32696step1Labels := by
      have ha : raw32696step1 = -raw32696step0 := by apply Matrix.ext; change ∀ i j, raw32696step1 i j = -(raw32696step0 i j); unfold raw32696step1 raw32696step0; decide +kernel
      have hl : raw32696step1Labels = raw32696step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5034 node5034Labels := by rfl

theorem canonical32697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32697 raw32697Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw32697 raw32697Labels = mixedMoment B raw32697step0 raw32697step0Labels := by
      have hz : ∀ j, raw32697 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32697step0 = (fun i j => raw32697 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32697step0 raw32697; decide +kernel
      have hl : raw32697step0Labels = raw32697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32697 raw32697Labels permutation346 hz
    mixedMoment B raw32697step0 raw32697step0Labels = mixedMoment B raw32697step1 raw32697step1Labels := by
      have ha : raw32697step1 = (fun i j => raw32697step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32697step1 raw32697step0; decide +kernel
      have hl : raw32697step1Labels = raw32697step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32697step0 raw32697step0Labels permutation151 permutation2
    mixedMoment B raw32697step1 raw32697step1Labels = mixedMoment B raw32697step2 raw32697step2Labels := by
      have ha : raw32697step2 = -raw32697step1 := by apply Matrix.ext; change ∀ i j, raw32697step2 i j = -(raw32697step1 i j); unfold raw32697step2 raw32697step1; decide +kernel
      have hl : raw32697step2Labels = raw32697step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5139 node5139Labels := by rfl

theorem canonical32698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32698 raw32698Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw32698 raw32698Labels = mixedMoment B raw32698step0 raw32698step0Labels := by
      have hz : ∀ j, raw32698 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32698step0 = (fun i j => raw32698 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32698step0 raw32698; decide +kernel
      have hl : raw32698step0Labels = raw32698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32698 raw32698Labels permutation520 hz
    mixedMoment B raw32698step0 raw32698step0Labels = mixedMoment B raw32698step1 raw32698step1Labels := by
      have hz : ∀ j, raw32698step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32698step1 = (fun i j => raw32698step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32698step1 raw32698step0; decide +kernel
      have hl : raw32698step1Labels = raw32698step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32698step0 raw32698step0Labels permutation80 hz
    mixedMoment B raw32698step1 raw32698step1Labels = mixedMoment B raw32698step2 raw32698step2Labels := by
      have ha : raw32698step2 = (fun i j => raw32698step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32698step2 raw32698step1; decide +kernel
      have hl : raw32698step2Labels = raw32698step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32698step1 raw32698step1Labels permutation31 permutation2
    mixedMoment B raw32698step2 raw32698step2Labels = mixedMoment B raw32698step3 raw32698step3Labels := by
      have ha : raw32698step3 = -raw32698step2 := by apply Matrix.ext; change ∀ i j, raw32698step3 i j = -(raw32698step2 i j); unfold raw32698step3 raw32698step2; decide +kernel
      have hl : raw32698step3Labels = raw32698step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5109 node5109Labels := by rfl

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

theorem singleton4971 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4971 node4971Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2807 node2807Labels + mixedMoment B node3590 node3590Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1953 singletonSmall4971
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4971) = raw1953Labels := by decide +kernel
  rw [hl, canonical1953 B hB] at h
  have hc0 : mixedMoment B raw1953 (Fin.cases (0 : Fin 2) singletonSmall4971) =
      mixedMoment B node2807 node2807Labels := by
    have ha : raw1953 = raw1954 := by apply Matrix.ext; unfold raw1953 raw1954; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4971 = raw1954Labels := by decide +kernel
    rw [ha, hj, canonical1954 B hB]
  have hc1 : mixedMoment B raw1953 (Fin.cases (1 : Fin 2) singletonSmall4971) =
      mixedMoment B node3590 node3590Labels := by
    have ha : raw1953 = raw1955 := by apply Matrix.ext; unfold raw1953 raw1955; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4971 = raw1955Labels := by decide +kernel
    rw [ha, hj, canonical1955 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4972 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4972 node4972Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2434 node2434Labels + mixedMoment B node3457 node3457Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1956 singletonSmall4972
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4972) = raw1956Labels := by decide +kernel
  rw [hl, canonical1956 B hB] at h
  have hc0 : mixedMoment B raw1956 (Fin.cases (0 : Fin 2) singletonSmall4972) =
      mixedMoment B node2434 node2434Labels := by
    have ha : raw1956 = raw1957 := by apply Matrix.ext; unfold raw1956 raw1957; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4972 = raw1957Labels := by decide +kernel
    rw [ha, hj, canonical1957 B hB]
  have hc1 : mixedMoment B raw1956 (Fin.cases (1 : Fin 2) singletonSmall4972) =
      mixedMoment B node3457 node3457Labels := by
    have ha : raw1956 = raw1958 := by apply Matrix.ext; unfold raw1956 raw1958; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4972 = raw1958Labels := by decide +kernel
    rw [ha, hj, canonical1958 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4973 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4973 node4973Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2817 node2817Labels + mixedMoment B node3591 node3591Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1959 singletonSmall4973
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4973) = raw1959Labels := by decide +kernel
  rw [hl, canonical1959 B hB] at h
  have hc0 : mixedMoment B raw1959 (Fin.cases (0 : Fin 2) singletonSmall4973) =
      mixedMoment B node2817 node2817Labels := by
    have ha : raw1959 = raw1960 := by apply Matrix.ext; unfold raw1959 raw1960; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4973 = raw1960Labels := by decide +kernel
    rw [ha, hj, canonical1960 B hB]
  have hc1 : mixedMoment B raw1959 (Fin.cases (1 : Fin 2) singletonSmall4973) =
      mixedMoment B node3591 node3591Labels := by
    have ha : raw1959 = raw1961 := by apply Matrix.ext; unfold raw1959 raw1961; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4973 = raw1961Labels := by decide +kernel
    rw [ha, hj, canonical1961 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4977 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4977 node4977Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2813 node2813Labels + mixedMoment B node3595 node3595Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1965 singletonSmall4977
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4977) = raw1965Labels := by decide +kernel
  rw [hl, canonical1965 B hB] at h
  have hc0 : mixedMoment B raw1965 (Fin.cases (0 : Fin 2) singletonSmall4977) =
      mixedMoment B node2813 node2813Labels := by
    have ha : raw1965 = raw1966 := by apply Matrix.ext; unfold raw1965 raw1966; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4977 = raw1966Labels := by decide +kernel
    rw [ha, hj, canonical1966 B hB]
  have hc1 : mixedMoment B raw1965 (Fin.cases (1 : Fin 2) singletonSmall4977) =
      mixedMoment B node3595 node3595Labels := by
    have ha : raw1965 = raw1967 := by apply Matrix.ext; unfold raw1965 raw1967; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4977 = raw1967Labels := by decide +kernel
    rw [ha, hj, canonical1967 B hB]
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

theorem singleton5109 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5109 node5109Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2519 node2519Labels + mixedMoment B node3486 node3486Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2133 singletonSmall5109
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5109) = raw2133Labels := by decide +kernel
  rw [hl, canonical2133 B hB] at h
  have hc0 : mixedMoment B raw2133 (Fin.cases (0 : Fin 2) singletonSmall5109) =
      mixedMoment B node2519 node2519Labels := by
    have ha : raw2133 = raw2134 := by apply Matrix.ext; unfold raw2133 raw2134; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5109 = raw2134Labels := by decide +kernel
    rw [ha, hj, canonical2134 B hB]
  have hc1 : mixedMoment B raw2133 (Fin.cases (1 : Fin 2) singletonSmall5109) =
      mixedMoment B node3486 node3486Labels := by
    have ha : raw2133 = raw2135 := by apply Matrix.ext; unfold raw2133 raw2135; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5109 = raw2135Labels := by decide +kernel
    rw [ha, hj, canonical2135 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5204 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5204 node5204Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2881 node2881Labels + mixedMoment B node3624 node3624Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2232 singletonSmall5204
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5204) = raw2232Labels := by decide +kernel
  rw [hl, canonical2232 B hB] at h
  have hc0 : mixedMoment B raw2232 (Fin.cases (0 : Fin 2) singletonSmall5204) =
      mixedMoment B node2881 node2881Labels := by
    have ha : raw2232 = raw2233 := by apply Matrix.ext; unfold raw2232 raw2233; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5204 = raw2233Labels := by decide +kernel
    rw [ha, hj, canonical2233 B hB]
  have hc1 : mixedMoment B raw2232 (Fin.cases (1 : Fin 2) singletonSmall5204) =
      mixedMoment B node3624 node3624Labels := by
    have ha : raw2232 = raw2234 := by apply Matrix.ext; unfold raw2232 raw2234; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5204 = raw2234Labels := by decide +kernel
    rw [ha, hj, canonical2234 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5207 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5207 node5207Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2889 node2889Labels + mixedMoment B node3631 node3631Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2235 singletonSmall5207
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5207) = raw2235Labels := by decide +kernel
  rw [hl, canonical2235 B hB] at h
  have hc0 : mixedMoment B raw2235 (Fin.cases (0 : Fin 2) singletonSmall5207) =
      mixedMoment B node2889 node2889Labels := by
    have ha : raw2235 = raw2236 := by apply Matrix.ext; unfold raw2235 raw2236; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5207 = raw2236Labels := by decide +kernel
    rw [ha, hj, canonical2236 B hB]
  have hc1 : mixedMoment B raw2235 (Fin.cases (1 : Fin 2) singletonSmall5207) =
      mixedMoment B node3631 node3631Labels := by
    have ha : raw2235 = raw2237 := by apply Matrix.ext; unfold raw2235 raw2237; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5207 = raw2237Labels := by decide +kernel
    rw [ha, hj, canonical2237 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5395 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5395 node5395Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3781 node3781Labels + mixedMoment B node3794 node3794Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2463 singletonSmall5395
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5395) = raw2463Labels := by decide +kernel
  rw [hl, canonical2463 B hB] at h
  have hc0 : mixedMoment B raw2463 (Fin.cases (0 : Fin 2) singletonSmall5395) =
      mixedMoment B node3781 node3781Labels := by
    have ha : raw2463 = raw2464 := by apply Matrix.ext; unfold raw2463 raw2464; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5395 = raw2464Labels := by decide +kernel
    rw [ha, hj, canonical2464 B hB]
  have hc1 : mixedMoment B raw2463 (Fin.cases (1 : Fin 2) singletonSmall5395) =
      mixedMoment B node3794 node3794Labels := by
    have ha : raw2463 = raw2465 := by apply Matrix.ext; unfold raw2463 raw2465; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5395 = raw2465Labels := by decide +kernel
    rw [ha, hj, canonical2465 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5428 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5428 node5428Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3845 node3845Labels + mixedMoment B node3845 node3845Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2517 singletonSmall5428
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5428) = raw2517Labels := by decide +kernel
  rw [hl, canonical2517 B hB] at h
  have hc0 : mixedMoment B raw2517 (Fin.cases (0 : Fin 2) singletonSmall5428) =
      mixedMoment B node3845 node3845Labels := by
    have ha : raw2517 = raw2518 := by apply Matrix.ext; unfold raw2517 raw2518; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5428 = raw2518Labels := by decide +kernel
    rw [ha, hj, canonical2518 B hB]
  have hc1 : mixedMoment B raw2517 (Fin.cases (1 : Fin 2) singletonSmall5428) =
      mixedMoment B node3845 node3845Labels := by
    have ha : raw2517 = raw2519 := by apply Matrix.ext; unfold raw2517 raw2519; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5428 = raw2519Labels := by decide +kernel
    rw [ha, hj, canonical2519 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2434 node2434Labels = Sparse.eval nodeValue2434 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2434) = mixedMoment B node2434 node2434Labels := rfl
  simpa [nodeValue2434, Sparse.eval] using hc.symm

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

theorem sound2519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2519 node2519Labels = Sparse.eval nodeValue2519 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2519) = mixedMoment B node2519 node2519Labels := rfl
  simpa [nodeValue2519, Sparse.eval] using hc.symm

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

theorem sound2807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2807 node2807Labels = Sparse.eval nodeValue2807 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2807) = mixedMoment B node2807 node2807Labels := rfl
  simpa [nodeValue2807, Sparse.eval] using hc.symm

theorem sound2813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2813 node2813Labels = Sparse.eval nodeValue2813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2813) = mixedMoment B node2813 node2813Labels := rfl
  simpa [nodeValue2813, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2817 node2817Labels = Sparse.eval nodeValue2817 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2817) = mixedMoment B node2817 node2817Labels := rfl
  simpa [nodeValue2817, Sparse.eval] using hc.symm

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

theorem sound2881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2881 node2881Labels = Sparse.eval nodeValue2881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2881) = mixedMoment B node2881 node2881Labels := rfl
  simpa [nodeValue2881, Sparse.eval] using hc.symm

theorem sound2889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2889 node2889Labels = Sparse.eval nodeValue2889 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2889) = mixedMoment B node2889 node2889Labels := rfl
  simpa [nodeValue2889, Sparse.eval] using hc.symm

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

theorem sound3457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3457 node3457Labels = Sparse.eval nodeValue3457 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3457) = mixedMoment B node3457 node3457Labels := rfl
  simpa [nodeValue3457, Sparse.eval] using hc.symm

theorem sound3486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3486 node3486Labels = Sparse.eval nodeValue3486 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3486) = mixedMoment B node3486 node3486Labels := rfl
  simpa [nodeValue3486, Sparse.eval] using hc.symm

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

theorem sound3590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3590 node3590Labels = Sparse.eval nodeValue3590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3590) = mixedMoment B node3590 node3590Labels := rfl
  simpa [nodeValue3590, Sparse.eval] using hc.symm

theorem sound3591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3591 node3591Labels = Sparse.eval nodeValue3591 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3591) = mixedMoment B node3591 node3591Labels := rfl
  simpa [nodeValue3591, Sparse.eval] using hc.symm

theorem sound3595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3595 node3595Labels = Sparse.eval nodeValue3595 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3595) = mixedMoment B node3595 node3595Labels := rfl
  simpa [nodeValue3595, Sparse.eval] using hc.symm

theorem sound3624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3624 node3624Labels = Sparse.eval nodeValue3624 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3624) = mixedMoment B node3624 node3624Labels := rfl
  simpa [nodeValue3624, Sparse.eval] using hc.symm

theorem sound3631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3631 node3631Labels = Sparse.eval nodeValue3631 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3631) = mixedMoment B node3631 node3631Labels := rfl
  simpa [nodeValue3631, Sparse.eval] using hc.symm

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

theorem sound3781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3781 node3781Labels = Sparse.eval nodeValue3781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3781) = mixedMoment B node3781 node3781Labels := rfl
  simpa [nodeValue3781, Sparse.eval] using hc.symm

theorem sound3794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3794 node3794Labels = Sparse.eval nodeValue3794 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3794) = mixedMoment B node3794 node3794Labels := rfl
  simpa [nodeValue3794, Sparse.eval] using hc.symm

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

theorem sound3845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3845 node3845Labels = Sparse.eval nodeValue3845 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3845) = mixedMoment B node3845 node3845Labels := rfl
  simpa [nodeValue3845, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4366 node4366Labels = Sparse.eval nodeValue4366 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4366) = mixedMoment B node4366 node4366Labels := rfl
  simpa [nodeValue4366, Sparse.eval] using hc.symm

theorem sound4367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4367 node4367Labels = Sparse.eval nodeValue4367 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4367) = mixedMoment B node4367 node4367Labels := rfl
  simpa [nodeValue4367, Sparse.eval] using hc.symm

theorem sound4368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4368 node4368Labels = Sparse.eval nodeValue4368 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4368) = mixedMoment B node4368 node4368Labels := rfl
  simpa [nodeValue4368, Sparse.eval] using hc.symm

theorem sound4372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4372 node4372Labels = Sparse.eval nodeValue4372 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4372) = mixedMoment B node4372 node4372Labels := rfl
  simpa [nodeValue4372, Sparse.eval] using hc.symm

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

theorem sound4475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4475 node4475Labels = Sparse.eval nodeValue4475 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4475) = mixedMoment B node4475 node4475Labels := rfl
  simpa [nodeValue4475, Sparse.eval] using hc.symm

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

theorem sound4971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4971 node4971Labels = Sparse.eval nodeValue4971 (mixedVector B) := by
  have h := singleton4971 B _hB
  rw [sound2807 B _hB _hF, sound3590 B _hB _hF] at h
  norm_num [nodeValue4971, nodeValue2807, nodeValue3590, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4972 node4972Labels = Sparse.eval nodeValue4972 (mixedVector B) := by
  have h := singleton4972 B _hB
  rw [sound2434 B _hB _hF, sound3457 B _hB _hF] at h
  norm_num [nodeValue4972, nodeValue2434, nodeValue3457, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4973 node4973Labels = Sparse.eval nodeValue4973 (mixedVector B) := by
  have h := singleton4973 B _hB
  rw [sound2817 B _hB _hF, sound3591 B _hB _hF] at h
  norm_num [nodeValue4973, nodeValue2817, nodeValue3591, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4977 node4977Labels = Sparse.eval nodeValue4977 (mixedVector B) := by
  have h := singleton4977 B _hB
  rw [sound2813 B _hB _hF, sound3595 B _hB _hF] at h
  norm_num [nodeValue4977, nodeValue2813, nodeValue3595, Sparse.eval] at h ⊢
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

theorem sound5034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5034 node5034Labels = Sparse.eval nodeValue5034 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5034) = mixedMoment B node5034 node5034Labels := rfl
  simpa [nodeValue5034, Sparse.eval] using hc.symm

theorem sound5042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5042 node5042Labels = Sparse.eval nodeValue5042 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5042) = mixedMoment B node5042 node5042Labels := rfl
  simpa [nodeValue5042, Sparse.eval] using hc.symm

theorem sound5044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5044 node5044Labels = Sparse.eval nodeValue5044 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5044) = mixedMoment B node5044 node5044Labels := rfl
  simpa [nodeValue5044, Sparse.eval] using hc.symm

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

theorem sound5086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5086 node5086Labels = Sparse.eval nodeValue5086 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5086) = mixedMoment B node5086 node5086Labels := rfl
  simpa [nodeValue5086, Sparse.eval] using hc.symm

theorem sound5109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5109 node5109Labels = Sparse.eval nodeValue5109 (mixedVector B) := by
  have h := singleton5109 B _hB
  rw [sound2519 B _hB _hF, sound3486 B _hB _hF] at h
  norm_num [nodeValue5109, nodeValue2519, nodeValue3486, Sparse.eval] at h ⊢
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

theorem sound5139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5139 node5139Labels = Sparse.eval nodeValue5139 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5139) = mixedMoment B node5139 node5139Labels := rfl
  simpa [nodeValue5139, Sparse.eval] using hc.symm

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

theorem sound5187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5187 node5187Labels = Sparse.eval nodeValue5187 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5187) = mixedMoment B node5187 node5187Labels := rfl
  simpa [nodeValue5187, Sparse.eval] using hc.symm

theorem sound5188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5188 node5188Labels = Sparse.eval nodeValue5188 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5188) = mixedMoment B node5188 node5188Labels := rfl
  simpa [nodeValue5188, Sparse.eval] using hc.symm

theorem sound5197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5197 node5197Labels = Sparse.eval nodeValue5197 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5197) = mixedMoment B node5197 node5197Labels := rfl
  simpa [nodeValue5197, Sparse.eval] using hc.symm

theorem sound5198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5198 node5198Labels = Sparse.eval nodeValue5198 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5198) = mixedMoment B node5198 node5198Labels := rfl
  simpa [nodeValue5198, Sparse.eval] using hc.symm

theorem sound5199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5199 node5199Labels = Sparse.eval nodeValue5199 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5199) = mixedMoment B node5199 node5199Labels := rfl
  simpa [nodeValue5199, Sparse.eval] using hc.symm

theorem sound5204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5204 node5204Labels = Sparse.eval nodeValue5204 (mixedVector B) := by
  have h := singleton5204 B _hB
  rw [sound2881 B _hB _hF, sound3624 B _hB _hF] at h
  norm_num [nodeValue5204, nodeValue2881, nodeValue3624, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5207 node5207Labels = Sparse.eval nodeValue5207 (mixedVector B) := by
  have h := singleton5207 B _hB
  rw [sound2889 B _hB _hF, sound3631 B _hB _hF] at h
  norm_num [nodeValue5207, nodeValue2889, nodeValue3631, Sparse.eval] at h ⊢
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

theorem sound5267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5267 node5267Labels = Sparse.eval nodeValue5267 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5267) = mixedMoment B node5267 node5267Labels := rfl
  simpa [nodeValue5267, Sparse.eval] using hc.symm

theorem sound5299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5299 node5299Labels = Sparse.eval nodeValue5299 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5299) = mixedMoment B node5299 node5299Labels := rfl
  simpa [nodeValue5299, Sparse.eval] using hc.symm

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

theorem zero5367 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5367 node5367Labels = 0 := by
  exact mixedMoment_order_one B hB node5367 node5367Labels 1
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

theorem sound5367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5367 node5367Labels = Sparse.eval nodeValue5367 (mixedVector B) := by
  simpa only [nodeValue5367, Sparse.eval_nil] using zero5367 B _hB _hF

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

theorem zero5413 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5413 node5413Labels = 0 := by
  exact mixedMoment_order_one B hB node5413 node5413Labels 1
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

theorem sound5395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5395 node5395Labels = Sparse.eval nodeValue5395 (mixedVector B) := by
  have h := singleton5395 B _hB
  rw [sound3781 B _hB _hF, sound3794 B _hB _hF] at h
  norm_num [nodeValue5395, nodeValue3781, nodeValue3794, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5413 node5413Labels = Sparse.eval nodeValue5413 (mixedVector B) := by
  simpa only [nodeValue5413, Sparse.eval_nil] using zero5413 B _hB _hF

theorem sound5428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5428 node5428Labels = Sparse.eval nodeValue5428 (mixedVector B) := by
  have h := singleton5428 B _hB
  rw [sound3845 B _hB _hF] at h
  norm_num [nodeValue5428, nodeValue3845, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources74
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2386 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2386 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2386 + difference 0 1) (sourceB2386 + difference 1 0) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2386 + difference 0 1) (sourceB2386 + difference 1 0) sourceC2386) = raw32669 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32669; decide +kernel
    rw [ha]
    exact (canonical32669 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2386 + difference 0 2) (sourceB2386 + difference 2 0) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA2386 + difference 0 2) (sourceB2386 + difference 2 0) sourceC2386) = raw32670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32670; decide +kernel
    rw [ha]
    exact (canonical32670 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2386 + difference 0 3) (sourceB2386 + difference 3 0) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA2386 + difference 0 3) (sourceB2386 + difference 3 0) sourceC2386) = raw32671 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32671; decide +kernel
    rw [ha]
    exact (canonical32671 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2386 + difference 0 4) (sourceB2386 + difference 4 0) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5413) := by
    have ha : (tripleCharges (sourceA2386 + difference 0 4) (sourceB2386 + difference 4 0) sourceC2386) = raw32672 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32672; decide +kernel
    rw [ha]
    exact (canonical32672 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2386 + difference 0 5) (sourceB2386 + difference 5 0) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA2386 + difference 0 5) (sourceB2386 + difference 5 0) sourceC2386) = raw32673 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32673; decide +kernel
    rw [ha]
    exact (canonical32673 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2386 + difference 1 0) (sourceB2386 + difference 0 1) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4475) := by
    have ha : (tripleCharges (sourceA2386 + difference 1 0) (sourceB2386 + difference 0 1) sourceC2386) = raw32674 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32674; decide +kernel
    rw [ha]
    exact (canonical32674 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2386 + difference 1 2) (sourceB2386 + difference 2 1) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5086) := by
    have ha : (tripleCharges (sourceA2386 + difference 1 2) (sourceB2386 + difference 2 1) sourceC2386) = raw32675 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32675; decide +kernel
    rw [ha]
    exact (canonical32675 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2386 + difference 1 3) (sourceB2386 + difference 3 1) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA2386 + difference 1 3) (sourceB2386 + difference 3 1) sourceC2386) = raw32676 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32676; decide +kernel
    rw [ha]
    exact (canonical32676 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2386 + difference 1 4) (sourceB2386 + difference 4 1) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA2386 + difference 1 4) (sourceB2386 + difference 4 1) sourceC2386) = raw32677 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32677; decide +kernel
    rw [ha]
    exact (canonical32677 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2386 + difference 1 5) (sourceB2386 + difference 5 1) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA2386 + difference 1 5) (sourceB2386 + difference 5 1) sourceC2386) = raw32678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32678; decide +kernel
    rw [ha]
    exact (canonical32678 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2386 + difference 2 0) (sourceB2386 + difference 0 2) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4366) := by
    have ha : (tripleCharges (sourceA2386 + difference 2 0) (sourceB2386 + difference 0 2) sourceC2386) = raw32679 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32679; decide +kernel
    rw [ha]
    exact (canonical32679 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2386 + difference 2 1) (sourceB2386 + difference 1 2) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4971) := by
    have ha : (tripleCharges (sourceA2386 + difference 2 1) (sourceB2386 + difference 1 2) sourceC2386) = raw32680 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32680; decide +kernel
    rw [ha]
    exact (canonical32680 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2386 + difference 2 3) (sourceB2386 + difference 3 2) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5187) := by
    have ha : (tripleCharges (sourceA2386 + difference 2 3) (sourceB2386 + difference 3 2) sourceC2386) = raw32681 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32681; decide +kernel
    rw [ha]
    exact (canonical32681 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2386 + difference 2 4) (sourceB2386 + difference 4 2) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA2386 + difference 2 4) (sourceB2386 + difference 4 2) sourceC2386) = raw32682 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32682; decide +kernel
    rw [ha]
    exact (canonical32682 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2386 + difference 2 5) (sourceB2386 + difference 5 2) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5197) := by
    have ha : (tripleCharges (sourceA2386 + difference 2 5) (sourceB2386 + difference 5 2) sourceC2386) = raw32683 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32683; decide +kernel
    rw [ha]
    exact (canonical32683 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2386 + difference 3 0) (sourceB2386 + difference 0 3) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4372) := by
    have ha : (tripleCharges (sourceA2386 + difference 3 0) (sourceB2386 + difference 0 3) sourceC2386) = raw32684 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32684; decide +kernel
    rw [ha]
    exact (canonical32684 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2386 + difference 3 1) (sourceB2386 + difference 1 3) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4977) := by
    have ha : (tripleCharges (sourceA2386 + difference 3 1) (sourceB2386 + difference 1 3) sourceC2386) = raw32685 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32685; decide +kernel
    rw [ha]
    exact (canonical32685 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2386 + difference 3 2) (sourceB2386 + difference 2 3) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5044) := by
    have ha : (tripleCharges (sourceA2386 + difference 3 2) (sourceB2386 + difference 2 3) sourceC2386) = raw32686 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32686; decide +kernel
    rw [ha]
    exact (canonical32686 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2386 + difference 3 4) (sourceB2386 + difference 4 3) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA2386 + difference 3 4) (sourceB2386 + difference 4 3) sourceC2386) = raw32687 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32687; decide +kernel
    rw [ha]
    exact (canonical32687 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2386 + difference 3 5) (sourceB2386 + difference 5 3) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5199) := by
    have ha : (tripleCharges (sourceA2386 + difference 3 5) (sourceB2386 + difference 5 3) sourceC2386) = raw32688 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32688; decide +kernel
    rw [ha]
    exact (canonical32688 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2386 + difference 4 0) (sourceB2386 + difference 0 4) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4368) := by
    have ha : (tripleCharges (sourceA2386 + difference 4 0) (sourceB2386 + difference 0 4) sourceC2386) = raw32689 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32689; decide +kernel
    rw [ha]
    exact (canonical32689 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2386 + difference 4 1) (sourceB2386 + difference 1 4) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4973) := by
    have ha : (tripleCharges (sourceA2386 + difference 4 1) (sourceB2386 + difference 1 4) sourceC2386) = raw32690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32690; decide +kernel
    rw [ha]
    exact (canonical32690 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2386 + difference 4 2) (sourceB2386 + difference 2 4) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5042) := by
    have ha : (tripleCharges (sourceA2386 + difference 4 2) (sourceB2386 + difference 2 4) sourceC2386) = raw32691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32691; decide +kernel
    rw [ha]
    exact (canonical32691 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2386 + difference 4 3) (sourceB2386 + difference 3 4) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5188) := by
    have ha : (tripleCharges (sourceA2386 + difference 4 3) (sourceB2386 + difference 3 4) sourceC2386) = raw32692 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32692; decide +kernel
    rw [ha]
    exact (canonical32692 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2386 + difference 4 5) (sourceB2386 + difference 5 4) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5198) := by
    have ha : (tripleCharges (sourceA2386 + difference 4 5) (sourceB2386 + difference 5 4) sourceC2386) = raw32693 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32693; decide +kernel
    rw [ha]
    exact (canonical32693 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2386 + difference 5 0) (sourceB2386 + difference 0 5) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4367) := by
    have ha : (tripleCharges (sourceA2386 + difference 5 0) (sourceB2386 + difference 0 5) sourceC2386) = raw32694 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32694; decide +kernel
    rw [ha]
    exact (canonical32694 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2386 + difference 5 1) (sourceB2386 + difference 1 5) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4972) := by
    have ha : (tripleCharges (sourceA2386 + difference 5 1) (sourceB2386 + difference 1 5) sourceC2386) = raw32695 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32695; decide +kernel
    rw [ha]
    exact (canonical32695 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2386 + difference 5 2) (sourceB2386 + difference 2 5) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5034) := by
    have ha : (tripleCharges (sourceA2386 + difference 5 2) (sourceB2386 + difference 2 5) sourceC2386) = raw32696 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32696; decide +kernel
    rw [ha]
    exact (canonical32696 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2386 + difference 5 3) (sourceB2386 + difference 3 5) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA2386 + difference 5 3) (sourceB2386 + difference 3 5) sourceC2386) = raw32697 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32697; decide +kernel
    rw [ha]
    exact (canonical32697 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2386 + difference 5 4) (sourceB2386 + difference 4 5) sourceC2386) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA2386 + difference 5 4) (sourceB2386 + difference 4 5) sourceC2386) = raw32698 := by
      apply Matrix.ext; unfold tripleCharges sourceA2386 sourceB2386 sourceC2386 difference raw32698; decide +kernel
    rw [ha]
    exact (canonical32698 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2386 sourceB2386 sourceC2386
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2386, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1937 : Integer.Sparse.reindex keyMap MixedData.row1937 = numericRow1937 := by decide +kernel

theorem numericCheck1937 (x : Master → ℝ) : Integer.Sparse.eval numericRow1937 x =
    (4 : ℝ) * reducedSource1937 x := by
  norm_num [numericRow1937, reducedSource1937, Integer.Sparse.eval, Sparse.eval, nodeValue4366, nodeValue4367, nodeValue4368, nodeValue4372, nodeValue4475, nodeValue4971, nodeValue4972, nodeValue4973, nodeValue4977, nodeValue5034, nodeValue5042, nodeValue5044, nodeValue5086, nodeValue5109, nodeValue5139, nodeValue5187, nodeValue5188, nodeValue5197, nodeValue5198, nodeValue5199, nodeValue5204, nodeValue5207, nodeValue5267, nodeValue5299, nodeValue5302, nodeValue5367, nodeValue5395, nodeValue5413, nodeValue5428, nodeValue5473]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1937 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1937 (mixedVector B) = 0 := by
  have h4366 : mixedVector B (Sum.inr 4366) = Sparse.eval nodeValue4366 (mixedVector B) := by
    change mixedMoment B node4366 node4366Labels = _
    exact sound4366 B hB hF
  have h4367 : mixedVector B (Sum.inr 4367) = Sparse.eval nodeValue4367 (mixedVector B) := by
    change mixedMoment B node4367 node4367Labels = _
    exact sound4367 B hB hF
  have h4368 : mixedVector B (Sum.inr 4368) = Sparse.eval nodeValue4368 (mixedVector B) := by
    change mixedMoment B node4368 node4368Labels = _
    exact sound4368 B hB hF
  have h4372 : mixedVector B (Sum.inr 4372) = Sparse.eval nodeValue4372 (mixedVector B) := by
    change mixedMoment B node4372 node4372Labels = _
    exact sound4372 B hB hF
  have h4475 : mixedVector B (Sum.inr 4475) = Sparse.eval nodeValue4475 (mixedVector B) := by
    change mixedMoment B node4475 node4475Labels = _
    exact sound4475 B hB hF
  have h4971 : mixedVector B (Sum.inr 4971) = Sparse.eval nodeValue4971 (mixedVector B) := by
    change mixedMoment B node4971 node4971Labels = _
    exact sound4971 B hB hF
  have h4972 : mixedVector B (Sum.inr 4972) = Sparse.eval nodeValue4972 (mixedVector B) := by
    change mixedMoment B node4972 node4972Labels = _
    exact sound4972 B hB hF
  have h4973 : mixedVector B (Sum.inr 4973) = Sparse.eval nodeValue4973 (mixedVector B) := by
    change mixedMoment B node4973 node4973Labels = _
    exact sound4973 B hB hF
  have h4977 : mixedVector B (Sum.inr 4977) = Sparse.eval nodeValue4977 (mixedVector B) := by
    change mixedMoment B node4977 node4977Labels = _
    exact sound4977 B hB hF
  have h5034 : mixedVector B (Sum.inr 5034) = Sparse.eval nodeValue5034 (mixedVector B) := by
    change mixedMoment B node5034 node5034Labels = _
    exact sound5034 B hB hF
  have h5042 : mixedVector B (Sum.inr 5042) = Sparse.eval nodeValue5042 (mixedVector B) := by
    change mixedMoment B node5042 node5042Labels = _
    exact sound5042 B hB hF
  have h5044 : mixedVector B (Sum.inr 5044) = Sparse.eval nodeValue5044 (mixedVector B) := by
    change mixedMoment B node5044 node5044Labels = _
    exact sound5044 B hB hF
  have h5086 : mixedVector B (Sum.inr 5086) = Sparse.eval nodeValue5086 (mixedVector B) := by
    change mixedMoment B node5086 node5086Labels = _
    exact sound5086 B hB hF
  have h5109 : mixedVector B (Sum.inr 5109) = Sparse.eval nodeValue5109 (mixedVector B) := by
    change mixedMoment B node5109 node5109Labels = _
    exact sound5109 B hB hF
  have h5139 : mixedVector B (Sum.inr 5139) = Sparse.eval nodeValue5139 (mixedVector B) := by
    change mixedMoment B node5139 node5139Labels = _
    exact sound5139 B hB hF
  have h5187 : mixedVector B (Sum.inr 5187) = Sparse.eval nodeValue5187 (mixedVector B) := by
    change mixedMoment B node5187 node5187Labels = _
    exact sound5187 B hB hF
  have h5188 : mixedVector B (Sum.inr 5188) = Sparse.eval nodeValue5188 (mixedVector B) := by
    change mixedMoment B node5188 node5188Labels = _
    exact sound5188 B hB hF
  have h5197 : mixedVector B (Sum.inr 5197) = Sparse.eval nodeValue5197 (mixedVector B) := by
    change mixedMoment B node5197 node5197Labels = _
    exact sound5197 B hB hF
  have h5198 : mixedVector B (Sum.inr 5198) = Sparse.eval nodeValue5198 (mixedVector B) := by
    change mixedMoment B node5198 node5198Labels = _
    exact sound5198 B hB hF
  have h5199 : mixedVector B (Sum.inr 5199) = Sparse.eval nodeValue5199 (mixedVector B) := by
    change mixedMoment B node5199 node5199Labels = _
    exact sound5199 B hB hF
  have h5204 : mixedVector B (Sum.inr 5204) = Sparse.eval nodeValue5204 (mixedVector B) := by
    change mixedMoment B node5204 node5204Labels = _
    exact sound5204 B hB hF
  have h5207 : mixedVector B (Sum.inr 5207) = Sparse.eval nodeValue5207 (mixedVector B) := by
    change mixedMoment B node5207 node5207Labels = _
    exact sound5207 B hB hF
  have h5267 : mixedVector B (Sum.inr 5267) = Sparse.eval nodeValue5267 (mixedVector B) := by
    change mixedMoment B node5267 node5267Labels = _
    exact sound5267 B hB hF
  have h5299 : mixedVector B (Sum.inr 5299) = Sparse.eval nodeValue5299 (mixedVector B) := by
    change mixedMoment B node5299 node5299Labels = _
    exact sound5299 B hB hF
  have h5302 : mixedVector B (Sum.inr 5302) = Sparse.eval nodeValue5302 (mixedVector B) := by
    change mixedMoment B node5302 node5302Labels = _
    exact sound5302 B hB hF
  have h5367 : mixedVector B (Sum.inr 5367) = Sparse.eval nodeValue5367 (mixedVector B) := by
    change mixedMoment B node5367 node5367Labels = _
    exact sound5367 B hB hF
  have h5395 : mixedVector B (Sum.inr 5395) = Sparse.eval nodeValue5395 (mixedVector B) := by
    change mixedMoment B node5395 node5395Labels = _
    exact sound5395 B hB hF
  have h5413 : mixedVector B (Sum.inr 5413) = Sparse.eval nodeValue5413 (mixedVector B) := by
    change mixedMoment B node5413 node5413Labels = _
    exact sound5413 B hB hF
  have h5428 : mixedVector B (Sum.inr 5428) = Sparse.eval nodeValue5428 (mixedVector B) := by
    change mixedMoment B node5428 node5428Labels = _
    exact sound5428 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  simpa only [sourceForm2386, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4366, h4367, h4368, h4372, h4475, h4971, h4972, h4973, h4977, h5034, h5042, h5044, h5086, h5109, h5139, h5187, h5188, h5197, h5198, h5199, h5204, h5207, h5267, h5299, h5302, h5367, h5395, h5413, h5428, h5473, reducedSource1937] using sourceEq2386 B hB

theorem rowSound1937_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1937 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1937, numericCheck1937, reducedZero1937 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937_e_oai
