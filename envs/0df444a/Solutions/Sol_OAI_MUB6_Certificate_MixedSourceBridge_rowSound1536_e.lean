-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1536_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:45:27.747033+00:00
-- url     : https://prove2.me/submissions/931ee09d-b445-4576-8ea1-1a45935a64fd

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1281 raw1281Labels = mixedMoment B node4489 node4489Labels := by
  calc
    mixedMoment B raw1281 raw1281Labels = mixedMoment B raw1281step0 raw1281step0Labels := by
      have ha : raw1281step0 = (fun i j => raw1281 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1281step0 raw1281; decide +kernel
      have hl : raw1281step0Labels = raw1281Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1281 raw1281Labels permutation32 permutation4
    mixedMoment B raw1281step0 raw1281step0Labels = mixedMoment B raw1281step1 raw1281step1Labels := by
      have ha : raw1281step1 = raw1281step0 := by apply Matrix.ext; unfold raw1281step1 raw1281step0; decide +kernel
      have hl : raw1281step0Labels = labelEmbedding7 ∘ raw1281step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1281step0 raw1281step0Labels raw1281step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4489 node4489Labels := by rfl

theorem canonical1282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1282 raw1282Labels = mixedMoment B node1073 node1073Labels := by
  calc
    mixedMoment B raw1282 raw1282Labels = mixedMoment B raw1282step0 raw1282step0Labels := by
      have ha : raw1282step0 = (fun i j => raw1282 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1282step0 raw1282; decide +kernel
      have hl : raw1282step0Labels = raw1282Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1282 raw1282Labels permutation32 permutation4
    _ = mixedMoment B node1073 node1073Labels := by rfl

theorem canonical1283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1283 raw1283Labels = mixedMoment B node1648 node1648Labels := by
  calc
    mixedMoment B raw1283 raw1283Labels = mixedMoment B raw1283step0 raw1283step0Labels := by
      have ha : raw1283step0 = (fun i j => raw1283 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1283step0 raw1283; decide +kernel
      have hl : raw1283step0Labels = raw1283Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1283 raw1283Labels permutation32 permutation6
    mixedMoment B raw1283step0 raw1283step0Labels = mixedMoment B raw1283step1 raw1283step1Labels := by
      have ha : raw1283step1 = -raw1283step0 := by apply Matrix.ext; change ∀ i j, raw1283step1 i j = -(raw1283step0 i j); unfold raw1283step1 raw1283step0; decide +kernel
      have hl : raw1283step1Labels = raw1283step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1283step1 raw1283step1Labels = mixedMoment B raw1283step2 raw1283step2Labels := by
      have ha : raw1283step2 = raw1283step1 := by apply Matrix.ext; unfold raw1283step2 raw1283step1; decide +kernel
      have hl : raw1283step1Labels = labelEmbedding1 ∘ raw1283step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1283step1 raw1283step1Labels raw1283step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1648 node1648Labels := by rfl

theorem canonical1293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1293 raw1293Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw1293 raw1293Labels = mixedMoment B raw1293step0 raw1293step0Labels := by
      have ha : raw1293step0 = (fun i j => raw1293 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1293step0 raw1293; decide +kernel
      have hl : raw1293step0Labels = raw1293Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1293 raw1293Labels permutation32 permutation4
    mixedMoment B raw1293step0 raw1293step0Labels = mixedMoment B raw1293step1 raw1293step1Labels := by
      have ha : raw1293step1 = raw1293step0 := by apply Matrix.ext; unfold raw1293step1 raw1293step0; decide +kernel
      have hl : raw1293step0Labels = labelEmbedding7 ∘ raw1293step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1293step0 raw1293step0Labels raw1293step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

theorem canonical1294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1294 raw1294Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw1294 raw1294Labels = mixedMoment B raw1294step0 raw1294step0Labels := by
      have ha : raw1294step0 = (fun i j => raw1294 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1294step0 raw1294; decide +kernel
      have hl : raw1294step0Labels = raw1294Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1294 raw1294Labels permutation32 permutation4
    _ = mixedMoment B node1079 node1079Labels := by rfl

theorem canonical1295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1295 raw1295Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw1295 raw1295Labels = mixedMoment B raw1295step0 raw1295step0Labels := by
      have ha : raw1295step0 = (fun i j => raw1295 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1295step0 raw1295; decide +kernel
      have hl : raw1295step0Labels = raw1295Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1295 raw1295Labels permutation32 permutation6
    mixedMoment B raw1295step0 raw1295step0Labels = mixedMoment B raw1295step1 raw1295step1Labels := by
      have ha : raw1295step1 = -raw1295step0 := by apply Matrix.ext; change ∀ i j, raw1295step1 i j = -(raw1295step0 i j); unfold raw1295step1 raw1295step0; decide +kernel
      have hl : raw1295step1Labels = raw1295step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1295step1 raw1295step1Labels = mixedMoment B raw1295step2 raw1295step2Labels := by
      have ha : raw1295step2 = raw1295step1 := by apply Matrix.ext; unfold raw1295step2 raw1295step1; decide +kernel
      have hl : raw1295step1Labels = labelEmbedding1 ∘ raw1295step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1295step1 raw1295step1Labels raw1295step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1708 node1708Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical204
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26214 raw26214Labels = mixedMoment B node4489 node4489Labels := by
  calc
    mixedMoment B raw26214 raw26214Labels = mixedMoment B raw26214step0 raw26214step0Labels := by
      have hz : ∀ j, raw26214 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26214step0 = (fun i j => raw26214 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26214step0 raw26214; decide +kernel
      have hl : raw26214step0Labels = raw26214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26214 raw26214Labels permutation346 hz
    mixedMoment B raw26214step0 raw26214step0Labels = mixedMoment B raw26214step1 raw26214step1Labels := by
      have ha : raw26214step1 = (fun i j => raw26214step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26214step1 raw26214step0; decide +kernel
      have hl : raw26214step1Labels = raw26214step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26214step0 raw26214step0Labels permutation32 permutation7
    mixedMoment B raw26214step1 raw26214step1Labels = mixedMoment B raw26214step2 raw26214step2Labels := by
      have ha : raw26214step2 = -raw26214step1 := by apply Matrix.ext; change ∀ i j, raw26214step2 i j = -(raw26214step1 i j); unfold raw26214step2 raw26214step1; decide +kernel
      have hl : raw26214step2Labels = raw26214step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26214step2 raw26214step2Labels = mixedMoment B raw26214step3 raw26214step3Labels := by
      have ha : raw26214step3 = raw26214step2 := by apply Matrix.ext; unfold raw26214step3 raw26214step2; decide +kernel
      have hl : raw26214step2Labels = labelEmbedding10 ∘ raw26214step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26214step2 raw26214step2Labels raw26214step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4489 node4489Labels := by rfl

theorem canonical26215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26215 raw26215Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw26215 raw26215Labels = mixedMoment B raw26215step0 raw26215step0Labels := by
      have ha : raw26215step0 = (fun i j => raw26215 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26215step0 raw26215; decide +kernel
      have hl : raw26215step0Labels = raw26215Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26215 raw26215Labels permutation176 permutation7
    mixedMoment B raw26215step0 raw26215step0Labels = mixedMoment B raw26215step1 raw26215step1Labels := by
      have ha : raw26215step1 = -raw26215step0 := by apply Matrix.ext; change ∀ i j, raw26215step1 i j = -(raw26215step0 i j); unfold raw26215step1 raw26215step0; decide +kernel
      have hl : raw26215step1Labels = raw26215step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26215step1 raw26215step1Labels = mixedMoment B raw26215step2 raw26215step2Labels := by
      have ha : raw26215step2 = raw26215step1 := by apply Matrix.ext; unfold raw26215step2 raw26215step1; decide +kernel
      have hl : raw26215step1Labels = labelEmbedding10 ∘ raw26215step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26215step1 raw26215step1Labels raw26215step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

theorem canonical26216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26216 raw26216Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw26216 raw26216Labels = mixedMoment B raw26216step0 raw26216step0Labels := by
      have hz : ∀ j, raw26216 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26216step0 = (fun i j => raw26216 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26216step0 raw26216; decide +kernel
      have hl : raw26216step0Labels = raw26216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26216 raw26216Labels permutation346 hz
    mixedMoment B raw26216step0 raw26216step0Labels = mixedMoment B raw26216step1 raw26216step1Labels := by
      have ha : raw26216step1 = (fun i j => raw26216step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26216step1 raw26216step0; decide +kernel
      have hl : raw26216step1Labels = raw26216step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26216step0 raw26216step0Labels permutation32 permutation7
    mixedMoment B raw26216step1 raw26216step1Labels = mixedMoment B raw26216step2 raw26216step2Labels := by
      have ha : raw26216step2 = -raw26216step1 := by apply Matrix.ext; change ∀ i j, raw26216step2 i j = -(raw26216step1 i j); unfold raw26216step2 raw26216step1; decide +kernel
      have hl : raw26216step2Labels = raw26216step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26216step2 raw26216step2Labels = mixedMoment B raw26216step3 raw26216step3Labels := by
      have ha : raw26216step3 = raw26216step2 := by apply Matrix.ext; unfold raw26216step3 raw26216step2; decide +kernel
      have hl : raw26216step2Labels = labelEmbedding10 ∘ raw26216step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26216step2 raw26216step2Labels raw26216step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

theorem canonical26217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26217 raw26217Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw26217 raw26217Labels = mixedMoment B raw26217step0 raw26217step0Labels := by
      have hz : ∀ j, raw26217 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26217step0 = (fun i j => raw26217 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26217step0 raw26217; decide +kernel
      have hl : raw26217step0Labels = raw26217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26217 raw26217Labels permutation346 hz
    mixedMoment B raw26217step0 raw26217step0Labels = mixedMoment B raw26217step1 raw26217step1Labels := by
      have ha : raw26217step1 = (fun i j => raw26217step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26217step1 raw26217step0; decide +kernel
      have hl : raw26217step1Labels = raw26217step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26217step0 raw26217step0Labels permutation34 permutation7
    mixedMoment B raw26217step1 raw26217step1Labels = mixedMoment B raw26217step2 raw26217step2Labels := by
      have ha : raw26217step2 = -raw26217step1 := by apply Matrix.ext; change ∀ i j, raw26217step2 i j = -(raw26217step1 i j); unfold raw26217step2 raw26217step1; decide +kernel
      have hl : raw26217step2Labels = raw26217step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26217step2 raw26217step2Labels = mixedMoment B raw26217step3 raw26217step3Labels := by
      have ha : raw26217step3 = raw26217step2 := by apply Matrix.ext; unfold raw26217step3 raw26217step2; decide +kernel
      have hl : raw26217step2Labels = labelEmbedding10 ∘ raw26217step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26217step2 raw26217step2Labels raw26217step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

theorem canonical26218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26218 raw26218Labels = mixedMoment B node4497 node4497Labels := by
  calc
    mixedMoment B raw26218 raw26218Labels = mixedMoment B raw26218step0 raw26218step0Labels := by
      have hz : ∀ j, raw26218 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26218step0 = (fun i j => raw26218 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26218step0 raw26218; decide +kernel
      have hl : raw26218step0Labels = raw26218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26218 raw26218Labels permutation346 hz
    mixedMoment B raw26218step0 raw26218step0Labels = mixedMoment B raw26218step1 raw26218step1Labels := by
      have ha : raw26218step1 = (fun i j => raw26218step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26218step1 raw26218step0; decide +kernel
      have hl : raw26218step1Labels = raw26218step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26218step0 raw26218step0Labels permutation32 permutation7
    mixedMoment B raw26218step1 raw26218step1Labels = mixedMoment B raw26218step2 raw26218step2Labels := by
      have ha : raw26218step2 = -raw26218step1 := by apply Matrix.ext; change ∀ i j, raw26218step2 i j = -(raw26218step1 i j); unfold raw26218step2 raw26218step1; decide +kernel
      have hl : raw26218step2Labels = raw26218step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26218step2 raw26218step2Labels = mixedMoment B raw26218step3 raw26218step3Labels := by
      have ha : raw26218step3 = raw26218step2 := by apply Matrix.ext; unfold raw26218step3 raw26218step2; decide +kernel
      have hl : raw26218step2Labels = labelEmbedding10 ∘ raw26218step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26218step2 raw26218step2Labels raw26218step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4497 node4497Labels := by rfl

theorem canonical26219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26219 raw26219Labels = mixedMoment B node4125 node4125Labels := by
  calc
    mixedMoment B raw26219 raw26219Labels = mixedMoment B raw26219step0 raw26219step0Labels := by
      have hz : ∀ j, raw26219 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26219step0 = (fun i j => raw26219 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26219step0 raw26219; decide +kernel
      have hl : raw26219step0Labels = raw26219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26219 raw26219Labels permutation346 hz
    _ = mixedMoment B node4125 node4125Labels := by rfl

theorem canonical26220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26220 raw26220Labels = mixedMoment B node4216 node4216Labels := by
  calc
    mixedMoment B raw26220 raw26220Labels = mixedMoment B raw26220step0 raw26220step0Labels := by
      have ha : raw26220step0 = (fun i j => raw26220 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26220step0 raw26220; decide +kernel
      have hl : raw26220step0Labels = raw26220Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26220 raw26220Labels permutation176 permutation2
    _ = mixedMoment B node4216 node4216Labels := by rfl

theorem canonical26221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26221 raw26221Labels = mixedMoment B node4267 node4267Labels := by
  calc
    mixedMoment B raw26221 raw26221Labels = mixedMoment B raw26221step0 raw26221step0Labels := by
      have hz : ∀ j, raw26221 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26221step0 = (fun i j => raw26221 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26221step0 raw26221; decide +kernel
      have hl : raw26221step0Labels = raw26221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26221 raw26221Labels permutation346 hz
    mixedMoment B raw26221step0 raw26221step0Labels = mixedMoment B raw26221step1 raw26221step1Labels := by
      have ha : raw26221step1 = (fun i j => raw26221step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26221step1 raw26221step0; decide +kernel
      have hl : raw26221step1Labels = raw26221step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26221step0 raw26221step0Labels permutation38 permutation2
    _ = mixedMoment B node4267 node4267Labels := by rfl

theorem canonical26222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26222 raw26222Labels = mixedMoment B node4267 node4267Labels := by
  calc
    mixedMoment B raw26222 raw26222Labels = mixedMoment B raw26222step0 raw26222step0Labels := by
      have hz : ∀ j, raw26222 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26222step0 = (fun i j => raw26222 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26222step0 raw26222; decide +kernel
      have hl : raw26222step0Labels = raw26222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26222 raw26222Labels permutation346 hz
    mixedMoment B raw26222step0 raw26222step0Labels = mixedMoment B raw26222step1 raw26222step1Labels := by
      have ha : raw26222step1 = (fun i j => raw26222step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26222step1 raw26222step0; decide +kernel
      have hl : raw26222step1Labels = raw26222step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26222step0 raw26222step0Labels permutation44 permutation2
    _ = mixedMoment B node4267 node4267Labels := by rfl

theorem canonical26223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26223 raw26223Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw26223 raw26223Labels = mixedMoment B raw26223step0 raw26223step0Labels := by
      have hz : ∀ j, raw26223 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26223step0 = (fun i j => raw26223 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26223step0 raw26223; decide +kernel
      have hl : raw26223step0Labels = raw26223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26223 raw26223Labels permutation346 hz
    mixedMoment B raw26223step0 raw26223step0Labels = mixedMoment B raw26223step1 raw26223step1Labels := by
      have hz : ∀ i, raw26223step0 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw26223step1 = (fun i j => raw26223step0 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw26223step1 raw26223step0; decide +kernel
      have hl : raw26223step1Labels = (fun j => raw26223step0Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26223step0 raw26223step0Labels permutation4 hz
    mixedMoment B raw26223step1 raw26223step1Labels = mixedMoment B raw26223step2 raw26223step2Labels := by
      have ha : raw26223step2 = raw26223step1 := by apply Matrix.ext; unfold raw26223step2 raw26223step1; decide +kernel
      have hl : raw26223step1Labels = labelEmbedding2 ∘ raw26223step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26223step1 raw26223step1Labels raw26223step2Labels labelEmbedding2 hl
    _ = mixedMoment B node4068 node4068Labels := by rfl

theorem canonical26224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26224 raw26224Labels = mixedMoment B node4100 node4100Labels := by
  calc
    _ = mixedMoment B node4100 node4100Labels := by rfl

theorem canonical26225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26225 raw26225Labels = mixedMoment B node4232 node4232Labels := by
  calc
    _ = mixedMoment B node4232 node4232Labels := by rfl

theorem canonical26226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26226 raw26226Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw26226 raw26226Labels = mixedMoment B raw26226step0 raw26226step0Labels := by
      have ha : raw26226step0 = (fun i j => raw26226 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26226step0 raw26226; decide +kernel
      have hl : raw26226step0Labels = raw26226Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26226 raw26226Labels permutation158 permutation2
    _ = mixedMoment B node4249 node4249Labels := by rfl

theorem canonical26227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26227 raw26227Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw26227 raw26227Labels = mixedMoment B raw26227step0 raw26227step0Labels := by
      have ha : raw26227step0 = (fun i j => raw26227 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26227step0 raw26227; decide +kernel
      have hl : raw26227step0Labels = raw26227Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26227 raw26227Labels permutation164 permutation2
    _ = mixedMoment B node4249 node4249Labels := by rfl

theorem canonical26228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26228 raw26228Labels = mixedMoment B node4263 node4263Labels := by
  calc
    _ = mixedMoment B node4263 node4263Labels := by rfl

theorem canonical26229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26229 raw26229Labels = mixedMoment B node4107 node4107Labels := by
  calc
    mixedMoment B raw26229 raw26229Labels = mixedMoment B raw26229step0 raw26229step0Labels := by
      have hz : ∀ j, raw26229 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26229step0 = (fun i j => raw26229 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26229step0 raw26229; decide +kernel
      have hl : raw26229step0Labels = raw26229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26229 raw26229Labels permutation346 hz
    mixedMoment B raw26229step0 raw26229step0Labels = mixedMoment B raw26229step1 raw26229step1Labels := by
      have ha : raw26229step1 = (fun i j => raw26229step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26229step1 raw26229step0; decide +kernel
      have hl : raw26229step1Labels = raw26229step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26229step0 raw26229step0Labels permutation34 permutation2
    _ = mixedMoment B node4107 node4107Labels := by rfl

theorem canonical26230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26230 raw26230Labels = mixedMoment B node4239 node4239Labels := by
  calc
    mixedMoment B raw26230 raw26230Labels = mixedMoment B raw26230step0 raw26230step0Labels := by
      have hz : ∀ j, raw26230 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26230step0 = (fun i j => raw26230 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26230step0 raw26230; decide +kernel
      have hl : raw26230step0Labels = raw26230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26230 raw26230Labels permutation346 hz
    mixedMoment B raw26230step0 raw26230step0Labels = mixedMoment B raw26230step1 raw26230step1Labels := by
      have ha : raw26230step1 = (fun i j => raw26230step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26230step1 raw26230step0; decide +kernel
      have hl : raw26230step1Labels = raw26230step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26230step0 raw26230step0Labels permutation34 permutation2
    _ = mixedMoment B node4239 node4239Labels := by rfl

theorem canonical26231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26231 raw26231Labels = mixedMoment B node4201 node4201Labels := by
  calc
    mixedMoment B raw26231 raw26231Labels = mixedMoment B raw26231step0 raw26231step0Labels := by
      have ha : raw26231step0 = (fun i j => raw26231 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26231step0 raw26231; decide +kernel
      have hl : raw26231step0Labels = raw26231Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26231 raw26231Labels permutation178 permutation2
    _ = mixedMoment B node4201 node4201Labels := by rfl

theorem canonical26232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26232 raw26232Labels = mixedMoment B node4256 node4256Labels := by
  calc
    mixedMoment B raw26232 raw26232Labels = mixedMoment B raw26232step0 raw26232step0Labels := by
      have hz : ∀ j, raw26232 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26232step0 = (fun i j => raw26232 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26232step0 raw26232; decide +kernel
      have hl : raw26232step0Labels = raw26232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26232 raw26232Labels permutation346 hz
    mixedMoment B raw26232step0 raw26232step0Labels = mixedMoment B raw26232step1 raw26232step1Labels := by
      have ha : raw26232step1 = (fun i j => raw26232step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26232step1 raw26232step0; decide +kernel
      have hl : raw26232step1Labels = raw26232step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26232step0 raw26232step0Labels permutation34 permutation2
    _ = mixedMoment B node4256 node4256Labels := by rfl

theorem canonical26233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26233 raw26233Labels = mixedMoment B node4267 node4267Labels := by
  calc
    mixedMoment B raw26233 raw26233Labels = mixedMoment B raw26233step0 raw26233step0Labels := by
      have hz : ∀ j, raw26233 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26233step0 = (fun i j => raw26233 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26233step0 raw26233; decide +kernel
      have hl : raw26233step0Labels = raw26233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26233 raw26233Labels permutation346 hz
    mixedMoment B raw26233step0 raw26233step0Labels = mixedMoment B raw26233step1 raw26233step1Labels := by
      have ha : raw26233step1 = (fun i j => raw26233step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26233step1 raw26233step0; decide +kernel
      have hl : raw26233step1Labels = raw26233step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26233step0 raw26233step0Labels permutation35 permutation2
    _ = mixedMoment B node4267 node4267Labels := by rfl

theorem canonical26234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26234 raw26234Labels = mixedMoment B node4107 node4107Labels := by
  calc
    mixedMoment B raw26234 raw26234Labels = mixedMoment B raw26234step0 raw26234step0Labels := by
      have hz : ∀ j, raw26234 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26234step0 = (fun i j => raw26234 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26234step0 raw26234; decide +kernel
      have hl : raw26234step0Labels = raw26234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26234 raw26234Labels permutation346 hz
    _ = mixedMoment B node4107 node4107Labels := by rfl

theorem canonical26235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26235 raw26235Labels = mixedMoment B node4239 node4239Labels := by
  calc
    mixedMoment B raw26235 raw26235Labels = mixedMoment B raw26235step0 raw26235step0Labels := by
      have hz : ∀ j, raw26235 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26235step0 = (fun i j => raw26235 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26235step0 raw26235; decide +kernel
      have hl : raw26235step0Labels = raw26235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26235 raw26235Labels permutation346 hz
    _ = mixedMoment B node4239 node4239Labels := by rfl

theorem canonical26236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26236 raw26236Labels = mixedMoment B node4201 node4201Labels := by
  calc
    mixedMoment B raw26236 raw26236Labels = mixedMoment B raw26236step0 raw26236step0Labels := by
      have ha : raw26236step0 = (fun i j => raw26236 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26236step0 raw26236; decide +kernel
      have hl : raw26236step0Labels = raw26236Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26236 raw26236Labels permutation176 permutation2
    _ = mixedMoment B node4201 node4201Labels := by rfl

theorem canonical26237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26237 raw26237Labels = mixedMoment B node4256 node4256Labels := by
  calc
    mixedMoment B raw26237 raw26237Labels = mixedMoment B raw26237step0 raw26237step0Labels := by
      have hz : ∀ j, raw26237 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26237step0 = (fun i j => raw26237 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26237step0 raw26237; decide +kernel
      have hl : raw26237step0Labels = raw26237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26237 raw26237Labels permutation346 hz
    _ = mixedMoment B node4256 node4256Labels := by rfl

theorem canonical26238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26238 raw26238Labels = mixedMoment B node4267 node4267Labels := by
  calc
    mixedMoment B raw26238 raw26238Labels = mixedMoment B raw26238step0 raw26238step0Labels := by
      have hz : ∀ j, raw26238 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26238step0 = (fun i j => raw26238 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26238step0 raw26238; decide +kernel
      have hl : raw26238step0Labels = raw26238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26238 raw26238Labels permutation346 hz
    mixedMoment B raw26238step0 raw26238step0Labels = mixedMoment B raw26238step1 raw26238step1Labels := by
      have ha : raw26238step1 = (fun i j => raw26238step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26238step1 raw26238step0; decide +kernel
      have hl : raw26238step1Labels = raw26238step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26238step0 raw26238step0Labels permutation33 permutation2
    _ = mixedMoment B node4267 node4267Labels := by rfl

theorem canonical26239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26239 raw26239Labels = mixedMoment B node4105 node4105Labels := by
  calc
    mixedMoment B raw26239 raw26239Labels = mixedMoment B raw26239step0 raw26239step0Labels := by
      have hz : ∀ j, raw26239 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26239step0 = (fun i j => raw26239 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26239step0 raw26239; decide +kernel
      have hl : raw26239step0Labels = raw26239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26239 raw26239Labels permutation346 hz
    _ = mixedMoment B node4105 node4105Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical205
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26240 raw26240Labels = mixedMoment B node4237 node4237Labels := by
  calc
    mixedMoment B raw26240 raw26240Labels = mixedMoment B raw26240step0 raw26240step0Labels := by
      have hz : ∀ j, raw26240 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26240step0 = (fun i j => raw26240 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26240step0 raw26240; decide +kernel
      have hl : raw26240step0Labels = raw26240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26240 raw26240Labels permutation346 hz
    _ = mixedMoment B node4237 node4237Labels := by rfl

theorem canonical26241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26241 raw26241Labels = mixedMoment B node4199 node4199Labels := by
  calc
    mixedMoment B raw26241 raw26241Labels = mixedMoment B raw26241step0 raw26241step0Labels := by
      have ha : raw26241step0 = (fun i j => raw26241 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26241step0 raw26241; decide +kernel
      have hl : raw26241step0Labels = raw26241Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26241 raw26241Labels permutation176 permutation2
    _ = mixedMoment B node4199 node4199Labels := by rfl

theorem canonical26242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26242 raw26242Labels = mixedMoment B node4253 node4253Labels := by
  calc
    mixedMoment B raw26242 raw26242Labels = mixedMoment B raw26242step0 raw26242step0Labels := by
      have hz : ∀ j, raw26242 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26242step0 = (fun i j => raw26242 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26242step0 raw26242; decide +kernel
      have hl : raw26242step0Labels = raw26242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26242 raw26242Labels permutation346 hz
    _ = mixedMoment B node4253 node4253Labels := by rfl

theorem canonical26243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26243 raw26243Labels = mixedMoment B node4253 node4253Labels := by
  calc
    mixedMoment B raw26243 raw26243Labels = mixedMoment B raw26243step0 raw26243step0Labels := by
      have hz : ∀ j, raw26243 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26243step0 = (fun i j => raw26243 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26243step0 raw26243; decide +kernel
      have hl : raw26243step0Labels = raw26243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26243 raw26243Labels permutation346 hz
    mixedMoment B raw26243step0 raw26243step0Labels = mixedMoment B raw26243step1 raw26243step1Labels := by
      have ha : raw26243step1 = (fun i j => raw26243step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26243step1 raw26243step0; decide +kernel
      have hl : raw26243step1Labels = raw26243step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26243step0 raw26243step0Labels permutation34 permutation2
    _ = mixedMoment B node4253 node4253Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw672 raw672Labels = mixedMoment B node4100 node4100Labels := by
  calc
    mixedMoment B raw672 raw672Labels = mixedMoment B raw672step0 raw672step0Labels := by
      have ha : raw672step0 = (fun i j => raw672 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw672step0 raw672; decide +kernel
      have hl : raw672step0Labels = raw672Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw672 raw672Labels permutation152 permutation4
    mixedMoment B raw672step0 raw672step0Labels = mixedMoment B raw672step1 raw672step1Labels := by
      have ha : raw672step1 = raw672step0 := by apply Matrix.ext; unfold raw672step1 raw672step0; decide +kernel
      have hl : raw672step0Labels = labelEmbedding7 ∘ raw672step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw672step0 raw672step0Labels raw672step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4100 node4100Labels := by rfl

theorem canonical673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw673 raw673Labels = mixedMoment B node537 node537Labels := by
  calc
    mixedMoment B raw673 raw673Labels = mixedMoment B raw673step0 raw673step0Labels := by
      have ha : raw673step0 = (fun i j => raw673 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw673step0 raw673; decide +kernel
      have hl : raw673step0Labels = raw673Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw673 raw673Labels permutation152 permutation4
    _ = mixedMoment B node537 node537Labels := by rfl

theorem canonical674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw674 raw674Labels = mixedMoment B node662 node662Labels := by
  calc
    mixedMoment B raw674 raw674Labels = mixedMoment B raw674step0 raw674step0Labels := by
      have ha : raw674step0 = (fun i j => raw674 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw674step0 raw674; decide +kernel
      have hl : raw674step0Labels = raw674Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw674 raw674Labels permutation176 permutation6
    mixedMoment B raw674step0 raw674step0Labels = mixedMoment B raw674step1 raw674step1Labels := by
      have ha : raw674step1 = -raw674step0 := by apply Matrix.ext; change ∀ i j, raw674step1 i j = -(raw674step0 i j); unfold raw674step1 raw674step0; decide +kernel
      have hl : raw674step1Labels = raw674step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw674step1 raw674step1Labels = mixedMoment B raw674step2 raw674step2Labels := by
      have ha : raw674step2 = raw674step1 := by apply Matrix.ext; unfold raw674step2 raw674step1; decide +kernel
      have hl : raw674step1Labels = labelEmbedding1 ∘ raw674step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw674step1 raw674step1Labels raw674step2Labels labelEmbedding1 hl
    _ = mixedMoment B node662 node662Labels := by rfl

theorem canonical687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw687 raw687Labels = mixedMoment B node4105 node4105Labels := by
  calc
    mixedMoment B raw687 raw687Labels = mixedMoment B raw687step0 raw687step0Labels := by
      have ha : raw687step0 = (fun i j => raw687 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw687step0 raw687; decide +kernel
      have hl : raw687step0Labels = raw687Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw687 raw687Labels permutation32 permutation4
    mixedMoment B raw687step0 raw687step0Labels = mixedMoment B raw687step1 raw687step1Labels := by
      have ha : raw687step1 = raw687step0 := by apply Matrix.ext; unfold raw687step1 raw687step0; decide +kernel
      have hl : raw687step0Labels = labelEmbedding7 ∘ raw687step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw687step0 raw687step0Labels raw687step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4105 node4105Labels := by rfl

theorem canonical688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw688 raw688Labels = mixedMoment B node542 node542Labels := by
  calc
    mixedMoment B raw688 raw688Labels = mixedMoment B raw688step0 raw688step0Labels := by
      have ha : raw688step0 = (fun i j => raw688 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw688step0 raw688; decide +kernel
      have hl : raw688step0Labels = raw688Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw688 raw688Labels permutation32 permutation4
    _ = mixedMoment B node542 node542Labels := by rfl

theorem canonical689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw689 raw689Labels = mixedMoment B node681 node681Labels := by
  calc
    mixedMoment B raw689 raw689Labels = mixedMoment B raw689step0 raw689step0Labels := by
      have ha : raw689step0 = (fun i j => raw689 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw689step0 raw689; decide +kernel
      have hl : raw689step0Labels = raw689Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw689 raw689Labels permutation32 permutation6
    mixedMoment B raw689step0 raw689step0Labels = mixedMoment B raw689step1 raw689step1Labels := by
      have ha : raw689step1 = -raw689step0 := by apply Matrix.ext; change ∀ i j, raw689step1 i j = -(raw689step0 i j); unfold raw689step1 raw689step0; decide +kernel
      have hl : raw689step1Labels = raw689step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw689step1 raw689step1Labels = mixedMoment B raw689step2 raw689step2Labels := by
      have ha : raw689step2 = raw689step1 := by apply Matrix.ext; unfold raw689step2 raw689step1; decide +kernel
      have hl : raw689step1Labels = labelEmbedding1 ∘ raw689step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw689step1 raw689step1Labels raw689step2Labels labelEmbedding1 hl
    _ = mixedMoment B node681 node681Labels := by rfl

theorem canonical693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw693 raw693Labels = mixedMoment B node4107 node4107Labels := by
  calc
    mixedMoment B raw693 raw693Labels = mixedMoment B raw693step0 raw693step0Labels := by
      have ha : raw693step0 = (fun i j => raw693 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw693step0 raw693; decide +kernel
      have hl : raw693step0Labels = raw693Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw693 raw693Labels permutation32 permutation4
    mixedMoment B raw693step0 raw693step0Labels = mixedMoment B raw693step1 raw693step1Labels := by
      have ha : raw693step1 = raw693step0 := by apply Matrix.ext; unfold raw693step1 raw693step0; decide +kernel
      have hl : raw693step0Labels = labelEmbedding7 ∘ raw693step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw693step0 raw693step0Labels raw693step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4107 node4107Labels := by rfl

theorem canonical694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw694 raw694Labels = mixedMoment B node544 node544Labels := by
  calc
    mixedMoment B raw694 raw694Labels = mixedMoment B raw694step0 raw694step0Labels := by
      have ha : raw694step0 = (fun i j => raw694 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw694step0 raw694; decide +kernel
      have hl : raw694step0Labels = raw694Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw694 raw694Labels permutation32 permutation4
    _ = mixedMoment B node544 node544Labels := by rfl

theorem canonical695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw695 raw695Labels = mixedMoment B node682 node682Labels := by
  calc
    mixedMoment B raw695 raw695Labels = mixedMoment B raw695step0 raw695step0Labels := by
      have ha : raw695step0 = (fun i j => raw695 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw695step0 raw695; decide +kernel
      have hl : raw695step0Labels = raw695Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw695 raw695Labels permutation32 permutation6
    mixedMoment B raw695step0 raw695step0Labels = mixedMoment B raw695step1 raw695step1Labels := by
      have ha : raw695step1 = -raw695step0 := by apply Matrix.ext; change ∀ i j, raw695step1 i j = -(raw695step0 i j); unfold raw695step1 raw695step0; decide +kernel
      have hl : raw695step1Labels = raw695step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw695step1 raw695step1Labels = mixedMoment B raw695step2 raw695step2Labels := by
      have ha : raw695step2 = raw695step1 := by apply Matrix.ext; unfold raw695step2 raw695step1; decide +kernel
      have hl : raw695step1Labels = labelEmbedding1 ∘ raw695step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw695step1 raw695step1Labels raw695step2Labels labelEmbedding1 hl
    _ = mixedMoment B node682 node682Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw861 raw861Labels = mixedMoment B node4199 node4199Labels := by
  calc
    mixedMoment B raw861 raw861Labels = mixedMoment B raw861step0 raw861step0Labels := by
      have ha : raw861step0 = (fun i j => raw861 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw861step0 raw861; decide +kernel
      have hl : raw861step0Labels = raw861Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw861 raw861Labels permutation152 permutation4
    mixedMoment B raw861step0 raw861step0Labels = mixedMoment B raw861step1 raw861step1Labels := by
      have ha : raw861step1 = raw861step0 := by apply Matrix.ext; unfold raw861step1 raw861step0; decide +kernel
      have hl : raw861step0Labels = labelEmbedding7 ∘ raw861step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw861step0 raw861step0Labels raw861step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4199 node4199Labels := by rfl

theorem canonical862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw862 raw862Labels = mixedMoment B node702 node702Labels := by
  calc
    mixedMoment B raw862 raw862Labels = mixedMoment B raw862step0 raw862step0Labels := by
      have ha : raw862step0 = (fun i j => raw862 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw862step0 raw862; decide +kernel
      have hl : raw862step0Labels = raw862Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw862 raw862Labels permutation152 permutation4
    _ = mixedMoment B node702 node702Labels := by rfl

theorem canonical863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw863 raw863Labels = mixedMoment B node760 node760Labels := by
  calc
    mixedMoment B raw863 raw863Labels = mixedMoment B raw863step0 raw863step0Labels := by
      have ha : raw863step0 = (fun i j => raw863 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw863step0 raw863; decide +kernel
      have hl : raw863step0Labels = raw863Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw863 raw863Labels permutation152 permutation6
    mixedMoment B raw863step0 raw863step0Labels = mixedMoment B raw863step1 raw863step1Labels := by
      have ha : raw863step1 = -raw863step0 := by apply Matrix.ext; change ∀ i j, raw863step1 i j = -(raw863step0 i j); unfold raw863step1 raw863step0; decide +kernel
      have hl : raw863step1Labels = raw863step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw863step1 raw863step1Labels = mixedMoment B raw863step2 raw863step2Labels := by
      have ha : raw863step2 = raw863step1 := by apply Matrix.ext; unfold raw863step2 raw863step1; decide +kernel
      have hl : raw863step1Labels = labelEmbedding1 ∘ raw863step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw863step1 raw863step1Labels raw863step2Labels labelEmbedding1 hl
    _ = mixedMoment B node760 node760Labels := by rfl

theorem canonical867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw867 raw867Labels = mixedMoment B node4201 node4201Labels := by
  calc
    mixedMoment B raw867 raw867Labels = mixedMoment B raw867step0 raw867step0Labels := by
      have ha : raw867step0 = (fun i j => raw867 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw867step0 raw867; decide +kernel
      have hl : raw867step0Labels = raw867Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw867 raw867Labels permutation152 permutation4
    mixedMoment B raw867step0 raw867step0Labels = mixedMoment B raw867step1 raw867step1Labels := by
      have ha : raw867step1 = raw867step0 := by apply Matrix.ext; unfold raw867step1 raw867step0; decide +kernel
      have hl : raw867step0Labels = labelEmbedding7 ∘ raw867step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw867step0 raw867step0Labels raw867step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4201 node4201Labels := by rfl

theorem canonical868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw868 raw868Labels = mixedMoment B node704 node704Labels := by
  calc
    mixedMoment B raw868 raw868Labels = mixedMoment B raw868step0 raw868step0Labels := by
      have ha : raw868step0 = (fun i j => raw868 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw868step0 raw868; decide +kernel
      have hl : raw868step0Labels = raw868Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw868 raw868Labels permutation152 permutation4
    _ = mixedMoment B node704 node704Labels := by rfl

theorem canonical869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw869 raw869Labels = mixedMoment B node761 node761Labels := by
  calc
    mixedMoment B raw869 raw869Labels = mixedMoment B raw869step0 raw869step0Labels := by
      have ha : raw869step0 = (fun i j => raw869 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw869step0 raw869; decide +kernel
      have hl : raw869step0Labels = raw869Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw869 raw869Labels permutation152 permutation6
    mixedMoment B raw869step0 raw869step0Labels = mixedMoment B raw869step1 raw869step1Labels := by
      have ha : raw869step1 = -raw869step0 := by apply Matrix.ext; change ∀ i j, raw869step1 i j = -(raw869step0 i j); unfold raw869step1 raw869step0; decide +kernel
      have hl : raw869step1Labels = raw869step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw869step1 raw869step1Labels = mixedMoment B raw869step2 raw869step2Labels := by
      have ha : raw869step2 = raw869step1 := by apply Matrix.ext; unfold raw869step2 raw869step1; decide +kernel
      have hl : raw869step1Labels = labelEmbedding1 ∘ raw869step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw869step1 raw869step1Labels raw869step2Labels labelEmbedding1 hl
    _ = mixedMoment B node761 node761Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw930 raw930Labels = mixedMoment B node4232 node4232Labels := by
  calc
    mixedMoment B raw930 raw930Labels = mixedMoment B raw930step0 raw930step0Labels := by
      have ha : raw930step0 = (fun i j => raw930 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw930step0 raw930; decide +kernel
      have hl : raw930step0Labels = raw930Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw930 raw930Labels permutation152 permutation4
    mixedMoment B raw930step0 raw930step0Labels = mixedMoment B raw930step1 raw930step1Labels := by
      have ha : raw930step1 = raw930step0 := by apply Matrix.ext; unfold raw930step1 raw930step0; decide +kernel
      have hl : raw930step0Labels = labelEmbedding7 ∘ raw930step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw930step0 raw930step0Labels raw930step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4232 node4232Labels := by rfl

theorem canonical931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw931 raw931Labels = mixedMoment B node732 node732Labels := by
  calc
    mixedMoment B raw931 raw931Labels = mixedMoment B raw931step0 raw931step0Labels := by
      have ha : raw931step0 = (fun i j => raw931 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw931step0 raw931; decide +kernel
      have hl : raw931step0Labels = raw931Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw931 raw931Labels permutation152 permutation4
    _ = mixedMoment B node732 node732Labels := by rfl

theorem canonical932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw932 raw932Labels = mixedMoment B node798 node798Labels := by
  calc
    mixedMoment B raw932 raw932Labels = mixedMoment B raw932step0 raw932step0Labels := by
      have ha : raw932step0 = (fun i j => raw932 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw932step0 raw932; decide +kernel
      have hl : raw932step0Labels = raw932Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw932 raw932Labels permutation176 permutation6
    mixedMoment B raw932step0 raw932step0Labels = mixedMoment B raw932step1 raw932step1Labels := by
      have ha : raw932step1 = -raw932step0 := by apply Matrix.ext; change ∀ i j, raw932step1 i j = -(raw932step0 i j); unfold raw932step1 raw932step0; decide +kernel
      have hl : raw932step1Labels = raw932step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw932step1 raw932step1Labels = mixedMoment B raw932step2 raw932step2Labels := by
      have ha : raw932step2 = raw932step1 := by apply Matrix.ext; unfold raw932step2 raw932step1; decide +kernel
      have hl : raw932step1Labels = labelEmbedding1 ∘ raw932step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw932step1 raw932step1Labels raw932step2Labels labelEmbedding1 hl
    _ = mixedMoment B node798 node798Labels := by rfl

theorem canonical945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw945 raw945Labels = mixedMoment B node4237 node4237Labels := by
  calc
    mixedMoment B raw945 raw945Labels = mixedMoment B raw945step0 raw945step0Labels := by
      have ha : raw945step0 = (fun i j => raw945 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw945step0 raw945; decide +kernel
      have hl : raw945step0Labels = raw945Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw945 raw945Labels permutation32 permutation4
    mixedMoment B raw945step0 raw945step0Labels = mixedMoment B raw945step1 raw945step1Labels := by
      have ha : raw945step1 = raw945step0 := by apply Matrix.ext; unfold raw945step1 raw945step0; decide +kernel
      have hl : raw945step0Labels = labelEmbedding7 ∘ raw945step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw945step0 raw945step0Labels raw945step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4237 node4237Labels := by rfl

theorem canonical946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw946 raw946Labels = mixedMoment B node737 node737Labels := by
  calc
    mixedMoment B raw946 raw946Labels = mixedMoment B raw946step0 raw946step0Labels := by
      have ha : raw946step0 = (fun i j => raw946 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw946step0 raw946; decide +kernel
      have hl : raw946step0Labels = raw946Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw946 raw946Labels permutation32 permutation4
    _ = mixedMoment B node737 node737Labels := by rfl

theorem canonical947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw947 raw947Labels = mixedMoment B node840 node840Labels := by
  calc
    mixedMoment B raw947 raw947Labels = mixedMoment B raw947step0 raw947step0Labels := by
      have ha : raw947step0 = (fun i j => raw947 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw947step0 raw947; decide +kernel
      have hl : raw947step0Labels = raw947Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw947 raw947Labels permutation32 permutation6
    mixedMoment B raw947step0 raw947step0Labels = mixedMoment B raw947step1 raw947step1Labels := by
      have ha : raw947step1 = -raw947step0 := by apply Matrix.ext; change ∀ i j, raw947step1 i j = -(raw947step0 i j); unfold raw947step1 raw947step0; decide +kernel
      have hl : raw947step1Labels = raw947step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw947step1 raw947step1Labels = mixedMoment B raw947step2 raw947step2Labels := by
      have ha : raw947step2 = raw947step1 := by apply Matrix.ext; unfold raw947step2 raw947step1; decide +kernel
      have hl : raw947step1Labels = labelEmbedding1 ∘ raw947step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw947step1 raw947step1Labels raw947step2Labels labelEmbedding1 hl
    _ = mixedMoment B node840 node840Labels := by rfl

theorem canonical951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw951 raw951Labels = mixedMoment B node4239 node4239Labels := by
  calc
    mixedMoment B raw951 raw951Labels = mixedMoment B raw951step0 raw951step0Labels := by
      have ha : raw951step0 = (fun i j => raw951 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw951step0 raw951; decide +kernel
      have hl : raw951step0Labels = raw951Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw951 raw951Labels permutation32 permutation4
    mixedMoment B raw951step0 raw951step0Labels = mixedMoment B raw951step1 raw951step1Labels := by
      have ha : raw951step1 = raw951step0 := by apply Matrix.ext; unfold raw951step1 raw951step0; decide +kernel
      have hl : raw951step0Labels = labelEmbedding7 ∘ raw951step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw951step0 raw951step0Labels raw951step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4239 node4239Labels := by rfl

theorem canonical952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw952 raw952Labels = mixedMoment B node739 node739Labels := by
  calc
    mixedMoment B raw952 raw952Labels = mixedMoment B raw952step0 raw952step0Labels := by
      have ha : raw952step0 = (fun i j => raw952 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw952step0 raw952; decide +kernel
      have hl : raw952step0Labels = raw952Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw952 raw952Labels permutation32 permutation4
    _ = mixedMoment B node739 node739Labels := by rfl

theorem canonical953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw953 raw953Labels = mixedMoment B node841 node841Labels := by
  calc
    mixedMoment B raw953 raw953Labels = mixedMoment B raw953step0 raw953step0Labels := by
      have ha : raw953step0 = (fun i j => raw953 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw953step0 raw953; decide +kernel
      have hl : raw953step0Labels = raw953Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw953 raw953Labels permutation32 permutation6
    mixedMoment B raw953step0 raw953step0Labels = mixedMoment B raw953step1 raw953step1Labels := by
      have ha : raw953step1 = -raw953step0 := by apply Matrix.ext; change ∀ i j, raw953step1 i j = -(raw953step0 i j); unfold raw953step1 raw953step0; decide +kernel
      have hl : raw953step1Labels = raw953step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw953step1 raw953step1Labels = mixedMoment B raw953step2 raw953step2Labels := by
      have ha : raw953step2 = raw953step1 := by apply Matrix.ext; unfold raw953step2 raw953step1; decide +kernel
      have hl : raw953step1Labels = labelEmbedding1 ∘ raw953step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw953step1 raw953step1Labels raw953step2Labels labelEmbedding1 hl
    _ = mixedMoment B node841 node841Labels := by rfl

theorem canonical969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw969 raw969Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw969 raw969Labels = mixedMoment B raw969step0 raw969step0Labels := by
      have ha : raw969step0 = (fun i j => raw969 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw969step0 raw969; decide +kernel
      have hl : raw969step0Labels = raw969Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw969 raw969Labels permutation152 permutation4
    mixedMoment B raw969step0 raw969step0Labels = mixedMoment B raw969step1 raw969step1Labels := by
      have ha : raw969step1 = raw969step0 := by apply Matrix.ext; unfold raw969step1 raw969step0; decide +kernel
      have hl : raw969step0Labels = labelEmbedding7 ∘ raw969step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw969step0 raw969step0Labels raw969step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4249 node4249Labels := by rfl

theorem canonical970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw970 raw970Labels = mixedMoment B node783 node783Labels := by
  calc
    mixedMoment B raw970 raw970Labels = mixedMoment B raw970step0 raw970step0Labels := by
      have ha : raw970step0 = (fun i j => raw970 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw970step0 raw970; decide +kernel
      have hl : raw970step0Labels = raw970Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw970 raw970Labels permutation152 permutation4
    _ = mixedMoment B node783 node783Labels := by rfl

theorem canonical971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw971 raw971Labels = mixedMoment B node803 node803Labels := by
  calc
    mixedMoment B raw971 raw971Labels = mixedMoment B raw971step0 raw971step0Labels := by
      have ha : raw971step0 = (fun i j => raw971 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw971step0 raw971; decide +kernel
      have hl : raw971step0Labels = raw971Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw971 raw971Labels permutation200 permutation6
    mixedMoment B raw971step0 raw971step0Labels = mixedMoment B raw971step1 raw971step1Labels := by
      have ha : raw971step1 = -raw971step0 := by apply Matrix.ext; change ∀ i j, raw971step1 i j = -(raw971step0 i j); unfold raw971step1 raw971step0; decide +kernel
      have hl : raw971step1Labels = raw971step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw971step1 raw971step1Labels = mixedMoment B raw971step2 raw971step2Labels := by
      have ha : raw971step2 = raw971step1 := by apply Matrix.ext; unfold raw971step2 raw971step1; decide +kernel
      have hl : raw971step1Labels = labelEmbedding1 ∘ raw971step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw971step1 raw971step1Labels raw971step2Labels labelEmbedding1 hl
    _ = mixedMoment B node803 node803Labels := by rfl

theorem canonical978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw978 raw978Labels = mixedMoment B node4253 node4253Labels := by
  calc
    mixedMoment B raw978 raw978Labels = mixedMoment B raw978step0 raw978step0Labels := by
      have ha : raw978step0 = (fun i j => raw978 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw978step0 raw978; decide +kernel
      have hl : raw978step0Labels = raw978Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw978 raw978Labels permutation32 permutation4
    mixedMoment B raw978step0 raw978step0Labels = mixedMoment B raw978step1 raw978step1Labels := by
      have ha : raw978step1 = raw978step0 := by apply Matrix.ext; unfold raw978step1 raw978step0; decide +kernel
      have hl : raw978step0Labels = labelEmbedding7 ∘ raw978step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw978step0 raw978step0Labels raw978step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4253 node4253Labels := by rfl

theorem canonical979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw979 raw979Labels = mixedMoment B node787 node787Labels := by
  calc
    mixedMoment B raw979 raw979Labels = mixedMoment B raw979step0 raw979step0Labels := by
      have ha : raw979step0 = (fun i j => raw979 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw979step0 raw979; decide +kernel
      have hl : raw979step0Labels = raw979Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw979 raw979Labels permutation32 permutation4
    _ = mixedMoment B node787 node787Labels := by rfl

theorem canonical980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw980 raw980Labels = mixedMoment B node847 node847Labels := by
  calc
    mixedMoment B raw980 raw980Labels = mixedMoment B raw980step0 raw980step0Labels := by
      have ha : raw980step0 = (fun i j => raw980 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw980step0 raw980; decide +kernel
      have hl : raw980step0Labels = raw980Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw980 raw980Labels permutation32 permutation6
    mixedMoment B raw980step0 raw980step0Labels = mixedMoment B raw980step1 raw980step1Labels := by
      have ha : raw980step1 = -raw980step0 := by apply Matrix.ext; change ∀ i j, raw980step1 i j = -(raw980step0 i j); unfold raw980step1 raw980step0; decide +kernel
      have hl : raw980step1Labels = raw980step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw980step1 raw980step1Labels = mixedMoment B raw980step2 raw980step2Labels := by
      have ha : raw980step2 = raw980step1 := by apply Matrix.ext; unfold raw980step2 raw980step1; decide +kernel
      have hl : raw980step1Labels = labelEmbedding1 ∘ raw980step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw980step1 raw980step1Labels raw980step2Labels labelEmbedding1 hl
    _ = mixedMoment B node847 node847Labels := by rfl

theorem canonical984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw984 raw984Labels = mixedMoment B node4256 node4256Labels := by
  calc
    mixedMoment B raw984 raw984Labels = mixedMoment B raw984step0 raw984step0Labels := by
      have ha : raw984step0 = (fun i j => raw984 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw984step0 raw984; decide +kernel
      have hl : raw984step0Labels = raw984Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw984 raw984Labels permutation32 permutation4
    mixedMoment B raw984step0 raw984step0Labels = mixedMoment B raw984step1 raw984step1Labels := by
      have ha : raw984step1 = raw984step0 := by apply Matrix.ext; unfold raw984step1 raw984step0; decide +kernel
      have hl : raw984step0Labels = labelEmbedding7 ∘ raw984step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw984step0 raw984step0Labels raw984step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4256 node4256Labels := by rfl

theorem canonical985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw985 raw985Labels = mixedMoment B node790 node790Labels := by
  calc
    mixedMoment B raw985 raw985Labels = mixedMoment B raw985step0 raw985step0Labels := by
      have ha : raw985step0 = (fun i j => raw985 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw985step0 raw985; decide +kernel
      have hl : raw985step0Labels = raw985Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw985 raw985Labels permutation32 permutation4
    _ = mixedMoment B node790 node790Labels := by rfl

theorem canonical986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw986 raw986Labels = mixedMoment B node848 node848Labels := by
  calc
    mixedMoment B raw986 raw986Labels = mixedMoment B raw986step0 raw986step0Labels := by
      have ha : raw986step0 = (fun i j => raw986 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw986step0 raw986; decide +kernel
      have hl : raw986step0Labels = raw986Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw986 raw986Labels permutation32 permutation6
    mixedMoment B raw986step0 raw986step0Labels = mixedMoment B raw986step1 raw986step1Labels := by
      have ha : raw986step1 = -raw986step0 := by apply Matrix.ext; change ∀ i j, raw986step1 i j = -(raw986step0 i j); unfold raw986step1 raw986step0; decide +kernel
      have hl : raw986step1Labels = raw986step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw986step1 raw986step1Labels = mixedMoment B raw986step2 raw986step2Labels := by
      have ha : raw986step2 = raw986step1 := by apply Matrix.ext; unfold raw986step2 raw986step1; decide +kernel
      have hl : raw986step1Labels = labelEmbedding1 ∘ raw986step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw986step1 raw986step1Labels raw986step2Labels labelEmbedding1 hl
    _ = mixedMoment B node848 node848Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1224 raw1224Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw1224 raw1224Labels = mixedMoment B raw1224step0 raw1224step0Labels := by
      have ha : raw1224step0 = (fun i j => raw1224 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1224step0 raw1224; decide +kernel
      have hl : raw1224step0Labels = raw1224Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1224 raw1224Labels permutation152 permutation4
    mixedMoment B raw1224step0 raw1224step0Labels = mixedMoment B raw1224step1 raw1224step1Labels := by
      have ha : raw1224step1 = raw1224step0 := by apply Matrix.ext; unfold raw1224step1 raw1224step0; decide +kernel
      have hl : raw1224step0Labels = labelEmbedding7 ∘ raw1224step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1224step0 raw1224step0Labels raw1224step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

theorem canonical1225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1225 raw1225Labels = mixedMoment B node998 node998Labels := by
  calc
    mixedMoment B raw1225 raw1225Labels = mixedMoment B raw1225step0 raw1225step0Labels := by
      have ha : raw1225step0 = (fun i j => raw1225 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1225step0 raw1225; decide +kernel
      have hl : raw1225step0Labels = raw1225Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1225 raw1225Labels permutation152 permutation4
    _ = mixedMoment B node998 node998Labels := by rfl

theorem canonical1226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1226 raw1226Labels = mixedMoment B node1600 node1600Labels := by
  calc
    mixedMoment B raw1226 raw1226Labels = mixedMoment B raw1226step0 raw1226step0Labels := by
      have ha : raw1226step0 = (fun i j => raw1226 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1226step0 raw1226; decide +kernel
      have hl : raw1226step0Labels = raw1226Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1226 raw1226Labels permutation152 permutation6
    mixedMoment B raw1226step0 raw1226step0Labels = mixedMoment B raw1226step1 raw1226step1Labels := by
      have ha : raw1226step1 = -raw1226step0 := by apply Matrix.ext; change ∀ i j, raw1226step1 i j = -(raw1226step0 i j); unfold raw1226step1 raw1226step0; decide +kernel
      have hl : raw1226step1Labels = raw1226step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1226step1 raw1226step1Labels = mixedMoment B raw1226step2 raw1226step2Labels := by
      have ha : raw1226step2 = raw1226step1 := by apply Matrix.ext; unfold raw1226step2 raw1226step1; decide +kernel
      have hl : raw1226step1Labels = labelEmbedding1 ∘ raw1226step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1226step1 raw1226step1Labels raw1226step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1600 node1600Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4100 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4100 node4100Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node537 node537Labels + mixedMoment B node662 node662Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw672 singletonSmall4100
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4100) = raw672Labels := by decide +kernel
  rw [hl, canonical672 B hB] at h
  have hc0 : mixedMoment B raw672 (Fin.cases (0 : Fin 2) singletonSmall4100) =
      mixedMoment B node537 node537Labels := by
    have ha : raw672 = raw673 := by apply Matrix.ext; unfold raw672 raw673; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4100 = raw673Labels := by decide +kernel
    rw [ha, hj, canonical673 B hB]
  have hc1 : mixedMoment B raw672 (Fin.cases (1 : Fin 2) singletonSmall4100) =
      mixedMoment B node662 node662Labels := by
    have ha : raw672 = raw674 := by apply Matrix.ext; unfold raw672 raw674; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4100 = raw674Labels := by decide +kernel
    rw [ha, hj, canonical674 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4105 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4105 node4105Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node542 node542Labels + mixedMoment B node681 node681Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw687 singletonSmall4105
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4105) = raw687Labels := by decide +kernel
  rw [hl, canonical687 B hB] at h
  have hc0 : mixedMoment B raw687 (Fin.cases (0 : Fin 2) singletonSmall4105) =
      mixedMoment B node542 node542Labels := by
    have ha : raw687 = raw688 := by apply Matrix.ext; unfold raw687 raw688; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4105 = raw688Labels := by decide +kernel
    rw [ha, hj, canonical688 B hB]
  have hc1 : mixedMoment B raw687 (Fin.cases (1 : Fin 2) singletonSmall4105) =
      mixedMoment B node681 node681Labels := by
    have ha : raw687 = raw689 := by apply Matrix.ext; unfold raw687 raw689; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4105 = raw689Labels := by decide +kernel
    rw [ha, hj, canonical689 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4107 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4107 node4107Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node544 node544Labels + mixedMoment B node682 node682Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw693 singletonSmall4107
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4107) = raw693Labels := by decide +kernel
  rw [hl, canonical693 B hB] at h
  have hc0 : mixedMoment B raw693 (Fin.cases (0 : Fin 2) singletonSmall4107) =
      mixedMoment B node544 node544Labels := by
    have ha : raw693 = raw694 := by apply Matrix.ext; unfold raw693 raw694; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4107 = raw694Labels := by decide +kernel
    rw [ha, hj, canonical694 B hB]
  have hc1 : mixedMoment B raw693 (Fin.cases (1 : Fin 2) singletonSmall4107) =
      mixedMoment B node682 node682Labels := by
    have ha : raw693 = raw695 := by apply Matrix.ext; unfold raw693 raw695; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4107 = raw695Labels := by decide +kernel
    rw [ha, hj, canonical695 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4199 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4199 node4199Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node702 node702Labels + mixedMoment B node760 node760Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw861 singletonSmall4199
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4199) = raw861Labels := by decide +kernel
  rw [hl, canonical861 B hB] at h
  have hc0 : mixedMoment B raw861 (Fin.cases (0 : Fin 2) singletonSmall4199) =
      mixedMoment B node702 node702Labels := by
    have ha : raw861 = raw862 := by apply Matrix.ext; unfold raw861 raw862; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4199 = raw862Labels := by decide +kernel
    rw [ha, hj, canonical862 B hB]
  have hc1 : mixedMoment B raw861 (Fin.cases (1 : Fin 2) singletonSmall4199) =
      mixedMoment B node760 node760Labels := by
    have ha : raw861 = raw863 := by apply Matrix.ext; unfold raw861 raw863; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4199 = raw863Labels := by decide +kernel
    rw [ha, hj, canonical863 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4201 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4201 node4201Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node704 node704Labels + mixedMoment B node761 node761Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw867 singletonSmall4201
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4201) = raw867Labels := by decide +kernel
  rw [hl, canonical867 B hB] at h
  have hc0 : mixedMoment B raw867 (Fin.cases (0 : Fin 2) singletonSmall4201) =
      mixedMoment B node704 node704Labels := by
    have ha : raw867 = raw868 := by apply Matrix.ext; unfold raw867 raw868; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4201 = raw868Labels := by decide +kernel
    rw [ha, hj, canonical868 B hB]
  have hc1 : mixedMoment B raw867 (Fin.cases (1 : Fin 2) singletonSmall4201) =
      mixedMoment B node761 node761Labels := by
    have ha : raw867 = raw869 := by apply Matrix.ext; unfold raw867 raw869; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4201 = raw869Labels := by decide +kernel
    rw [ha, hj, canonical869 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4232 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4232 node4232Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node732 node732Labels + mixedMoment B node798 node798Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw930 singletonSmall4232
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4232) = raw930Labels := by decide +kernel
  rw [hl, canonical930 B hB] at h
  have hc0 : mixedMoment B raw930 (Fin.cases (0 : Fin 2) singletonSmall4232) =
      mixedMoment B node732 node732Labels := by
    have ha : raw930 = raw931 := by apply Matrix.ext; unfold raw930 raw931; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4232 = raw931Labels := by decide +kernel
    rw [ha, hj, canonical931 B hB]
  have hc1 : mixedMoment B raw930 (Fin.cases (1 : Fin 2) singletonSmall4232) =
      mixedMoment B node798 node798Labels := by
    have ha : raw930 = raw932 := by apply Matrix.ext; unfold raw930 raw932; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4232 = raw932Labels := by decide +kernel
    rw [ha, hj, canonical932 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4237 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4237 node4237Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node737 node737Labels + mixedMoment B node840 node840Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw945 singletonSmall4237
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4237) = raw945Labels := by decide +kernel
  rw [hl, canonical945 B hB] at h
  have hc0 : mixedMoment B raw945 (Fin.cases (0 : Fin 2) singletonSmall4237) =
      mixedMoment B node737 node737Labels := by
    have ha : raw945 = raw946 := by apply Matrix.ext; unfold raw945 raw946; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4237 = raw946Labels := by decide +kernel
    rw [ha, hj, canonical946 B hB]
  have hc1 : mixedMoment B raw945 (Fin.cases (1 : Fin 2) singletonSmall4237) =
      mixedMoment B node840 node840Labels := by
    have ha : raw945 = raw947 := by apply Matrix.ext; unfold raw945 raw947; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4237 = raw947Labels := by decide +kernel
    rw [ha, hj, canonical947 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4239 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4239 node4239Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node739 node739Labels + mixedMoment B node841 node841Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw951 singletonSmall4239
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4239) = raw951Labels := by decide +kernel
  rw [hl, canonical951 B hB] at h
  have hc0 : mixedMoment B raw951 (Fin.cases (0 : Fin 2) singletonSmall4239) =
      mixedMoment B node739 node739Labels := by
    have ha : raw951 = raw952 := by apply Matrix.ext; unfold raw951 raw952; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4239 = raw952Labels := by decide +kernel
    rw [ha, hj, canonical952 B hB]
  have hc1 : mixedMoment B raw951 (Fin.cases (1 : Fin 2) singletonSmall4239) =
      mixedMoment B node841 node841Labels := by
    have ha : raw951 = raw953 := by apply Matrix.ext; unfold raw951 raw953; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4239 = raw953Labels := by decide +kernel
    rw [ha, hj, canonical953 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4249 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4249 node4249Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node783 node783Labels + mixedMoment B node803 node803Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw969 singletonSmall4249
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4249) = raw969Labels := by decide +kernel
  rw [hl, canonical969 B hB] at h
  have hc0 : mixedMoment B raw969 (Fin.cases (0 : Fin 2) singletonSmall4249) =
      mixedMoment B node783 node783Labels := by
    have ha : raw969 = raw970 := by apply Matrix.ext; unfold raw969 raw970; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4249 = raw970Labels := by decide +kernel
    rw [ha, hj, canonical970 B hB]
  have hc1 : mixedMoment B raw969 (Fin.cases (1 : Fin 2) singletonSmall4249) =
      mixedMoment B node803 node803Labels := by
    have ha : raw969 = raw971 := by apply Matrix.ext; unfold raw969 raw971; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4249 = raw971Labels := by decide +kernel
    rw [ha, hj, canonical971 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4253 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4253 node4253Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node787 node787Labels + mixedMoment B node847 node847Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw978 singletonSmall4253
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4253) = raw978Labels := by decide +kernel
  rw [hl, canonical978 B hB] at h
  have hc0 : mixedMoment B raw978 (Fin.cases (0 : Fin 2) singletonSmall4253) =
      mixedMoment B node787 node787Labels := by
    have ha : raw978 = raw979 := by apply Matrix.ext; unfold raw978 raw979; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4253 = raw979Labels := by decide +kernel
    rw [ha, hj, canonical979 B hB]
  have hc1 : mixedMoment B raw978 (Fin.cases (1 : Fin 2) singletonSmall4253) =
      mixedMoment B node847 node847Labels := by
    have ha : raw978 = raw980 := by apply Matrix.ext; unfold raw978 raw980; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4253 = raw980Labels := by decide +kernel
    rw [ha, hj, canonical980 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4256 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4256 node4256Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node790 node790Labels + mixedMoment B node848 node848Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw984 singletonSmall4256
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4256) = raw984Labels := by decide +kernel
  rw [hl, canonical984 B hB] at h
  have hc0 : mixedMoment B raw984 (Fin.cases (0 : Fin 2) singletonSmall4256) =
      mixedMoment B node790 node790Labels := by
    have ha : raw984 = raw985 := by apply Matrix.ext; unfold raw984 raw985; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4256 = raw985Labels := by decide +kernel
    rw [ha, hj, canonical985 B hB]
  have hc1 : mixedMoment B raw984 (Fin.cases (1 : Fin 2) singletonSmall4256) =
      mixedMoment B node848 node848Labels := by
    have ha : raw984 = raw986 := by apply Matrix.ext; unfold raw984 raw986; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4256 = raw986Labels := by decide +kernel
    rw [ha, hj, canonical986 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4417 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4417 node4417Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node998 node998Labels + mixedMoment B node1600 node1600Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1224 singletonSmall4417
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4417) = raw1224Labels := by decide +kernel
  rw [hl, canonical1224 B hB] at h
  have hc0 : mixedMoment B raw1224 (Fin.cases (0 : Fin 2) singletonSmall4417) =
      mixedMoment B node998 node998Labels := by
    have ha : raw1224 = raw1225 := by apply Matrix.ext; unfold raw1224 raw1225; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4417 = raw1225Labels := by decide +kernel
    rw [ha, hj, canonical1225 B hB]
  have hc1 : mixedMoment B raw1224 (Fin.cases (1 : Fin 2) singletonSmall4417) =
      mixedMoment B node1600 node1600Labels := by
    have ha : raw1224 = raw1226 := by apply Matrix.ext; unfold raw1224 raw1226; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4417 = raw1226Labels := by decide +kernel
    rw [ha, hj, canonical1226 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4489 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4489 node4489Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1073 node1073Labels + mixedMoment B node1648 node1648Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1281 singletonSmall4489
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4489) = raw1281Labels := by decide +kernel
  rw [hl, canonical1281 B hB] at h
  have hc0 : mixedMoment B raw1281 (Fin.cases (0 : Fin 2) singletonSmall4489) =
      mixedMoment B node1073 node1073Labels := by
    have ha : raw1281 = raw1282 := by apply Matrix.ext; unfold raw1281 raw1282; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4489 = raw1282Labels := by decide +kernel
    rw [ha, hj, canonical1282 B hB]
  have hc1 : mixedMoment B raw1281 (Fin.cases (1 : Fin 2) singletonSmall4489) =
      mixedMoment B node1648 node1648Labels := by
    have ha : raw1281 = raw1283 := by apply Matrix.ext; unfold raw1281 raw1283; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4489 = raw1283Labels := by decide +kernel
    rw [ha, hj, canonical1283 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4495 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4495 node4495Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1079 node1079Labels + mixedMoment B node1708 node1708Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1293 singletonSmall4495
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4495) = raw1293Labels := by decide +kernel
  rw [hl, canonical1293 B hB] at h
  have hc0 : mixedMoment B raw1293 (Fin.cases (0 : Fin 2) singletonSmall4495) =
      mixedMoment B node1079 node1079Labels := by
    have ha : raw1293 = raw1294 := by apply Matrix.ext; unfold raw1293 raw1294; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4495 = raw1294Labels := by decide +kernel
    rw [ha, hj, canonical1294 B hB]
  have hc1 : mixedMoment B raw1293 (Fin.cases (1 : Fin 2) singletonSmall4495) =
      mixedMoment B node1708 node1708Labels := by
    have ha : raw1293 = raw1295 := by apply Matrix.ext; unfold raw1293 raw1295; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4495 = raw1295Labels := by decide +kernel
    rw [ha, hj, canonical1295 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node662 node662Labels = Sparse.eval nodeValue662 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 662) = mixedMoment B node662 node662Labels := rfl
  simpa [nodeValue662, Sparse.eval] using hc.symm

theorem sound681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node681 node681Labels = Sparse.eval nodeValue681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 681) = mixedMoment B node681 node681Labels := rfl
  simpa [nodeValue681, Sparse.eval] using hc.symm

theorem sound682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node682 node682Labels = Sparse.eval nodeValue682 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 682) = mixedMoment B node682 node682Labels := rfl
  simpa [nodeValue682, Sparse.eval] using hc.symm

theorem sound702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node702 node702Labels = Sparse.eval nodeValue702 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 702) = mixedMoment B node702 node702Labels := rfl
  simpa [nodeValue702, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node704 node704Labels = Sparse.eval nodeValue704 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 704) = mixedMoment B node704 node704Labels := rfl
  simpa [nodeValue704, Sparse.eval] using hc.symm

theorem sound732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node732 node732Labels = Sparse.eval nodeValue732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 732) = mixedMoment B node732 node732Labels := rfl
  simpa [nodeValue732, Sparse.eval] using hc.symm

theorem sound737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node737 node737Labels = Sparse.eval nodeValue737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 737) = mixedMoment B node737 node737Labels := rfl
  simpa [nodeValue737, Sparse.eval] using hc.symm

theorem sound739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node739 node739Labels = Sparse.eval nodeValue739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 739) = mixedMoment B node739 node739Labels := rfl
  simpa [nodeValue739, Sparse.eval] using hc.symm

theorem sound760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node760 node760Labels = Sparse.eval nodeValue760 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 760) = mixedMoment B node760 node760Labels := rfl
  simpa [nodeValue760, Sparse.eval] using hc.symm

theorem sound761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node761 node761Labels = Sparse.eval nodeValue761 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 761) = mixedMoment B node761 node761Labels := rfl
  simpa [nodeValue761, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node783 node783Labels = Sparse.eval nodeValue783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 783) = mixedMoment B node783 node783Labels := rfl
  simpa [nodeValue783, Sparse.eval] using hc.symm

theorem sound787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node787 node787Labels = Sparse.eval nodeValue787 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 787) = mixedMoment B node787 node787Labels := rfl
  simpa [nodeValue787, Sparse.eval] using hc.symm

theorem sound790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node790 node790Labels = Sparse.eval nodeValue790 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 790) = mixedMoment B node790 node790Labels := rfl
  simpa [nodeValue790, Sparse.eval] using hc.symm

theorem sound798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node798 node798Labels = Sparse.eval nodeValue798 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 798) = mixedMoment B node798 node798Labels := rfl
  simpa [nodeValue798, Sparse.eval] using hc.symm

theorem sound803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node803 node803Labels = Sparse.eval nodeValue803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 803) = mixedMoment B node803 node803Labels := rfl
  simpa [nodeValue803, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node840 node840Labels = Sparse.eval nodeValue840 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 840) = mixedMoment B node840 node840Labels := rfl
  simpa [nodeValue840, Sparse.eval] using hc.symm

theorem sound841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node841 node841Labels = Sparse.eval nodeValue841 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 841) = mixedMoment B node841 node841Labels := rfl
  simpa [nodeValue841, Sparse.eval] using hc.symm

theorem sound847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node847 node847Labels = Sparse.eval nodeValue847 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 847) = mixedMoment B node847 node847Labels := rfl
  simpa [nodeValue847, Sparse.eval] using hc.symm

theorem sound848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node848 node848Labels = Sparse.eval nodeValue848 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 848) = mixedMoment B node848 node848Labels := rfl
  simpa [nodeValue848, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node998 node998Labels = Sparse.eval nodeValue998 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 998) = mixedMoment B node998 node998Labels := rfl
  simpa [nodeValue998, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1073 node1073Labels = Sparse.eval nodeValue1073 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1073) = mixedMoment B node1073 node1073Labels := rfl
  simpa [nodeValue1073, Sparse.eval] using hc.symm

theorem sound1079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1079 node1079Labels = Sparse.eval nodeValue1079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1079) = mixedMoment B node1079 node1079Labels := rfl
  simpa [nodeValue1079, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1600 node1600Labels = Sparse.eval nodeValue1600 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1600) = mixedMoment B node1600 node1600Labels := rfl
  simpa [nodeValue1600, Sparse.eval] using hc.symm

theorem sound1648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1648 node1648Labels = Sparse.eval nodeValue1648 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1648) = mixedMoment B node1648 node1648Labels := rfl
  simpa [nodeValue1648, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1708 node1708Labels = Sparse.eval nodeValue1708 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1708) = mixedMoment B node1708 node1708Labels := rfl
  simpa [nodeValue1708, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node537 node537Labels = Sparse.eval nodeValue537 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 537) = mixedMoment B node537 node537Labels := rfl
  simpa [nodeValue537, Sparse.eval] using hc.symm

theorem sound542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node542 node542Labels = Sparse.eval nodeValue542 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 542) = mixedMoment B node542 node542Labels := rfl
  simpa [nodeValue542, Sparse.eval] using hc.symm

theorem sound544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node544 node544Labels = Sparse.eval nodeValue544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 544) = mixedMoment B node544 node544Labels := rfl
  simpa [nodeValue544, Sparse.eval] using hc.symm

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

theorem sound4068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4068 node4068Labels = Sparse.eval nodeValue4068 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4068) = mixedMoment B node4068 node4068Labels := rfl
  simpa [nodeValue4068, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4125 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4125 node4125Labels = 0 := by
  exact mixedMoment_order_one B hB node4125 node4125Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4100 node4100Labels = Sparse.eval nodeValue4100 (mixedVector B) := by
  have h := singleton4100 B _hB
  rw [sound537 B _hB _hF, sound662 B _hB _hF] at h
  norm_num [nodeValue4100, nodeValue537, nodeValue662, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4105 node4105Labels = Sparse.eval nodeValue4105 (mixedVector B) := by
  have h := singleton4105 B _hB
  rw [sound542 B _hB _hF, sound681 B _hB _hF] at h
  norm_num [nodeValue4105, nodeValue542, nodeValue681, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4107 node4107Labels = Sparse.eval nodeValue4107 (mixedVector B) := by
  have h := singleton4107 B _hB
  rw [sound544 B _hB _hF, sound682 B _hB _hF] at h
  norm_num [nodeValue4107, nodeValue544, nodeValue682, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4125 node4125Labels = Sparse.eval nodeValue4125 (mixedVector B) := by
  simpa only [nodeValue4125, Sparse.eval_nil] using zero4125 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4216 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4216 node4216Labels = 0 := by
  exact mixedMoment_order_one B hB node4216 node4216Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4199 node4199Labels = Sparse.eval nodeValue4199 (mixedVector B) := by
  have h := singleton4199 B _hB
  rw [sound702 B _hB _hF, sound760 B _hB _hF] at h
  norm_num [nodeValue4199, nodeValue702, nodeValue760, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4201 node4201Labels = Sparse.eval nodeValue4201 (mixedVector B) := by
  have h := singleton4201 B _hB
  rw [sound704 B _hB _hF, sound761 B _hB _hF] at h
  norm_num [nodeValue4201, nodeValue704, nodeValue761, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4216 node4216Labels = Sparse.eval nodeValue4216 (mixedVector B) := by
  simpa only [nodeValue4216, Sparse.eval_nil] using zero4216 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4263 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4263 node4263Labels = 0 := by
  exact mixedMoment_order_one B hB node4263 node4263Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4267 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4267 node4267Labels = 0 := by
  exact mixedMoment_order_one B hB node4267 node4267Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4232 node4232Labels = Sparse.eval nodeValue4232 (mixedVector B) := by
  have h := singleton4232 B _hB
  rw [sound732 B _hB _hF, sound798 B _hB _hF] at h
  norm_num [nodeValue4232, nodeValue732, nodeValue798, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4237 node4237Labels = Sparse.eval nodeValue4237 (mixedVector B) := by
  have h := singleton4237 B _hB
  rw [sound737 B _hB _hF, sound840 B _hB _hF] at h
  norm_num [nodeValue4237, nodeValue737, nodeValue840, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4239 node4239Labels = Sparse.eval nodeValue4239 (mixedVector B) := by
  have h := singleton4239 B _hB
  rw [sound739 B _hB _hF, sound841 B _hB _hF] at h
  norm_num [nodeValue4239, nodeValue739, nodeValue841, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4249 node4249Labels = Sparse.eval nodeValue4249 (mixedVector B) := by
  have h := singleton4249 B _hB
  rw [sound783 B _hB _hF, sound803 B _hB _hF] at h
  norm_num [nodeValue4249, nodeValue783, nodeValue803, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4253 node4253Labels = Sparse.eval nodeValue4253 (mixedVector B) := by
  have h := singleton4253 B _hB
  rw [sound787 B _hB _hF, sound847 B _hB _hF] at h
  norm_num [nodeValue4253, nodeValue787, nodeValue847, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4256 node4256Labels = Sparse.eval nodeValue4256 (mixedVector B) := by
  have h := singleton4256 B _hB
  rw [sound790 B _hB _hF, sound848 B _hB _hF] at h
  norm_num [nodeValue4256, nodeValue790, nodeValue848, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4263 node4263Labels = Sparse.eval nodeValue4263 (mixedVector B) := by
  simpa only [nodeValue4263, Sparse.eval_nil] using zero4263 B _hB _hF

theorem sound4267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4267 node4267Labels = Sparse.eval nodeValue4267 (mixedVector B) := by
  simpa only [nodeValue4267, Sparse.eval_nil] using zero4267 B _hB _hF

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

theorem sound4417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4417 node4417Labels = Sparse.eval nodeValue4417 (mixedVector B) := by
  have h := singleton4417 B _hB
  rw [sound998 B _hB _hF, sound1600 B _hB _hF] at h
  norm_num [nodeValue4417, nodeValue998, nodeValue1600, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4497 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4497 node4497Labels = 0 := by
  exact mixedMoment_order_one B hB node4497 node4497Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4489 node4489Labels = Sparse.eval nodeValue4489 (mixedVector B) := by
  have h := singleton4489 B _hB
  rw [sound1073 B _hB _hF, sound1648 B _hB _hF] at h
  norm_num [nodeValue4489, nodeValue1073, nodeValue1648, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4495 node4495Labels = Sparse.eval nodeValue4495 (mixedVector B) := by
  have h := singleton4495 B _hB
  rw [sound1079 B _hB _hF, sound1708 B _hB _hF] at h
  norm_num [nodeValue4495, nodeValue1079, nodeValue1708, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4497 node4497Labels = Sparse.eval nodeValue4497 (mixedVector B) := by
  simpa only [nodeValue4497, Sparse.eval_nil] using zero4497 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources56
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1815 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1815 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1815 + difference 0 1) (sourceB1815 + difference 1 0) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4489) := by
    have ha : (tripleCharges (sourceA1815 + difference 0 1) (sourceB1815 + difference 1 0) sourceC1815) = raw26214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26214; decide +kernel
    rw [ha]
    exact (canonical26214 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1815 + difference 0 2) (sourceB1815 + difference 2 0) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1815 + difference 0 2) (sourceB1815 + difference 2 0) sourceC1815) = raw26215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26215; decide +kernel
    rw [ha]
    exact (canonical26215 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1815 + difference 0 3) (sourceB1815 + difference 3 0) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1815 + difference 0 3) (sourceB1815 + difference 3 0) sourceC1815) = raw26216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26216; decide +kernel
    rw [ha]
    exact (canonical26216 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1815 + difference 0 4) (sourceB1815 + difference 4 0) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1815 + difference 0 4) (sourceB1815 + difference 4 0) sourceC1815) = raw26217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26217; decide +kernel
    rw [ha]
    exact (canonical26217 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1815 + difference 0 5) (sourceB1815 + difference 5 0) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1815 + difference 0 5) (sourceB1815 + difference 5 0) sourceC1815) = raw26218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26218; decide +kernel
    rw [ha]
    exact (canonical26218 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1815 + difference 1 0) (sourceB1815 + difference 0 1) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4125) := by
    have ha : (tripleCharges (sourceA1815 + difference 1 0) (sourceB1815 + difference 0 1) sourceC1815) = raw26219 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26219; decide +kernel
    rw [ha]
    exact (canonical26219 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1815 + difference 1 2) (sourceB1815 + difference 2 1) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4216) := by
    have ha : (tripleCharges (sourceA1815 + difference 1 2) (sourceB1815 + difference 2 1) sourceC1815) = raw26220 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26220; decide +kernel
    rw [ha]
    exact (canonical26220 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1815 + difference 1 3) (sourceB1815 + difference 3 1) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4267) := by
    have ha : (tripleCharges (sourceA1815 + difference 1 3) (sourceB1815 + difference 3 1) sourceC1815) = raw26221 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26221; decide +kernel
    rw [ha]
    exact (canonical26221 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1815 + difference 1 4) (sourceB1815 + difference 4 1) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4267) := by
    have ha : (tripleCharges (sourceA1815 + difference 1 4) (sourceB1815 + difference 4 1) sourceC1815) = raw26222 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26222; decide +kernel
    rw [ha]
    exact (canonical26222 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1815 + difference 1 5) (sourceB1815 + difference 5 1) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (tripleCharges (sourceA1815 + difference 1 5) (sourceB1815 + difference 5 1) sourceC1815) = raw26223 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26223; decide +kernel
    rw [ha]
    exact (canonical26223 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1815 + difference 2 0) (sourceB1815 + difference 0 2) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4100) := by
    have ha : (tripleCharges (sourceA1815 + difference 2 0) (sourceB1815 + difference 0 2) sourceC1815) = raw26224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26224; decide +kernel
    rw [ha]
    exact (canonical26224 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1815 + difference 2 1) (sourceB1815 + difference 1 2) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4232) := by
    have ha : (tripleCharges (sourceA1815 + difference 2 1) (sourceB1815 + difference 1 2) sourceC1815) = raw26225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26225; decide +kernel
    rw [ha]
    exact (canonical26225 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1815 + difference 2 3) (sourceB1815 + difference 3 2) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA1815 + difference 2 3) (sourceB1815 + difference 3 2) sourceC1815) = raw26226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26226; decide +kernel
    rw [ha]
    exact (canonical26226 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1815 + difference 2 4) (sourceB1815 + difference 4 2) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA1815 + difference 2 4) (sourceB1815 + difference 4 2) sourceC1815) = raw26227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26227; decide +kernel
    rw [ha]
    exact (canonical26227 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1815 + difference 2 5) (sourceB1815 + difference 5 2) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4263) := by
    have ha : (tripleCharges (sourceA1815 + difference 2 5) (sourceB1815 + difference 5 2) sourceC1815) = raw26228 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26228; decide +kernel
    rw [ha]
    exact (canonical26228 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1815 + difference 3 0) (sourceB1815 + difference 0 3) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4107) := by
    have ha : (tripleCharges (sourceA1815 + difference 3 0) (sourceB1815 + difference 0 3) sourceC1815) = raw26229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26229; decide +kernel
    rw [ha]
    exact (canonical26229 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1815 + difference 3 1) (sourceB1815 + difference 1 3) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4239) := by
    have ha : (tripleCharges (sourceA1815 + difference 3 1) (sourceB1815 + difference 1 3) sourceC1815) = raw26230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26230; decide +kernel
    rw [ha]
    exact (canonical26230 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1815 + difference 3 2) (sourceB1815 + difference 2 3) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4201) := by
    have ha : (tripleCharges (sourceA1815 + difference 3 2) (sourceB1815 + difference 2 3) sourceC1815) = raw26231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26231; decide +kernel
    rw [ha]
    exact (canonical26231 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1815 + difference 3 4) (sourceB1815 + difference 4 3) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4256) := by
    have ha : (tripleCharges (sourceA1815 + difference 3 4) (sourceB1815 + difference 4 3) sourceC1815) = raw26232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26232; decide +kernel
    rw [ha]
    exact (canonical26232 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1815 + difference 3 5) (sourceB1815 + difference 5 3) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4267) := by
    have ha : (tripleCharges (sourceA1815 + difference 3 5) (sourceB1815 + difference 5 3) sourceC1815) = raw26233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26233; decide +kernel
    rw [ha]
    exact (canonical26233 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1815 + difference 4 0) (sourceB1815 + difference 0 4) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4107) := by
    have ha : (tripleCharges (sourceA1815 + difference 4 0) (sourceB1815 + difference 0 4) sourceC1815) = raw26234 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26234; decide +kernel
    rw [ha]
    exact (canonical26234 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1815 + difference 4 1) (sourceB1815 + difference 1 4) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4239) := by
    have ha : (tripleCharges (sourceA1815 + difference 4 1) (sourceB1815 + difference 1 4) sourceC1815) = raw26235 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26235; decide +kernel
    rw [ha]
    exact (canonical26235 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1815 + difference 4 2) (sourceB1815 + difference 2 4) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4201) := by
    have ha : (tripleCharges (sourceA1815 + difference 4 2) (sourceB1815 + difference 2 4) sourceC1815) = raw26236 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26236; decide +kernel
    rw [ha]
    exact (canonical26236 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1815 + difference 4 3) (sourceB1815 + difference 3 4) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4256) := by
    have ha : (tripleCharges (sourceA1815 + difference 4 3) (sourceB1815 + difference 3 4) sourceC1815) = raw26237 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26237; decide +kernel
    rw [ha]
    exact (canonical26237 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1815 + difference 4 5) (sourceB1815 + difference 5 4) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4267) := by
    have ha : (tripleCharges (sourceA1815 + difference 4 5) (sourceB1815 + difference 5 4) sourceC1815) = raw26238 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26238; decide +kernel
    rw [ha]
    exact (canonical26238 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1815 + difference 5 0) (sourceB1815 + difference 0 5) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4105) := by
    have ha : (tripleCharges (sourceA1815 + difference 5 0) (sourceB1815 + difference 0 5) sourceC1815) = raw26239 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26239; decide +kernel
    rw [ha]
    exact (canonical26239 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1815 + difference 5 1) (sourceB1815 + difference 1 5) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4237) := by
    have ha : (tripleCharges (sourceA1815 + difference 5 1) (sourceB1815 + difference 1 5) sourceC1815) = raw26240 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26240; decide +kernel
    rw [ha]
    exact (canonical26240 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1815 + difference 5 2) (sourceB1815 + difference 2 5) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4199) := by
    have ha : (tripleCharges (sourceA1815 + difference 5 2) (sourceB1815 + difference 2 5) sourceC1815) = raw26241 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26241; decide +kernel
    rw [ha]
    exact (canonical26241 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1815 + difference 5 3) (sourceB1815 + difference 3 5) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4253) := by
    have ha : (tripleCharges (sourceA1815 + difference 5 3) (sourceB1815 + difference 3 5) sourceC1815) = raw26242 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26242; decide +kernel
    rw [ha]
    exact (canonical26242 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1815 + difference 5 4) (sourceB1815 + difference 4 5) sourceC1815) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4253) := by
    have ha : (tripleCharges (sourceA1815 + difference 5 4) (sourceB1815 + difference 4 5) sourceC1815) = raw26243 := by
      apply Matrix.ext; unfold tripleCharges sourceA1815 sourceB1815 sourceC1815 difference raw26243; decide +kernel
    rw [ha]
    exact (canonical26243 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1815 sourceB1815 sourceC1815
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1815, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic96
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1536 : Integer.Sparse.reindex keyMap MixedData.row1536 = numericRow1536 := by decide +kernel

theorem numericCheck1536 (x : Master → ℝ) : Integer.Sparse.eval numericRow1536 x =
    (4 : ℝ) * reducedSource1536 x := by
  norm_num [numericRow1536, reducedSource1536, Integer.Sparse.eval, Sparse.eval, nodeValue4068, nodeValue4100, nodeValue4105, nodeValue4107, nodeValue4125, nodeValue4199, nodeValue4201, nodeValue4216, nodeValue4232, nodeValue4237, nodeValue4239, nodeValue4249, nodeValue4253, nodeValue4256, nodeValue4263, nodeValue4267, nodeValue4417, nodeValue4489, nodeValue4495, nodeValue4497]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows96
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1536 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1536 (mixedVector B) = 0 := by
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  have h4100 : mixedVector B (Sum.inr 4100) = Sparse.eval nodeValue4100 (mixedVector B) := by
    change mixedMoment B node4100 node4100Labels = _
    exact sound4100 B hB hF
  have h4105 : mixedVector B (Sum.inr 4105) = Sparse.eval nodeValue4105 (mixedVector B) := by
    change mixedMoment B node4105 node4105Labels = _
    exact sound4105 B hB hF
  have h4107 : mixedVector B (Sum.inr 4107) = Sparse.eval nodeValue4107 (mixedVector B) := by
    change mixedMoment B node4107 node4107Labels = _
    exact sound4107 B hB hF
  have h4125 : mixedVector B (Sum.inr 4125) = Sparse.eval nodeValue4125 (mixedVector B) := by
    change mixedMoment B node4125 node4125Labels = _
    exact sound4125 B hB hF
  have h4199 : mixedVector B (Sum.inr 4199) = Sparse.eval nodeValue4199 (mixedVector B) := by
    change mixedMoment B node4199 node4199Labels = _
    exact sound4199 B hB hF
  have h4201 : mixedVector B (Sum.inr 4201) = Sparse.eval nodeValue4201 (mixedVector B) := by
    change mixedMoment B node4201 node4201Labels = _
    exact sound4201 B hB hF
  have h4216 : mixedVector B (Sum.inr 4216) = Sparse.eval nodeValue4216 (mixedVector B) := by
    change mixedMoment B node4216 node4216Labels = _
    exact sound4216 B hB hF
  have h4232 : mixedVector B (Sum.inr 4232) = Sparse.eval nodeValue4232 (mixedVector B) := by
    change mixedMoment B node4232 node4232Labels = _
    exact sound4232 B hB hF
  have h4237 : mixedVector B (Sum.inr 4237) = Sparse.eval nodeValue4237 (mixedVector B) := by
    change mixedMoment B node4237 node4237Labels = _
    exact sound4237 B hB hF
  have h4239 : mixedVector B (Sum.inr 4239) = Sparse.eval nodeValue4239 (mixedVector B) := by
    change mixedMoment B node4239 node4239Labels = _
    exact sound4239 B hB hF
  have h4249 : mixedVector B (Sum.inr 4249) = Sparse.eval nodeValue4249 (mixedVector B) := by
    change mixedMoment B node4249 node4249Labels = _
    exact sound4249 B hB hF
  have h4253 : mixedVector B (Sum.inr 4253) = Sparse.eval nodeValue4253 (mixedVector B) := by
    change mixedMoment B node4253 node4253Labels = _
    exact sound4253 B hB hF
  have h4256 : mixedVector B (Sum.inr 4256) = Sparse.eval nodeValue4256 (mixedVector B) := by
    change mixedMoment B node4256 node4256Labels = _
    exact sound4256 B hB hF
  have h4263 : mixedVector B (Sum.inr 4263) = Sparse.eval nodeValue4263 (mixedVector B) := by
    change mixedMoment B node4263 node4263Labels = _
    exact sound4263 B hB hF
  have h4267 : mixedVector B (Sum.inr 4267) = Sparse.eval nodeValue4267 (mixedVector B) := by
    change mixedMoment B node4267 node4267Labels = _
    exact sound4267 B hB hF
  have h4417 : mixedVector B (Sum.inr 4417) = Sparse.eval nodeValue4417 (mixedVector B) := by
    change mixedMoment B node4417 node4417Labels = _
    exact sound4417 B hB hF
  have h4489 : mixedVector B (Sum.inr 4489) = Sparse.eval nodeValue4489 (mixedVector B) := by
    change mixedMoment B node4489 node4489Labels = _
    exact sound4489 B hB hF
  have h4495 : mixedVector B (Sum.inr 4495) = Sparse.eval nodeValue4495 (mixedVector B) := by
    change mixedMoment B node4495 node4495Labels = _
    exact sound4495 B hB hF
  have h4497 : mixedVector B (Sum.inr 4497) = Sparse.eval nodeValue4497 (mixedVector B) := by
    change mixedMoment B node4497 node4497Labels = _
    exact sound4497 B hB hF
  simpa only [sourceForm1815, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4068, h4100, h4105, h4107, h4125, h4199, h4201, h4216, h4232, h4237, h4239, h4249, h4253, h4256, h4263, h4267, h4417, h4489, h4495, h4497, reducedSource1536] using sourceEq1815 B hB

theorem rowSound1536_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1536 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1536, numericCheck1536, reducedZero1536 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1536_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1536_e_oai
