-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1794_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:20:52.975187+00:00
-- url     : https://prove2.me/submissions/c9ca9c7f-114d-433e-ba1c-bfad05ccd626

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E122
import Definitions.Def_OAIQ106E130
import Definitions.Def_OAIQ106E137
import Definitions.Def_OAIQ106E138
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1812 raw1812Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw1812 raw1812Labels = mixedMoment B raw1812step0 raw1812step0Labels := by
      have ha : raw1812step0 = (fun i j => raw1812 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1812step0 raw1812; decide +kernel
      have hl : raw1812step0Labels = raw1812Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1812 raw1812Labels permutation152 permutation4
    mixedMoment B raw1812step0 raw1812step0Labels = mixedMoment B raw1812step1 raw1812step1Labels := by
      have ha : raw1812step1 = raw1812step0 := by apply Matrix.ext; unfold raw1812step1 raw1812step0; decide +kernel
      have hl : raw1812step0Labels = labelEmbedding7 ∘ raw1812step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1812step0 raw1812step0Labels raw1812step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4887 node4887Labels := by rfl

theorem canonical1813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1813 raw1813Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw1813 raw1813Labels = mixedMoment B raw1813step0 raw1813step0Labels := by
      have ha : raw1813step0 = (fun i j => raw1813 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1813step0 raw1813; decide +kernel
      have hl : raw1813step0Labels = raw1813Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1813 raw1813Labels permutation152 permutation4
    _ = mixedMoment B node2243 node2243Labels := by rfl

theorem canonical1814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1814 raw1814Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw1814 raw1814Labels = mixedMoment B raw1814step0 raw1814step0Labels := by
      have ha : raw1814step0 = (fun i j => raw1814 (permutation212 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1814step0 raw1814; decide +kernel
      have hl : raw1814step0Labels = raw1814Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1814 raw1814Labels permutation212 permutation6
    mixedMoment B raw1814step0 raw1814step0Labels = mixedMoment B raw1814step1 raw1814step1Labels := by
      have ha : raw1814step1 = -raw1814step0 := by apply Matrix.ext; change ∀ i j, raw1814step1 i j = -(raw1814step0 i j); unfold raw1814step1 raw1814step0; decide +kernel
      have hl : raw1814step1Labels = raw1814step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1814step1 raw1814step1Labels = mixedMoment B raw1814step2 raw1814step2Labels := by
      have ha : raw1814step2 = raw1814step1 := by apply Matrix.ext; unfold raw1814step2 raw1814step1; decide +kernel
      have hl : raw1814step1Labels = labelEmbedding1 ∘ raw1814step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1814step1 raw1814step1Labels raw1814step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2243 node2243Labels := by rfl

theorem canonical1815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1815 raw1815Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw1815 raw1815Labels = mixedMoment B raw1815step0 raw1815step0Labels := by
      have ha : raw1815step0 = (fun i j => raw1815 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1815step0 raw1815; decide +kernel
      have hl : raw1815step0Labels = raw1815Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1815 raw1815Labels permutation32 permutation4
    mixedMoment B raw1815step0 raw1815step0Labels = mixedMoment B raw1815step1 raw1815step1Labels := by
      have ha : raw1815step1 = raw1815step0 := by apply Matrix.ext; unfold raw1815step1 raw1815step0; decide +kernel
      have hl : raw1815step0Labels = labelEmbedding7 ∘ raw1815step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1815step0 raw1815step0Labels raw1815step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical1816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1816 raw1816Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw1816 raw1816Labels = mixedMoment B raw1816step0 raw1816step0Labels := by
      have ha : raw1816step0 = (fun i j => raw1816 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1816step0 raw1816; decide +kernel
      have hl : raw1816step0Labels = raw1816Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1816 raw1816Labels permutation32 permutation4
    _ = mixedMoment B node2244 node2244Labels := by rfl

theorem canonical1817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1817 raw1817Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw1817 raw1817Labels = mixedMoment B raw1817step0 raw1817step0Labels := by
      have ha : raw1817step0 = (fun i j => raw1817 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1817step0 raw1817; decide +kernel
      have hl : raw1817step0Labels = raw1817Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1817 raw1817Labels permutation44 permutation6
    mixedMoment B raw1817step0 raw1817step0Labels = mixedMoment B raw1817step1 raw1817step1Labels := by
      have ha : raw1817step1 = -raw1817step0 := by apply Matrix.ext; change ∀ i j, raw1817step1 i j = -(raw1817step0 i j); unfold raw1817step1 raw1817step0; decide +kernel
      have hl : raw1817step1Labels = raw1817step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1817step1 raw1817step1Labels = mixedMoment B raw1817step2 raw1817step2Labels := by
      have ha : raw1817step2 = raw1817step1 := by apply Matrix.ext; unfold raw1817step2 raw1817step1; decide +kernel
      have hl : raw1817step1Labels = labelEmbedding1 ∘ raw1817step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1817step1 raw1817step1Labels raw1817step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

theorem canonical1818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1818 raw1818Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw1818 raw1818Labels = mixedMoment B raw1818step0 raw1818step0Labels := by
      have ha : raw1818step0 = (fun i j => raw1818 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1818step0 raw1818; decide +kernel
      have hl : raw1818step0Labels = raw1818Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1818 raw1818Labels permutation32 permutation4
    mixedMoment B raw1818step0 raw1818step0Labels = mixedMoment B raw1818step1 raw1818step1Labels := by
      have ha : raw1818step1 = raw1818step0 := by apply Matrix.ext; unfold raw1818step1 raw1818step0; decide +kernel
      have hl : raw1818step0Labels = labelEmbedding7 ∘ raw1818step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1818step0 raw1818step0Labels raw1818step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical1819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1819 raw1819Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw1819 raw1819Labels = mixedMoment B raw1819step0 raw1819step0Labels := by
      have ha : raw1819step0 = (fun i j => raw1819 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1819step0 raw1819; decide +kernel
      have hl : raw1819step0Labels = raw1819Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1819 raw1819Labels permutation32 permutation4
    _ = mixedMoment B node2245 node2245Labels := by rfl

theorem canonical1820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1820 raw1820Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw1820 raw1820Labels = mixedMoment B raw1820step0 raw1820step0Labels := by
      have ha : raw1820step0 = (fun i j => raw1820 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1820step0 raw1820; decide +kernel
      have hl : raw1820step0Labels = raw1820Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1820 raw1820Labels permutation50 permutation6
    mixedMoment B raw1820step0 raw1820step0Labels = mixedMoment B raw1820step1 raw1820step1Labels := by
      have ha : raw1820step1 = -raw1820step0 := by apply Matrix.ext; change ∀ i j, raw1820step1 i j = -(raw1820step0 i j); unfold raw1820step1 raw1820step0; decide +kernel
      have hl : raw1820step1Labels = raw1820step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1820step1 raw1820step1Labels = mixedMoment B raw1820step2 raw1820step2Labels := by
      have ha : raw1820step2 = raw1820step1 := by apply Matrix.ext; unfold raw1820step2 raw1820step1; decide +kernel
      have hl : raw1820step1Labels = labelEmbedding1 ∘ raw1820step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1820step1 raw1820step1Labels raw1820step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

theorem canonical1821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1821 raw1821Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw1821 raw1821Labels = mixedMoment B raw1821step0 raw1821step0Labels := by
      have ha : raw1821step0 = (fun i j => raw1821 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1821step0 raw1821; decide +kernel
      have hl : raw1821step0Labels = raw1821Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1821 raw1821Labels permutation8 permutation4
    mixedMoment B raw1821step0 raw1821step0Labels = mixedMoment B raw1821step1 raw1821step1Labels := by
      have ha : raw1821step1 = raw1821step0 := by apply Matrix.ext; unfold raw1821step1 raw1821step0; decide +kernel
      have hl : raw1821step0Labels = labelEmbedding7 ∘ raw1821step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1821step0 raw1821step0Labels raw1821step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

theorem canonical1822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1822 raw1822Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw1822 raw1822Labels = mixedMoment B raw1822step0 raw1822step0Labels := by
      have ha : raw1822step0 = (fun i j => raw1822 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1822step0 raw1822; decide +kernel
      have hl : raw1822step0Labels = raw1822Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1822 raw1822Labels permutation8 permutation4
    _ = mixedMoment B node2247 node2247Labels := by rfl

theorem canonical1823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1823 raw1823Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw1823 raw1823Labels = mixedMoment B raw1823step0 raw1823step0Labels := by
      have ha : raw1823step0 = (fun i j => raw1823 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1823step0 raw1823; decide +kernel
      have hl : raw1823step0Labels = raw1823Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1823 raw1823Labels permutation8 permutation6
    mixedMoment B raw1823step0 raw1823step0Labels = mixedMoment B raw1823step1 raw1823step1Labels := by
      have ha : raw1823step1 = -raw1823step0 := by apply Matrix.ext; change ∀ i j, raw1823step1 i j = -(raw1823step0 i j); unfold raw1823step1 raw1823step0; decide +kernel
      have hl : raw1823step1Labels = raw1823step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1823step1 raw1823step1Labels = mixedMoment B raw1823step2 raw1823step2Labels := by
      have ha : raw1823step2 = raw1823step1 := by apply Matrix.ext; unfold raw1823step2 raw1823step1; decide +kernel
      have hl : raw1823step1Labels = labelEmbedding1 ∘ raw1823step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1823step1 raw1823step1Labels raw1823step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2290 node2290Labels := by rfl

theorem canonical1824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1824 raw1824Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw1824 raw1824Labels = mixedMoment B raw1824step0 raw1824step0Labels := by
      have ha : raw1824step0 = (fun i j => raw1824 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1824step0 raw1824; decide +kernel
      have hl : raw1824step0Labels = raw1824Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1824 raw1824Labels permutation8 permutation4
    mixedMoment B raw1824step0 raw1824step0Labels = mixedMoment B raw1824step1 raw1824step1Labels := by
      have ha : raw1824step1 = raw1824step0 := by apply Matrix.ext; unfold raw1824step1 raw1824step0; decide +kernel
      have hl : raw1824step0Labels = labelEmbedding7 ∘ raw1824step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1824step0 raw1824step0Labels raw1824step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

theorem canonical1825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1825 raw1825Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw1825 raw1825Labels = mixedMoment B raw1825step0 raw1825step0Labels := by
      have ha : raw1825step0 = (fun i j => raw1825 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1825step0 raw1825; decide +kernel
      have hl : raw1825step0Labels = raw1825Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1825 raw1825Labels permutation8 permutation4
    _ = mixedMoment B node2266 node2266Labels := by rfl

theorem canonical1826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1826 raw1826Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw1826 raw1826Labels = mixedMoment B raw1826step0 raw1826step0Labels := by
      have ha : raw1826step0 = (fun i j => raw1826 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1826step0 raw1826; decide +kernel
      have hl : raw1826step0Labels = raw1826Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1826 raw1826Labels permutation12 permutation6
    mixedMoment B raw1826step0 raw1826step0Labels = mixedMoment B raw1826step1 raw1826step1Labels := by
      have ha : raw1826step1 = -raw1826step0 := by apply Matrix.ext; change ∀ i j, raw1826step1 i j = -(raw1826step0 i j); unfold raw1826step1 raw1826step0; decide +kernel
      have hl : raw1826step1Labels = raw1826step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1826step1 raw1826step1Labels = mixedMoment B raw1826step2 raw1826step2Labels := by
      have ha : raw1826step2 = raw1826step1 := by apply Matrix.ext; unfold raw1826step2 raw1826step1; decide +kernel
      have hl : raw1826step1Labels = labelEmbedding1 ∘ raw1826step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1826step1 raw1826step1Labels raw1826step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2278 node2278Labels := by rfl

theorem canonical1827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1827 raw1827Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw1827 raw1827Labels = mixedMoment B raw1827step0 raw1827step0Labels := by
      have ha : raw1827step0 = (fun i j => raw1827 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1827step0 raw1827; decide +kernel
      have hl : raw1827step0Labels = raw1827Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1827 raw1827Labels permutation8 permutation4
    mixedMoment B raw1827step0 raw1827step0Labels = mixedMoment B raw1827step1 raw1827step1Labels := by
      have ha : raw1827step1 = raw1827step0 := by apply Matrix.ext; unfold raw1827step1 raw1827step0; decide +kernel
      have hl : raw1827step0Labels = labelEmbedding7 ∘ raw1827step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1827step0 raw1827step0Labels raw1827step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

theorem canonical1828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1828 raw1828Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw1828 raw1828Labels = mixedMoment B raw1828step0 raw1828step0Labels := by
      have ha : raw1828step0 = (fun i j => raw1828 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1828step0 raw1828; decide +kernel
      have hl : raw1828step0Labels = raw1828Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1828 raw1828Labels permutation8 permutation4
    _ = mixedMoment B node2279 node2279Labels := by rfl

theorem canonical1829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1829 raw1829Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw1829 raw1829Labels = mixedMoment B raw1829step0 raw1829step0Labels := by
      have ha : raw1829step0 = (fun i j => raw1829 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1829step0 raw1829; decide +kernel
      have hl : raw1829step0Labels = raw1829Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1829 raw1829Labels permutation13 permutation6
    mixedMoment B raw1829step0 raw1829step0Labels = mixedMoment B raw1829step1 raw1829step1Labels := by
      have ha : raw1829step1 = -raw1829step0 := by apply Matrix.ext; change ∀ i j, raw1829step1 i j = -(raw1829step0 i j); unfold raw1829step1 raw1829step0; decide +kernel
      have hl : raw1829step1Labels = raw1829step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1829step1 raw1829step1Labels = mixedMoment B raw1829step2 raw1829step2Labels := by
      have ha : raw1829step2 = raw1829step1 := by apply Matrix.ext; unfold raw1829step2 raw1829step1; decide +kernel
      have hl : raw1829step1Labels = labelEmbedding1 ∘ raw1829step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1829step1 raw1829step1Labels raw1829step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2279 node2279Labels := by rfl

theorem canonical1830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1830 raw1830Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw1830 raw1830Labels = mixedMoment B raw1830step0 raw1830step0Labels := by
      have ha : raw1830step0 = (fun i j => raw1830 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1830step0 raw1830; decide +kernel
      have hl : raw1830step0Labels = raw1830Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1830 raw1830Labels permutation2 permutation4
    mixedMoment B raw1830step0 raw1830step0Labels = mixedMoment B raw1830step1 raw1830step1Labels := by
      have ha : raw1830step1 = raw1830step0 := by apply Matrix.ext; unfold raw1830step1 raw1830step0; decide +kernel
      have hl : raw1830step0Labels = labelEmbedding7 ∘ raw1830step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1830step0 raw1830step0Labels raw1830step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

theorem canonical1831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1831 raw1831Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw1831 raw1831Labels = mixedMoment B raw1831step0 raw1831step0Labels := by
      have ha : raw1831step0 = (fun i j => raw1831 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1831step0 raw1831; decide +kernel
      have hl : raw1831step0Labels = raw1831Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1831 raw1831Labels permutation2 permutation4
    _ = mixedMoment B node2281 node2281Labels := by rfl

theorem canonical1832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1832 raw1832Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw1832 raw1832Labels = mixedMoment B raw1832step0 raw1832step0Labels := by
      have ha : raw1832step0 = (fun i j => raw1832 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1832step0 raw1832; decide +kernel
      have hl : raw1832step0Labels = raw1832Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1832 raw1832Labels permutation3 permutation6
    mixedMoment B raw1832step0 raw1832step0Labels = mixedMoment B raw1832step1 raw1832step1Labels := by
      have ha : raw1832step1 = -raw1832step0 := by apply Matrix.ext; change ∀ i j, raw1832step1 i j = -(raw1832step0 i j); unfold raw1832step1 raw1832step0; decide +kernel
      have hl : raw1832step1Labels = raw1832step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1832step1 raw1832step1Labels = mixedMoment B raw1832step2 raw1832step2Labels := by
      have ha : raw1832step2 = raw1832step1 := by apply Matrix.ext; unfold raw1832step2 raw1832step1; decide +kernel
      have hl : raw1832step1Labels = labelEmbedding1 ∘ raw1832step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1832step1 raw1832step1Labels raw1832step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2294 node2294Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4887 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4887 node4887Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2243 node2243Labels + mixedMoment B node2243 node2243Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1812 singletonSmall4887
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4887) = raw1812Labels := by decide +kernel
  rw [hl, canonical1812 B hB] at h
  have hc0 : mixedMoment B raw1812 (Fin.cases (0 : Fin 2) singletonSmall4887) =
      mixedMoment B node2243 node2243Labels := by
    have ha : raw1812 = raw1813 := by apply Matrix.ext; unfold raw1812 raw1813; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4887 = raw1813Labels := by decide +kernel
    rw [ha, hj, canonical1813 B hB]
  have hc1 : mixedMoment B raw1812 (Fin.cases (1 : Fin 2) singletonSmall4887) =
      mixedMoment B node2243 node2243Labels := by
    have ha : raw1812 = raw1814 := by apply Matrix.ext; unfold raw1812 raw1814; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4887 = raw1814Labels := by decide +kernel
    rw [ha, hj, canonical1814 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4888 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4888 node4888Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2244 node2244Labels + mixedMoment B node2262 node2262Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1815 singletonSmall4888
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4888) = raw1815Labels := by decide +kernel
  rw [hl, canonical1815 B hB] at h
  have hc0 : mixedMoment B raw1815 (Fin.cases (0 : Fin 2) singletonSmall4888) =
      mixedMoment B node2244 node2244Labels := by
    have ha : raw1815 = raw1816 := by apply Matrix.ext; unfold raw1815 raw1816; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4888 = raw1816Labels := by decide +kernel
    rw [ha, hj, canonical1816 B hB]
  have hc1 : mixedMoment B raw1815 (Fin.cases (1 : Fin 2) singletonSmall4888) =
      mixedMoment B node2262 node2262Labels := by
    have ha : raw1815 = raw1817 := by apply Matrix.ext; unfold raw1815 raw1817; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4888 = raw1817Labels := by decide +kernel
    rw [ha, hj, canonical1817 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4889 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4889 node4889Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2245 node2245Labels + mixedMoment B node2277 node2277Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1818 singletonSmall4889
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4889) = raw1818Labels := by decide +kernel
  rw [hl, canonical1818 B hB] at h
  have hc0 : mixedMoment B raw1818 (Fin.cases (0 : Fin 2) singletonSmall4889) =
      mixedMoment B node2245 node2245Labels := by
    have ha : raw1818 = raw1819 := by apply Matrix.ext; unfold raw1818 raw1819; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4889 = raw1819Labels := by decide +kernel
    rw [ha, hj, canonical1819 B hB]
  have hc1 : mixedMoment B raw1818 (Fin.cases (1 : Fin 2) singletonSmall4889) =
      mixedMoment B node2277 node2277Labels := by
    have ha : raw1818 = raw1820 := by apply Matrix.ext; unfold raw1818 raw1820; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4889 = raw1820Labels := by decide +kernel
    rw [ha, hj, canonical1820 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4890 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4890 node4890Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2247 node2247Labels + mixedMoment B node2290 node2290Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1821 singletonSmall4890
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4890) = raw1821Labels := by decide +kernel
  rw [hl, canonical1821 B hB] at h
  have hc0 : mixedMoment B raw1821 (Fin.cases (0 : Fin 2) singletonSmall4890) =
      mixedMoment B node2247 node2247Labels := by
    have ha : raw1821 = raw1822 := by apply Matrix.ext; unfold raw1821 raw1822; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4890 = raw1822Labels := by decide +kernel
    rw [ha, hj, canonical1822 B hB]
  have hc1 : mixedMoment B raw1821 (Fin.cases (1 : Fin 2) singletonSmall4890) =
      mixedMoment B node2290 node2290Labels := by
    have ha : raw1821 = raw1823 := by apply Matrix.ext; unfold raw1821 raw1823; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4890 = raw1823Labels := by decide +kernel
    rw [ha, hj, canonical1823 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4896 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4896 node4896Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2266 node2266Labels + mixedMoment B node2278 node2278Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1824 singletonSmall4896
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4896) = raw1824Labels := by decide +kernel
  rw [hl, canonical1824 B hB] at h
  have hc0 : mixedMoment B raw1824 (Fin.cases (0 : Fin 2) singletonSmall4896) =
      mixedMoment B node2266 node2266Labels := by
    have ha : raw1824 = raw1825 := by apply Matrix.ext; unfold raw1824 raw1825; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4896 = raw1825Labels := by decide +kernel
    rw [ha, hj, canonical1825 B hB]
  have hc1 : mixedMoment B raw1824 (Fin.cases (1 : Fin 2) singletonSmall4896) =
      mixedMoment B node2278 node2278Labels := by
    have ha : raw1824 = raw1826 := by apply Matrix.ext; unfold raw1824 raw1826; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4896 = raw1826Labels := by decide +kernel
    rw [ha, hj, canonical1826 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4898 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4898 node4898Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2279 node2279Labels + mixedMoment B node2279 node2279Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1827 singletonSmall4898
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4898) = raw1827Labels := by decide +kernel
  rw [hl, canonical1827 B hB] at h
  have hc0 : mixedMoment B raw1827 (Fin.cases (0 : Fin 2) singletonSmall4898) =
      mixedMoment B node2279 node2279Labels := by
    have ha : raw1827 = raw1828 := by apply Matrix.ext; unfold raw1827 raw1828; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4898 = raw1828Labels := by decide +kernel
    rw [ha, hj, canonical1828 B hB]
  have hc1 : mixedMoment B raw1827 (Fin.cases (1 : Fin 2) singletonSmall4898) =
      mixedMoment B node2279 node2279Labels := by
    have ha : raw1827 = raw1829 := by apply Matrix.ext; unfold raw1827 raw1829; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4898 = raw1829Labels := by decide +kernel
    rw [ha, hj, canonical1829 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4899 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4899 node4899Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2281 node2281Labels + mixedMoment B node2294 node2294Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1830 singletonSmall4899
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4899) = raw1830Labels := by decide +kernel
  rw [hl, canonical1830 B hB] at h
  have hc0 : mixedMoment B raw1830 (Fin.cases (0 : Fin 2) singletonSmall4899) =
      mixedMoment B node2281 node2281Labels := by
    have ha : raw1830 = raw1831 := by apply Matrix.ext; unfold raw1830 raw1831; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4899 = raw1831Labels := by decide +kernel
    rw [ha, hj, canonical1831 B hB]
  have hc1 : mixedMoment B raw1830 (Fin.cases (1 : Fin 2) singletonSmall4899) =
      mixedMoment B node2294 node2294Labels := by
    have ha : raw1830 = raw1832 := by apply Matrix.ext; unfold raw1830 raw1832; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4899 = raw1832Labels := by decide +kernel
    rw [ha, hj, canonical1832 B hB]
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

theorem sound2279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2279 node2279Labels = Sparse.eval nodeValue2279 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2279) = mixedMoment B node2279 node2279Labels := rfl
  simpa [nodeValue2279, Sparse.eval] using hc.symm

theorem sound2281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2281 node2281Labels = Sparse.eval nodeValue2281 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2281) = mixedMoment B node2281 node2281Labels := rfl
  simpa [nodeValue2281, Sparse.eval] using hc.symm

theorem sound2294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2294 node2294Labels = Sparse.eval nodeValue2294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2294) = mixedMoment B node2294 node2294Labels := rfl
  simpa [nodeValue2294, Sparse.eval] using hc.symm

theorem sound4898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4898 node4898Labels = Sparse.eval nodeValue4898 (mixedVector B) := by
  have h := singleton4898 B _hB
  rw [sound2279 B _hB _hF] at h
  norm_num [nodeValue4898, nodeValue2279, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4899 node4899Labels = Sparse.eval nodeValue4899 (mixedVector B) := by
  have h := singleton4899 B _hB
  rw [sound2281 B _hB _hF, sound2294 B _hB _hF] at h
  norm_num [nodeValue4899, nodeValue2281, nodeValue2294, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2243 node2243Labels = Sparse.eval nodeValue2243 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2243) = mixedMoment B node2243 node2243Labels := rfl
  simpa [nodeValue2243, Sparse.eval] using hc.symm

theorem sound2244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2244 node2244Labels = Sparse.eval nodeValue2244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2244) = mixedMoment B node2244 node2244Labels := rfl
  simpa [nodeValue2244, Sparse.eval] using hc.symm

theorem sound2245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2245 node2245Labels = Sparse.eval nodeValue2245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2245) = mixedMoment B node2245 node2245Labels := rfl
  simpa [nodeValue2245, Sparse.eval] using hc.symm

theorem sound2247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2247 node2247Labels = Sparse.eval nodeValue2247 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2247) = mixedMoment B node2247 node2247Labels := rfl
  simpa [nodeValue2247, Sparse.eval] using hc.symm

theorem sound2262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2262 node2262Labels = Sparse.eval nodeValue2262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2262) = mixedMoment B node2262 node2262Labels := rfl
  simpa [nodeValue2262, Sparse.eval] using hc.symm

theorem sound2266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2266 node2266Labels = Sparse.eval nodeValue2266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2266) = mixedMoment B node2266 node2266Labels := rfl
  simpa [nodeValue2266, Sparse.eval] using hc.symm

theorem sound2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2277 node2277Labels = Sparse.eval nodeValue2277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2277) = mixedMoment B node2277 node2277Labels := rfl
  simpa [nodeValue2277, Sparse.eval] using hc.symm

theorem sound2278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2278 node2278Labels = Sparse.eval nodeValue2278 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2278) = mixedMoment B node2278 node2278Labels := rfl
  simpa [nodeValue2278, Sparse.eval] using hc.symm

theorem sound2290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2290 node2290Labels = Sparse.eval nodeValue2290 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2290) = mixedMoment B node2290 node2290Labels := rfl
  simpa [nodeValue2290, Sparse.eval] using hc.symm

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

theorem sound4705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4705 node4705Labels = Sparse.eval nodeValue4705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4705) = mixedMoment B node4705 node4705Labels := rfl
  simpa [nodeValue4705, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4756 node4756Labels = Sparse.eval nodeValue4756 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4756) = mixedMoment B node4756 node4756Labels := rfl
  simpa [nodeValue4756, Sparse.eval] using hc.symm

theorem sound4757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4757 node4757Labels = Sparse.eval nodeValue4757 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4757) = mixedMoment B node4757 node4757Labels := rfl
  simpa [nodeValue4757, Sparse.eval] using hc.symm

theorem sound4761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4761 node4761Labels = Sparse.eval nodeValue4761 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4761) = mixedMoment B node4761 node4761Labels := rfl
  simpa [nodeValue4761, Sparse.eval] using hc.symm

theorem sound4762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4762 node4762Labels = Sparse.eval nodeValue4762 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4762) = mixedMoment B node4762 node4762Labels := rfl
  simpa [nodeValue4762, Sparse.eval] using hc.symm

theorem sound4765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4765 node4765Labels = Sparse.eval nodeValue4765 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4765) = mixedMoment B node4765 node4765Labels := rfl
  simpa [nodeValue4765, Sparse.eval] using hc.symm

theorem sound4768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4768 node4768Labels = Sparse.eval nodeValue4768 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4768) = mixedMoment B node4768 node4768Labels := rfl
  simpa [nodeValue4768, Sparse.eval] using hc.symm

theorem sound4771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4771 node4771Labels = Sparse.eval nodeValue4771 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4771) = mixedMoment B node4771 node4771Labels := rfl
  simpa [nodeValue4771, Sparse.eval] using hc.symm

theorem sound4772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4772 node4772Labels = Sparse.eval nodeValue4772 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4772) = mixedMoment B node4772 node4772Labels := rfl
  simpa [nodeValue4772, Sparse.eval] using hc.symm

theorem sound4773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4773 node4773Labels = Sparse.eval nodeValue4773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4773) = mixedMoment B node4773 node4773Labels := rfl
  simpa [nodeValue4773, Sparse.eval] using hc.symm

theorem sound4774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4774 node4774Labels = Sparse.eval nodeValue4774 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4774) = mixedMoment B node4774 node4774Labels := rfl
  simpa [nodeValue4774, Sparse.eval] using hc.symm

theorem sound4775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4775 node4775Labels = Sparse.eval nodeValue4775 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4775) = mixedMoment B node4775 node4775Labels := rfl
  simpa [nodeValue4775, Sparse.eval] using hc.symm

theorem sound4776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4776 node4776Labels = Sparse.eval nodeValue4776 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4776) = mixedMoment B node4776 node4776Labels := rfl
  simpa [nodeValue4776, Sparse.eval] using hc.symm

theorem sound4777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4777 node4777Labels = Sparse.eval nodeValue4777 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4777) = mixedMoment B node4777 node4777Labels := rfl
  simpa [nodeValue4777, Sparse.eval] using hc.symm

theorem sound4792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4792 node4792Labels = Sparse.eval nodeValue4792 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4792) = mixedMoment B node4792 node4792Labels := rfl
  simpa [nodeValue4792, Sparse.eval] using hc.symm

theorem sound4793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4793 node4793Labels = Sparse.eval nodeValue4793 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4793) = mixedMoment B node4793 node4793Labels := rfl
  simpa [nodeValue4793, Sparse.eval] using hc.symm

theorem sound4795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4795 node4795Labels = Sparse.eval nodeValue4795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4795) = mixedMoment B node4795 node4795Labels := rfl
  simpa [nodeValue4795, Sparse.eval] using hc.symm

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

theorem sound4803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4803 node4803Labels = Sparse.eval nodeValue4803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4803) = mixedMoment B node4803 node4803Labels := rfl
  simpa [nodeValue4803, Sparse.eval] using hc.symm

theorem sound4808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4808 node4808Labels = Sparse.eval nodeValue4808 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4808) = mixedMoment B node4808 node4808Labels := rfl
  simpa [nodeValue4808, Sparse.eval] using hc.symm

theorem sound4815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4815 node4815Labels = Sparse.eval nodeValue4815 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4815) = mixedMoment B node4815 node4815Labels := rfl
  simpa [nodeValue4815, Sparse.eval] using hc.symm

theorem sound4816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4816 node4816Labels = Sparse.eval nodeValue4816 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4816) = mixedMoment B node4816 node4816Labels := rfl
  simpa [nodeValue4816, Sparse.eval] using hc.symm

theorem sound4817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4817 node4817Labels = Sparse.eval nodeValue4817 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4817) = mixedMoment B node4817 node4817Labels := rfl
  simpa [nodeValue4817, Sparse.eval] using hc.symm

theorem sound4819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4819 node4819Labels = Sparse.eval nodeValue4819 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4819) = mixedMoment B node4819 node4819Labels := rfl
  simpa [nodeValue4819, Sparse.eval] using hc.symm

theorem sound4821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4821 node4821Labels = Sparse.eval nodeValue4821 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4821) = mixedMoment B node4821 node4821Labels := rfl
  simpa [nodeValue4821, Sparse.eval] using hc.symm

theorem sound4830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4830 node4830Labels = Sparse.eval nodeValue4830 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4830) = mixedMoment B node4830 node4830Labels := rfl
  simpa [nodeValue4830, Sparse.eval] using hc.symm

theorem sound4836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4836 node4836Labels = Sparse.eval nodeValue4836 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4836) = mixedMoment B node4836 node4836Labels := rfl
  simpa [nodeValue4836, Sparse.eval] using hc.symm

theorem sound4844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4844 node4844Labels = Sparse.eval nodeValue4844 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4844) = mixedMoment B node4844 node4844Labels := rfl
  simpa [nodeValue4844, Sparse.eval] using hc.symm

theorem sound4851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4851 node4851Labels = Sparse.eval nodeValue4851 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4851) = mixedMoment B node4851 node4851Labels := rfl
  simpa [nodeValue4851, Sparse.eval] using hc.symm

theorem sound4852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4852 node4852Labels = Sparse.eval nodeValue4852 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4852) = mixedMoment B node4852 node4852Labels := rfl
  simpa [nodeValue4852, Sparse.eval] using hc.symm

theorem sound4853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4853 node4853Labels = Sparse.eval nodeValue4853 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4853) = mixedMoment B node4853 node4853Labels := rfl
  simpa [nodeValue4853, Sparse.eval] using hc.symm

theorem sound4856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4856 node4856Labels = Sparse.eval nodeValue4856 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4856) = mixedMoment B node4856 node4856Labels := rfl
  simpa [nodeValue4856, Sparse.eval] using hc.symm

theorem sound4863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4863 node4863Labels = Sparse.eval nodeValue4863 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4863) = mixedMoment B node4863 node4863Labels := rfl
  simpa [nodeValue4863, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4893 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4893 node4893Labels = 0 := by
  exact mixedMoment_order_one B hB node4893 node4893Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4894 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4894 node4894Labels = 0 := by
  exact mixedMoment_order_one B hB node4894 node4894Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4895 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4895 node4895Labels = 0 := by
  exact mixedMoment_order_one B hB node4895 node4895Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4897 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4897 node4897Labels = 0 := by
  exact mixedMoment_order_one B hB node4897 node4897Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4901 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4901 node4901Labels = 0 := by
  exact mixedMoment_order_one B hB node4901 node4901Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4867 node4867Labels = Sparse.eval nodeValue4867 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4867) = mixedMoment B node4867 node4867Labels := rfl
  simpa [nodeValue4867, Sparse.eval] using hc.symm

theorem sound4872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4872 node4872Labels = Sparse.eval nodeValue4872 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4872) = mixedMoment B node4872 node4872Labels := rfl
  simpa [nodeValue4872, Sparse.eval] using hc.symm

theorem sound4878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4878 node4878Labels = Sparse.eval nodeValue4878 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4878) = mixedMoment B node4878 node4878Labels := rfl
  simpa [nodeValue4878, Sparse.eval] using hc.symm

theorem sound4879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4879 node4879Labels = Sparse.eval nodeValue4879 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4879) = mixedMoment B node4879 node4879Labels := rfl
  simpa [nodeValue4879, Sparse.eval] using hc.symm

theorem sound4880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4880 node4880Labels = Sparse.eval nodeValue4880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4880) = mixedMoment B node4880 node4880Labels := rfl
  simpa [nodeValue4880, Sparse.eval] using hc.symm

theorem sound4881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4881 node4881Labels = Sparse.eval nodeValue4881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4881) = mixedMoment B node4881 node4881Labels := rfl
  simpa [nodeValue4881, Sparse.eval] using hc.symm

theorem sound4884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4884 node4884Labels = Sparse.eval nodeValue4884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4884) = mixedMoment B node4884 node4884Labels := rfl
  simpa [nodeValue4884, Sparse.eval] using hc.symm

theorem sound4885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4885 node4885Labels = Sparse.eval nodeValue4885 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4885) = mixedMoment B node4885 node4885Labels := rfl
  simpa [nodeValue4885, Sparse.eval] using hc.symm

theorem sound4886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4886 node4886Labels = Sparse.eval nodeValue4886 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4886) = mixedMoment B node4886 node4886Labels := rfl
  simpa [nodeValue4886, Sparse.eval] using hc.symm

theorem sound4887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4887 node4887Labels = Sparse.eval nodeValue4887 (mixedVector B) := by
  have h := singleton4887 B _hB
  rw [sound2243 B _hB _hF] at h
  norm_num [nodeValue4887, nodeValue2243, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4888 node4888Labels = Sparse.eval nodeValue4888 (mixedVector B) := by
  have h := singleton4888 B _hB
  rw [sound2244 B _hB _hF, sound2262 B _hB _hF] at h
  norm_num [nodeValue4888, nodeValue2244, nodeValue2262, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4889 node4889Labels = Sparse.eval nodeValue4889 (mixedVector B) := by
  have h := singleton4889 B _hB
  rw [sound2245 B _hB _hF, sound2277 B _hB _hF] at h
  norm_num [nodeValue4889, nodeValue2245, nodeValue2277, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4890 node4890Labels = Sparse.eval nodeValue4890 (mixedVector B) := by
  have h := singleton4890 B _hB
  rw [sound2247 B _hB _hF, sound2290 B _hB _hF] at h
  norm_num [nodeValue4890, nodeValue2247, nodeValue2290, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4891 node4891Labels = Sparse.eval nodeValue4891 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4891) = mixedMoment B node4891 node4891Labels := rfl
  simpa [nodeValue4891, Sparse.eval] using hc.symm

theorem sound4892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4892 node4892Labels = Sparse.eval nodeValue4892 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4892) = mixedMoment B node4892 node4892Labels := rfl
  simpa [nodeValue4892, Sparse.eval] using hc.symm

theorem sound4893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4893 node4893Labels = Sparse.eval nodeValue4893 (mixedVector B) := by
  simpa only [nodeValue4893, Sparse.eval_nil] using zero4893 B _hB _hF

theorem sound4894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4894 node4894Labels = Sparse.eval nodeValue4894 (mixedVector B) := by
  simpa only [nodeValue4894, Sparse.eval_nil] using zero4894 B _hB _hF

theorem sound4895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4895 node4895Labels = Sparse.eval nodeValue4895 (mixedVector B) := by
  simpa only [nodeValue4895, Sparse.eval_nil] using zero4895 B _hB _hF

theorem sound4896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4896 node4896Labels = Sparse.eval nodeValue4896 (mixedVector B) := by
  have h := singleton4896 B _hB
  rw [sound2266 B _hB _hF, sound2278 B _hB _hF] at h
  norm_num [nodeValue4896, nodeValue2266, nodeValue2278, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4897 node4897Labels = Sparse.eval nodeValue4897 (mixedVector B) := by
  simpa only [nodeValue4897, Sparse.eval_nil] using zero4897 B _hB _hF

theorem sound4900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4900 node4900Labels = Sparse.eval nodeValue4900 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4900) = mixedMoment B node4900 node4900Labels := rfl
  simpa [nodeValue4900, Sparse.eval] using hc.symm

theorem sound4901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4901 node4901Labels = Sparse.eval nodeValue4901 (mixedVector B) := by
  simpa only [nodeValue4901, Sparse.eval_nil] using zero4901 B _hB _hF

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

theorem sound4931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4931 node4931Labels = Sparse.eval nodeValue4931 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4931) = mixedMoment B node4931 node4931Labels := rfl
  simpa [nodeValue4931, Sparse.eval] using hc.symm

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

theorem sound4942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4942 node4942Labels = Sparse.eval nodeValue4942 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4942) = mixedMoment B node4942 node4942Labels := rfl
  simpa [nodeValue4942, Sparse.eval] using hc.symm

theorem sound4944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4944 node4944Labels = Sparse.eval nodeValue4944 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4944) = mixedMoment B node4944 node4944Labels := rfl
  simpa [nodeValue4944, Sparse.eval] using hc.symm

theorem sound4945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4945 node4945Labels = Sparse.eval nodeValue4945 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4945) = mixedMoment B node4945 node4945Labels := rfl
  simpa [nodeValue4945, Sparse.eval] using hc.symm

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

theorem sound4955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4955 node4955Labels = Sparse.eval nodeValue4955 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4955) = mixedMoment B node4955 node4955Labels := rfl
  simpa [nodeValue4955, Sparse.eval] using hc.symm

theorem sound4956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4956 node4956Labels = Sparse.eval nodeValue4956 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4956) = mixedMoment B node4956 node4956Labels := rfl
  simpa [nodeValue4956, Sparse.eval] using hc.symm

theorem sound4957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4957 node4957Labels = Sparse.eval nodeValue4957 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4957) = mixedMoment B node4957 node4957Labels := rfl
  simpa [nodeValue4957, Sparse.eval] using hc.symm

theorem sound4958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4958 node4958Labels = Sparse.eval nodeValue4958 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4958) = mixedMoment B node4958 node4958Labels := rfl
  simpa [nodeValue4958, Sparse.eval] using hc.symm

theorem sound4959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4959 node4959Labels = Sparse.eval nodeValue4959 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4959) = mixedMoment B node4959 node4959Labels := rfl
  simpa [nodeValue4959, Sparse.eval] using hc.symm

theorem sound4963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4963 node4963Labels = Sparse.eval nodeValue4963 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4963) = mixedMoment B node4963 node4963Labels := rfl
  simpa [nodeValue4963, Sparse.eval] using hc.symm

theorem sound4964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4964 node4964Labels = Sparse.eval nodeValue4964 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4964) = mixedMoment B node4964 node4964Labels := rfl
  simpa [nodeValue4964, Sparse.eval] using hc.symm

theorem sound4965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4965 node4965Labels = Sparse.eval nodeValue4965 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4965) = mixedMoment B node4965 node4965Labels := rfl
  simpa [nodeValue4965, Sparse.eval] using hc.symm

theorem sound4966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4966 node4966Labels = Sparse.eval nodeValue4966 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4966) = mixedMoment B node4966 node4966Labels := rfl
  simpa [nodeValue4966, Sparse.eval] using hc.symm

theorem sound4975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4975 node4975Labels = Sparse.eval nodeValue4975 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4975) = mixedMoment B node4975 node4975Labels := rfl
  simpa [nodeValue4975, Sparse.eval] using hc.symm

theorem sound4976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4976 node4976Labels = Sparse.eval nodeValue4976 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4976) = mixedMoment B node4976 node4976Labels := rfl
  simpa [nodeValue4976, Sparse.eval] using hc.symm

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

theorem sound5035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5035 node5035Labels = Sparse.eval nodeValue5035 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5035) = mixedMoment B node5035 node5035Labels := rfl
  simpa [nodeValue5035, Sparse.eval] using hc.symm

theorem sound5040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5040 node5040Labels = Sparse.eval nodeValue5040 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5040) = mixedMoment B node5040 node5040Labels := rfl
  simpa [nodeValue5040, Sparse.eval] using hc.symm

theorem sound5041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5041 node5041Labels = Sparse.eval nodeValue5041 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5041) = mixedMoment B node5041 node5041Labels := rfl
  simpa [nodeValue5041, Sparse.eval] using hc.symm

theorem sound5042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5042 node5042Labels = Sparse.eval nodeValue5042 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5042) = mixedMoment B node5042 node5042Labels := rfl
  simpa [nodeValue5042, Sparse.eval] using hc.symm

theorem sound5043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5043 node5043Labels = Sparse.eval nodeValue5043 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5043) = mixedMoment B node5043 node5043Labels := rfl
  simpa [nodeValue5043, Sparse.eval] using hc.symm

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

theorem sound5065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5065 node5065Labels = Sparse.eval nodeValue5065 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5065) = mixedMoment B node5065 node5065Labels := rfl
  simpa [nodeValue5065, Sparse.eval] using hc.symm

theorem sound5067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5067 node5067Labels = Sparse.eval nodeValue5067 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5067) = mixedMoment B node5067 node5067Labels := rfl
  simpa [nodeValue5067, Sparse.eval] using hc.symm

theorem sound5074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5074 node5074Labels = Sparse.eval nodeValue5074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5074) = mixedMoment B node5074 node5074Labels := rfl
  simpa [nodeValue5074, Sparse.eval] using hc.symm

theorem sound5085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5085 node5085Labels = Sparse.eval nodeValue5085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5085) = mixedMoment B node5085 node5085Labels := rfl
  simpa [nodeValue5085, Sparse.eval] using hc.symm

theorem sound5086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5086 node5086Labels = Sparse.eval nodeValue5086 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5086) = mixedMoment B node5086 node5086Labels := rfl
  simpa [nodeValue5086, Sparse.eval] using hc.symm

theorem sound5087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5087 node5087Labels = Sparse.eval nodeValue5087 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5087) = mixedMoment B node5087 node5087Labels := rfl
  simpa [nodeValue5087, Sparse.eval] using hc.symm

theorem sound5090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5090 node5090Labels = Sparse.eval nodeValue5090 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5090) = mixedMoment B node5090 node5090Labels := rfl
  simpa [nodeValue5090, Sparse.eval] using hc.symm

theorem sound5097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5097 node5097Labels = Sparse.eval nodeValue5097 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5097) = mixedMoment B node5097 node5097Labels := rfl
  simpa [nodeValue5097, Sparse.eval] using hc.symm

theorem sound5103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5103 node5103Labels = Sparse.eval nodeValue5103 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5103) = mixedMoment B node5103 node5103Labels := rfl
  simpa [nodeValue5103, Sparse.eval] using hc.symm

theorem sound5112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5112 node5112Labels = Sparse.eval nodeValue5112 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5112) = mixedMoment B node5112 node5112Labels := rfl
  simpa [nodeValue5112, Sparse.eval] using hc.symm

theorem sound5116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5116 node5116Labels = Sparse.eval nodeValue5116 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5116) = mixedMoment B node5116 node5116Labels := rfl
  simpa [nodeValue5116, Sparse.eval] using hc.symm

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

theorem sound5128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5128 node5128Labels = Sparse.eval nodeValue5128 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5128) = mixedMoment B node5128 node5128Labels := rfl
  simpa [nodeValue5128, Sparse.eval] using hc.symm

theorem sound5129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5129 node5129Labels = Sparse.eval nodeValue5129 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5129) = mixedMoment B node5129 node5129Labels := rfl
  simpa [nodeValue5129, Sparse.eval] using hc.symm

theorem sound5138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5138 node5138Labels = Sparse.eval nodeValue5138 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5138) = mixedMoment B node5138 node5138Labels := rfl
  simpa [nodeValue5138, Sparse.eval] using hc.symm

theorem sound5139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5139 node5139Labels = Sparse.eval nodeValue5139 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5139) = mixedMoment B node5139 node5139Labels := rfl
  simpa [nodeValue5139, Sparse.eval] using hc.symm

theorem sound5140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5140 node5140Labels = Sparse.eval nodeValue5140 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5140) = mixedMoment B node5140 node5140Labels := rfl
  simpa [nodeValue5140, Sparse.eval] using hc.symm

theorem sound5144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5144 node5144Labels = Sparse.eval nodeValue5144 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5144) = mixedMoment B node5144 node5144Labels := rfl
  simpa [nodeValue5144, Sparse.eval] using hc.symm

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

theorem sound5150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5150 node5150Labels = Sparse.eval nodeValue5150 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5150) = mixedMoment B node5150 node5150Labels := rfl
  simpa [nodeValue5150, Sparse.eval] using hc.symm

theorem sound5151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5151 node5151Labels = Sparse.eval nodeValue5151 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5151) = mixedMoment B node5151 node5151Labels := rfl
  simpa [nodeValue5151, Sparse.eval] using hc.symm

theorem sound5160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5160 node5160Labels = Sparse.eval nodeValue5160 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5160) = mixedMoment B node5160 node5160Labels := rfl
  simpa [nodeValue5160, Sparse.eval] using hc.symm

theorem sound5161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5161 node5161Labels = Sparse.eval nodeValue5161 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5161) = mixedMoment B node5161 node5161Labels := rfl
  simpa [nodeValue5161, Sparse.eval] using hc.symm

theorem sound5164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5164 node5164Labels = Sparse.eval nodeValue5164 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5164) = mixedMoment B node5164 node5164Labels := rfl
  simpa [nodeValue5164, Sparse.eval] using hc.symm

theorem sound5173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5173 node5173Labels = Sparse.eval nodeValue5173 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5173) = mixedMoment B node5173 node5173Labels := rfl
  simpa [nodeValue5173, Sparse.eval] using hc.symm

theorem sound5175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5175 node5175Labels = Sparse.eval nodeValue5175 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5175) = mixedMoment B node5175 node5175Labels := rfl
  simpa [nodeValue5175, Sparse.eval] using hc.symm

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

theorem sound5184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5184 node5184Labels = Sparse.eval nodeValue5184 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5184) = mixedMoment B node5184 node5184Labels := rfl
  simpa [nodeValue5184, Sparse.eval] using hc.symm

theorem sound5185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5185 node5185Labels = Sparse.eval nodeValue5185 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5185) = mixedMoment B node5185 node5185Labels := rfl
  simpa [nodeValue5185, Sparse.eval] using hc.symm

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

theorem sound5189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5189 node5189Labels = Sparse.eval nodeValue5189 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5189) = mixedMoment B node5189 node5189Labels := rfl
  simpa [nodeValue5189, Sparse.eval] using hc.symm

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

theorem sound5201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5201 node5201Labels = Sparse.eval nodeValue5201 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5201) = mixedMoment B node5201 node5201Labels := rfl
  simpa [nodeValue5201, Sparse.eval] using hc.symm

theorem sound5205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5205 node5205Labels = Sparse.eval nodeValue5205 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5205) = mixedMoment B node5205 node5205Labels := rfl
  simpa [nodeValue5205, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1679 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1679 x = (5611114966542188544000 : ℝ) * Sparse.eval nodeValue4705 x := by
  norm_num [reducedTerm1679, nodeValue4705, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1680 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1680 x = (-4157338039461347328000 : ℝ) * Sparse.eval nodeValue4756 x := by
  norm_num [reducedTerm1680, nodeValue4756, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1681 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1681 x = (-9921532838029295616000 : ℝ) * Sparse.eval nodeValue4757 x := by
  norm_num [reducedTerm1681, nodeValue4757, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1682 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1682 x = (-9955508355996844032000 : ℝ) * Sparse.eval nodeValue4761 x := by
  norm_num [reducedTerm1682, nodeValue4761, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1683 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1683 x = (-3552860462980792320000 : ℝ) * Sparse.eval nodeValue4762 x := by
  norm_num [reducedTerm1683, nodeValue4762, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1684 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1684 x = (1531209998492762112000 : ℝ) * Sparse.eval nodeValue4765 x := by
  norm_num [reducedTerm1684, nodeValue4765, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1685 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1685 x = (-10577125298707365888000 : ℝ) * Sparse.eval nodeValue4768 x := by
  norm_num [reducedTerm1685, nodeValue4768, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1686 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1686 x = (-2142501973049475072000 : ℝ) * Sparse.eval nodeValue4771 x := by
  norm_num [reducedTerm1686, nodeValue4771, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1687 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1687 x = (-7032198870020653056000 : ℝ) * Sparse.eval nodeValue4772 x := by
  norm_num [reducedTerm1687, nodeValue4772, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1688 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1688 x = (2026857879932239872000 : ℝ) * Sparse.eval nodeValue4773 x := by
  norm_num [reducedTerm1688, nodeValue4773, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1689 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1689 x = (-2118434941245063168000 : ℝ) * Sparse.eval nodeValue4774 x := by
  norm_num [reducedTerm1689, nodeValue4774, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1690 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1690 x = (12472080070696501248000 : ℝ) * Sparse.eval nodeValue4775 x := by
  norm_num [reducedTerm1690, nodeValue4775, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1691 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1691 x = (13670070453059715072000 : ℝ) * Sparse.eval nodeValue4776 x := by
  norm_num [reducedTerm1691, nodeValue4776, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1692 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1692 x = (1819985088072646656000 : ℝ) * Sparse.eval nodeValue4777 x := by
  norm_num [reducedTerm1692, nodeValue4777, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1693 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1693 x = (-3874325650567593984000 : ℝ) * Sparse.eval nodeValue4792 x := by
  norm_num [reducedTerm1693, nodeValue4792, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1694 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1694 x = (2175984329530540032000 : ℝ) * Sparse.eval nodeValue4793 x := by
  norm_num [reducedTerm1694, nodeValue4793, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1695 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1695 x = (-657568140574851072000 : ℝ) * Sparse.eval nodeValue4795 x := by
  norm_num [reducedTerm1695, nodeValue4795, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1696 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1696 x = (9126733393928650752000 : ℝ) * Sparse.eval nodeValue4803 x := by
  norm_num [reducedTerm1696, nodeValue4803, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1697 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1697 x = (6795525312677412864000 : ℝ) * Sparse.eval nodeValue4808 x := by
  norm_num [reducedTerm1697, nodeValue4808, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1698 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1698 x = (10203027601367236608000 : ℝ) * Sparse.eval nodeValue4815 x := by
  norm_num [reducedTerm1698, nodeValue4815, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1699 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1699 x = (16684169003853152256000 : ℝ) * Sparse.eval nodeValue4816 x := by
  norm_num [reducedTerm1699, nodeValue4816, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1700 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1700 x = (-4302249789556260864000 : ℝ) * Sparse.eval nodeValue4817 x := by
  norm_num [reducedTerm1700, nodeValue4817, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1701 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1701 x = (-9689775870270504960000 : ℝ) * Sparse.eval nodeValue4819 x := by
  norm_num [reducedTerm1701, nodeValue4819, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1702 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1702 x = (24425621100813090816000 : ℝ) * Sparse.eval nodeValue4821 x := by
  norm_num [reducedTerm1702, nodeValue4821, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1703 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1703 x = (4276208522593566720000 : ℝ) * Sparse.eval nodeValue4830 x := by
  norm_num [reducedTerm1703, nodeValue4830, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1704 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1704 x = (14865336275325419520000 : ℝ) * Sparse.eval nodeValue4836 x := by
  norm_num [reducedTerm1704, nodeValue4836, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1705 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1705 x = (-10611725918904778752000 : ℝ) * Sparse.eval nodeValue4844 x := by
  norm_num [reducedTerm1705, nodeValue4844, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1706 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1706 x = (-3651536391380140032000 : ℝ) * Sparse.eval nodeValue4851 x := by
  norm_num [reducedTerm1706, nodeValue4851, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1707 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1707 x = (25540881314177875968000 : ℝ) * Sparse.eval nodeValue4852 x := by
  norm_num [reducedTerm1707, nodeValue4852, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1708 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1708 x = (-8931969569439350784000 : ℝ) * Sparse.eval nodeValue4853 x := by
  norm_num [reducedTerm1708, nodeValue4853, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1709 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1709 x = (47721697208593809408000 : ℝ) * Sparse.eval nodeValue4856 x := by
  norm_num [reducedTerm1709, nodeValue4856, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1710 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1710 x = (3301651066537377792000 : ℝ) * Sparse.eval nodeValue4863 x := by
  norm_num [reducedTerm1710, nodeValue4863, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1711 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1711 x = (25180426029650411520000 : ℝ) * Sparse.eval nodeValue4867 x := by
  norm_num [reducedTerm1711, nodeValue4867, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1712 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1712 x = (-1313798019878486016000 : ℝ) * Sparse.eval nodeValue4872 x := by
  norm_num [reducedTerm1712, nodeValue4872, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1713 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1713 x = (21125648675937189888000 : ℝ) * Sparse.eval nodeValue4878 x := by
  norm_num [reducedTerm1713, nodeValue4878, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1714 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1714 x = (58246227271801110528000 : ℝ) * Sparse.eval nodeValue4879 x := by
  norm_num [reducedTerm1714, nodeValue4879, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1715 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1715 x = (15911341251193995264000 : ℝ) * Sparse.eval nodeValue4880 x := by
  norm_num [reducedTerm1715, nodeValue4880, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1716 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1716 x = (9824764650698833920000 : ℝ) * Sparse.eval nodeValue4881 x := by
  norm_num [reducedTerm1716, nodeValue4881, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1717 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1717 x = (19178062513867063296000 : ℝ) * Sparse.eval nodeValue4884 x := by
  norm_num [reducedTerm1717, nodeValue4884, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1718 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1718 x = (-1093534813718839296000 : ℝ) * Sparse.eval nodeValue4885 x := by
  norm_num [reducedTerm1718, nodeValue4885, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1719 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1719 x = (22163666956793413632000 : ℝ) * Sparse.eval nodeValue4886 x := by
  norm_num [reducedTerm1719, nodeValue4886, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1720 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1720 x = (-18745268956005924864000 : ℝ) * Sparse.eval nodeValue4887 x := by
  norm_num [reducedTerm1720, nodeValue4887, Integer.Sparse.eval, Sparse.eval] <;> ring

theorem reducedTermArithmetic1721 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1721 x = (-11533811195062517760000 : ℝ) * Sparse.eval nodeValue4888 x := by
  norm_num [reducedTerm1721, nodeValue4888, Integer.Sparse.eval, Sparse.eval] <;> ring

theorem reducedTermArithmetic1722 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1722 x = (16229027400171651072000 : ℝ) * Sparse.eval nodeValue4889 x := by
  norm_num [reducedTerm1722, nodeValue4889, Integer.Sparse.eval, Sparse.eval] <;> ring

theorem reducedTermArithmetic1723 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1723 x = (3028045911784685568000 : ℝ) * Sparse.eval nodeValue4890 x := by
  norm_num [reducedTerm1723, nodeValue4890, Integer.Sparse.eval, Sparse.eval] <;> ring

theorem reducedTermArithmetic1724 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1724 x = (39451307385118261248000 : ℝ) * Sparse.eval nodeValue4891 x := by
  norm_num [reducedTerm1724, nodeValue4891, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1725 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1725 x = (6273766636234997760000 : ℝ) * Sparse.eval nodeValue4892 x := by
  norm_num [reducedTerm1725, nodeValue4892, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1726 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1726 x = (31615295491978297344000 : ℝ) * Sparse.eval nodeValue4893 x := by
  norm_num [reducedTerm1726, nodeValue4893, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1727 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1727 x = (36270799555963650048000 : ℝ) * Sparse.eval nodeValue4894 x := by
  norm_num [reducedTerm1727, nodeValue4894, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1728 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1728 x = (100574139684149526528000 : ℝ) * Sparse.eval nodeValue4895 x := by
  norm_num [reducedTerm1728, nodeValue4895, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1729 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1729 x = (6889837408441860096000 : ℝ) * Sparse.eval nodeValue4896 x := by
  norm_num [reducedTerm1729, nodeValue4896, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1730 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1730 x = (30644085061601722368000 : ℝ) * Sparse.eval nodeValue4897 x := by
  norm_num [reducedTerm1730, nodeValue4897, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1731 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1731 x = (13107125496566513664000 : ℝ) * Sparse.eval nodeValue4898 x := by
  norm_num [reducedTerm1731, nodeValue4898, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1732 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1732 x = (-4861253499425390592000 : ℝ) * Sparse.eval nodeValue4899 x := by
  norm_num [reducedTerm1732, nodeValue4899, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic1733 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1733 x = (-1647434443064868864000 : ℝ) * Sparse.eval nodeValue4900 x := by
  norm_num [reducedTerm1733, nodeValue4900, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1734 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1734 x = (9891662941808492544000 : ℝ) * Sparse.eval nodeValue4901 x := by
  norm_num [reducedTerm1734, nodeValue4901, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1735 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1735 x = (-7941663994208845824000 : ℝ) * Sparse.eval nodeValue4930 x := by
  norm_num [reducedTerm1735, nodeValue4930, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1736 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1736 x = (2611987518440079360000 : ℝ) * Sparse.eval nodeValue4931 x := by
  norm_num [reducedTerm1736, nodeValue4931, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1737 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1737 x = (1421670070005792768000 : ℝ) * Sparse.eval nodeValue4933 x := by
  norm_num [reducedTerm1737, nodeValue4933, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1738 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1738 x = (-6239960297145630720000 : ℝ) * Sparse.eval nodeValue4934 x := by
  norm_num [reducedTerm1738, nodeValue4934, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1739 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1739 x = (3259996962101526528000 : ℝ) * Sparse.eval nodeValue4935 x := by
  norm_num [reducedTerm1739, nodeValue4935, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1740 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1740 x = (13377767853843283968000 : ℝ) * Sparse.eval nodeValue4942 x := by
  norm_num [reducedTerm1740, nodeValue4942, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1741 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1741 x = (-11958904477318643712000 : ℝ) * Sparse.eval nodeValue4944 x := by
  norm_num [reducedTerm1741, nodeValue4944, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1742 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1742 x = (-127393862378323968000 : ℝ) * Sparse.eval nodeValue4945 x := by
  norm_num [reducedTerm1742, nodeValue4945, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1743 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1743 x = (-1418863376524640256000 : ℝ) * Sparse.eval nodeValue4951 x := by
  norm_num [reducedTerm1743, nodeValue4951, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1744 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1744 x = (19134699747307683840000 : ℝ) * Sparse.eval nodeValue4954 x := by
  norm_num [reducedTerm1744, nodeValue4954, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1745 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1745 x = (-5686906574229995520000 : ℝ) * Sparse.eval nodeValue4955 x := by
  norm_num [reducedTerm1745, nodeValue4955, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1746 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1746 x = (-5324013064735948800000 : ℝ) * Sparse.eval nodeValue4956 x := by
  norm_num [reducedTerm1746, nodeValue4956, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1747 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1747 x = (29561192263900200960000 : ℝ) * Sparse.eval nodeValue4957 x := by
  norm_num [reducedTerm1747, nodeValue4957, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1748 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1748 x = (-1083441906686361600000 : ℝ) * Sparse.eval nodeValue4958 x := by
  norm_num [reducedTerm1748, nodeValue4958, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1749 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1749 x = (-12567225913008979968000 : ℝ) * Sparse.eval nodeValue4959 x := by
  norm_num [reducedTerm1749, nodeValue4959, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1750 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1750 x = (-4535331438044381184000 : ℝ) * Sparse.eval nodeValue4963 x := by
  norm_num [reducedTerm1750, nodeValue4963, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1751 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1751 x = (-23732159479676928000000 : ℝ) * Sparse.eval nodeValue4964 x := by
  norm_num [reducedTerm1751, nodeValue4964, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1752 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1752 x = (-18533635534082801664000 : ℝ) * Sparse.eval nodeValue4965 x := by
  norm_num [reducedTerm1752, nodeValue4965, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1753 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1753 x = (-22975789646216429568000 : ℝ) * Sparse.eval nodeValue4966 x := by
  norm_num [reducedTerm1753, nodeValue4966, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1754 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1754 x = (-8499226830254899200000 : ℝ) * Sparse.eval nodeValue4975 x := by
  norm_num [reducedTerm1754, nodeValue4975, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1755 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1755 x = (-16875309640898838528000 : ℝ) * Sparse.eval nodeValue4976 x := by
  norm_num [reducedTerm1755, nodeValue4976, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1756 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1756 x = (2978479197322739712000 : ℝ) * Sparse.eval nodeValue5034 x := by
  norm_num [reducedTerm1756, nodeValue5034, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1757 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1757 x = (16389072352617431040000 : ℝ) * Sparse.eval nodeValue5035 x := by
  norm_num [reducedTerm1757, nodeValue5035, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1758 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1758 x = (23233730127482585088000 : ℝ) * Sparse.eval nodeValue5040 x := by
  norm_num [reducedTerm1758, nodeValue5040, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1759 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1759 x = (92883104915521536000 : ℝ) * Sparse.eval nodeValue5041 x := by
  norm_num [reducedTerm1759, nodeValue5041, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1760 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1760 x = (-9483177650962563072000 : ℝ) * Sparse.eval nodeValue5042 x := by
  norm_num [reducedTerm1760, nodeValue5042, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1761 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1761 x = (-2890541624919588864000 : ℝ) * Sparse.eval nodeValue5043 x := by
  norm_num [reducedTerm1761, nodeValue5043, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1762 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1762 x = (-7341806534933348352000 : ℝ) * Sparse.eval nodeValue5044 x := by
  norm_num [reducedTerm1762, nodeValue5044, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1763 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1763 x = (-14530652001365262336000 : ℝ) * Sparse.eval nodeValue5065 x := by
  norm_num [reducedTerm1763, nodeValue5065, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1764 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1764 x = (7427653233623433216000 : ℝ) * Sparse.eval nodeValue5067 x := by
  norm_num [reducedTerm1764, nodeValue5067, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1765 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1765 x = (-12264455942580731904000 : ℝ) * Sparse.eval nodeValue5074 x := by
  norm_num [reducedTerm1765, nodeValue5074, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1766 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1766 x = (8916509350529335296000 : ℝ) * Sparse.eval nodeValue5085 x := by
  norm_num [reducedTerm1766, nodeValue5085, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1767 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1767 x = (12233494979845816320000 : ℝ) * Sparse.eval nodeValue5086 x := by
  norm_num [reducedTerm1767, nodeValue5086, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1768 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1768 x = (2026846219688607744000 : ℝ) * Sparse.eval nodeValue5087 x := by
  norm_num [reducedTerm1768, nodeValue5087, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1769 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1769 x = (-18907268073784344576000 : ℝ) * Sparse.eval nodeValue5090 x := by
  norm_num [reducedTerm1769, nodeValue5090, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1770 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1770 x = (1037405314429747200000 : ℝ) * Sparse.eval nodeValue5097 x := by
  norm_num [reducedTerm1770, nodeValue5097, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1771 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1771 x = (6797176070885867520000 : ℝ) * Sparse.eval nodeValue5103 x := by
  norm_num [reducedTerm1771, nodeValue5103, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1772 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1772 x = (-6581206302477778944000 : ℝ) * Sparse.eval nodeValue5112 x := by
  norm_num [reducedTerm1772, nodeValue5112, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1773 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1773 x = (1658951609427689472000 : ℝ) * Sparse.eval nodeValue5116 x := by
  norm_num [reducedTerm1773, nodeValue5116, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1774 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1774 x = (-2003708022304407552000 : ℝ) * Sparse.eval nodeValue5128 x := by
  norm_num [reducedTerm1774, nodeValue5128, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1775 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1775 x = (6585849716091125760000 : ℝ) * Sparse.eval nodeValue5129 x := by
  norm_num [reducedTerm1775, nodeValue5129, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1776 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1776 x = (12127532681381806080000 : ℝ) * Sparse.eval nodeValue5138 x := by
  norm_num [reducedTerm1776, nodeValue5138, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1777 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1777 x = (-49178321197557350400000 : ℝ) * Sparse.eval nodeValue5139 x := by
  norm_num [reducedTerm1777, nodeValue5139, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1778 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1778 x = (-17211622947812278272000 : ℝ) * Sparse.eval nodeValue5140 x := by
  norm_num [reducedTerm1778, nodeValue5140, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1779 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1779 x = (3601578321337909248000 : ℝ) * Sparse.eval nodeValue5144 x := by
  norm_num [reducedTerm1779, nodeValue5144, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1780 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1780 x = (11949080038817660928000 : ℝ) * Sparse.eval nodeValue5145 x := by
  norm_num [reducedTerm1780, nodeValue5145, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1781 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1781 x = (26234697751049797632000 : ℝ) * Sparse.eval nodeValue5147 x := by
  norm_num [reducedTerm1781, nodeValue5147, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1782 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1782 x = (-1803031804161294336000 : ℝ) * Sparse.eval nodeValue5150 x := by
  norm_num [reducedTerm1782, nodeValue5150, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1783 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1783 x = (-1219510267957739520000 : ℝ) * Sparse.eval nodeValue5151 x := by
  norm_num [reducedTerm1783, nodeValue5151, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1784 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1784 x = (34816216585195487232000 : ℝ) * Sparse.eval nodeValue5160 x := by
  norm_num [reducedTerm1784, nodeValue5160, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1785 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1785 x = (758866233230622720000 : ℝ) * Sparse.eval nodeValue5161 x := by
  norm_num [reducedTerm1785, nodeValue5161, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1786 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1786 x = (22613357947383447552000 : ℝ) * Sparse.eval nodeValue5164 x := by
  norm_num [reducedTerm1786, nodeValue5164, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1787 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1787 x = (13429246920497823744000 : ℝ) * Sparse.eval nodeValue5173 x := by
  norm_num [reducedTerm1787, nodeValue5173, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1788 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1788 x = (-4064171765800108032000 : ℝ) * Sparse.eval nodeValue5175 x := by
  norm_num [reducedTerm1788, nodeValue5175, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1789 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1789 x = (-4291086391493787648000 : ℝ) * Sparse.eval nodeValue5184 x := by
  norm_num [reducedTerm1789, nodeValue5184, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1790 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1790 x = (9726337145084313600000 : ℝ) * Sparse.eval nodeValue5185 x := by
  norm_num [reducedTerm1790, nodeValue5185, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1791 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1791 x = (30794924164413652992000 : ℝ) * Sparse.eval nodeValue5187 x := by
  norm_num [reducedTerm1791, nodeValue5187, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

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

theorem reducedTermArithmetic1792 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1792 x = (5010817572354392064000 : ℝ) * Sparse.eval nodeValue5188 x := by
  norm_num [reducedTerm1792, nodeValue5188, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1793 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1793 x = (-5752353613478363136000 : ℝ) * Sparse.eval nodeValue5189 x := by
  norm_num [reducedTerm1793, nodeValue5189, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1794 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1794 x = (7848902981735940096000 : ℝ) * Sparse.eval nodeValue5197 x := by
  norm_num [reducedTerm1794, nodeValue5197, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1795 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1795 x = (9732294813230825472000 : ℝ) * Sparse.eval nodeValue5198 x := by
  norm_num [reducedTerm1795, nodeValue5198, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1796 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1796 x = (55912898410749886464000 : ℝ) * Sparse.eval nodeValue5199 x := by
  norm_num [reducedTerm1796, nodeValue5199, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1797 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1797 x = (18198562535170375680000 : ℝ) * Sparse.eval nodeValue5201 x := by
  norm_num [reducedTerm1797, nodeValue5201, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1798 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1798 x = (16689362260860076032000 : ℝ) * Sparse.eval nodeValue5205 x := by
  norm_num [reducedTerm1798, nodeValue5205, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1676Check : reducedMerge1676 = Integer.Sparse.mergeBy masterLess reducedTerm1680 reducedTerm1681 := by decide +kernel

theorem reducedMerge1677Check : reducedMerge1677 = Integer.Sparse.mergeBy masterLess reducedTerm1679 reducedMerge1676 := by decide +kernel

theorem reducedMerge1678Check : reducedMerge1678 = Integer.Sparse.mergeBy masterLess reducedTerm1682 reducedTerm1683 := by decide +kernel

theorem reducedMerge1679Check : reducedMerge1679 = Integer.Sparse.mergeBy masterLess reducedTerm1684 reducedTerm1685 := by decide +kernel

theorem reducedMerge1680Check : reducedMerge1680 = Integer.Sparse.mergeBy masterLess reducedMerge1678 reducedMerge1679 := by decide +kernel

theorem reducedMerge1681Check : reducedMerge1681 = Integer.Sparse.mergeBy masterLess reducedMerge1677 reducedMerge1680 := by decide +kernel

theorem reducedMerge1682Check : reducedMerge1682 = Integer.Sparse.mergeBy masterLess reducedTerm1686 reducedTerm1687 := by decide +kernel

theorem reducedMerge1683Check : reducedMerge1683 = Integer.Sparse.mergeBy masterLess reducedTerm1688 reducedTerm1689 := by decide +kernel

theorem reducedMerge1684Check : reducedMerge1684 = Integer.Sparse.mergeBy masterLess reducedMerge1682 reducedMerge1683 := by decide +kernel

theorem reducedMerge1685Check : reducedMerge1685 = Integer.Sparse.mergeBy masterLess reducedTerm1690 reducedTerm1691 := by decide +kernel

theorem reducedMerge1686Check : reducedMerge1686 = Integer.Sparse.mergeBy masterLess reducedTerm1692 reducedTerm1693 := by decide +kernel

theorem reducedMerge1687Check : reducedMerge1687 = Integer.Sparse.mergeBy masterLess reducedMerge1685 reducedMerge1686 := by decide +kernel

theorem reducedMerge1688Check : reducedMerge1688 = Integer.Sparse.mergeBy masterLess reducedMerge1684 reducedMerge1687 := by decide +kernel

theorem reducedMerge1689Check : reducedMerge1689 = Integer.Sparse.mergeBy masterLess reducedMerge1681 reducedMerge1688 := by decide +kernel

theorem reducedMerge1690Check : reducedMerge1690 = Integer.Sparse.mergeBy masterLess reducedTerm1695 reducedTerm1696 := by decide +kernel

theorem reducedMerge1691Check : reducedMerge1691 = Integer.Sparse.mergeBy masterLess reducedTerm1694 reducedMerge1690 := by decide +kernel

theorem reducedMerge1692Check : reducedMerge1692 = Integer.Sparse.mergeBy masterLess reducedTerm1697 reducedTerm1698 := by decide +kernel

theorem reducedMerge1693Check : reducedMerge1693 = Integer.Sparse.mergeBy masterLess reducedTerm1699 reducedTerm1700 := by decide +kernel

theorem reducedMerge1694Check : reducedMerge1694 = Integer.Sparse.mergeBy masterLess reducedMerge1692 reducedMerge1693 := by decide +kernel

theorem reducedMerge1695Check : reducedMerge1695 = Integer.Sparse.mergeBy masterLess reducedMerge1691 reducedMerge1694 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1696Check : reducedMerge1696 = Integer.Sparse.mergeBy masterLess reducedTerm1701 reducedTerm1702 := by decide +kernel

theorem reducedMerge1697Check : reducedMerge1697 = Integer.Sparse.mergeBy masterLess reducedTerm1703 reducedTerm1704 := by decide +kernel

theorem reducedMerge1698Check : reducedMerge1698 = Integer.Sparse.mergeBy masterLess reducedMerge1696 reducedMerge1697 := by decide +kernel

theorem reducedMerge1699Check : reducedMerge1699 = Integer.Sparse.mergeBy masterLess reducedTerm1705 reducedTerm1706 := by decide +kernel

theorem reducedMerge1700Check : reducedMerge1700 = Integer.Sparse.mergeBy masterLess reducedTerm1707 reducedTerm1708 := by decide +kernel

theorem reducedMerge1701Check : reducedMerge1701 = Integer.Sparse.mergeBy masterLess reducedMerge1699 reducedMerge1700 := by decide +kernel

theorem reducedMerge1702Check : reducedMerge1702 = Integer.Sparse.mergeBy masterLess reducedMerge1698 reducedMerge1701 := by decide +kernel

theorem reducedMerge1703Check : reducedMerge1703 = Integer.Sparse.mergeBy masterLess reducedMerge1695 reducedMerge1702 := by decide +kernel

theorem reducedMerge1704Check : reducedMerge1704 = Integer.Sparse.mergeBy masterLess reducedMerge1689 reducedMerge1703 := by decide +kernel

theorem reducedMerge1705Check : reducedMerge1705 = Integer.Sparse.mergeBy masterLess reducedTerm1710 reducedTerm1711 := by decide +kernel

theorem reducedMerge1706Check : reducedMerge1706 = Integer.Sparse.mergeBy masterLess reducedTerm1709 reducedMerge1705 := by decide +kernel

theorem reducedMerge1707Check : reducedMerge1707 = Integer.Sparse.mergeBy masterLess reducedTerm1712 reducedTerm1713 := by decide +kernel

theorem reducedMerge1708Check : reducedMerge1708 = Integer.Sparse.mergeBy masterLess reducedTerm1714 reducedTerm1715 := by decide +kernel

theorem reducedMerge1709Check : reducedMerge1709 = Integer.Sparse.mergeBy masterLess reducedMerge1707 reducedMerge1708 := by decide +kernel

theorem reducedMerge1710Check : reducedMerge1710 = Integer.Sparse.mergeBy masterLess reducedMerge1706 reducedMerge1709 := by decide +kernel

theorem reducedMerge1711Check : reducedMerge1711 = Integer.Sparse.mergeBy masterLess reducedTerm1716 reducedTerm1717 := by decide +kernel

theorem reducedMerge1712Check : reducedMerge1712 = Integer.Sparse.mergeBy masterLess reducedTerm1718 reducedTerm1719 := by decide +kernel

theorem reducedMerge1713Check : reducedMerge1713 = Integer.Sparse.mergeBy masterLess reducedMerge1711 reducedMerge1712 := by decide +kernel

theorem reducedMerge1714Check : reducedMerge1714 = Integer.Sparse.mergeBy masterLess reducedTerm1720 reducedTerm1721 := by decide +kernel

theorem reducedMerge1715Check : reducedMerge1715 = Integer.Sparse.mergeBy masterLess reducedTerm1722 reducedTerm1723 := by decide +kernel

theorem reducedMerge1716Check : reducedMerge1716 = Integer.Sparse.mergeBy masterLess reducedMerge1714 reducedMerge1715 := by decide +kernel

theorem reducedMerge1717Check : reducedMerge1717 = Integer.Sparse.mergeBy masterLess reducedMerge1713 reducedMerge1716 := by decide +kernel

theorem reducedMerge1718Check : reducedMerge1718 = Integer.Sparse.mergeBy masterLess reducedMerge1710 reducedMerge1717 := by decide +kernel

theorem reducedMerge1719Check : reducedMerge1719 = Integer.Sparse.mergeBy masterLess reducedTerm1725 reducedTerm1726 := by decide +kernel

theorem reducedMerge1720Check : reducedMerge1720 = Integer.Sparse.mergeBy masterLess reducedTerm1724 reducedMerge1719 := by decide +kernel

theorem reducedMerge1721Check : reducedMerge1721 = Integer.Sparse.mergeBy masterLess reducedTerm1727 reducedTerm1728 := by decide +kernel

theorem reducedMerge1722Check : reducedMerge1722 = Integer.Sparse.mergeBy masterLess reducedTerm1729 reducedTerm1730 := by decide +kernel

theorem reducedMerge1723Check : reducedMerge1723 = Integer.Sparse.mergeBy masterLess reducedMerge1721 reducedMerge1722 := by decide +kernel

theorem reducedMerge1724Check : reducedMerge1724 = Integer.Sparse.mergeBy masterLess reducedMerge1720 reducedMerge1723 := by decide +kernel

theorem reducedMerge1725Check : reducedMerge1725 = Integer.Sparse.mergeBy masterLess reducedTerm1731 reducedTerm1732 := by decide +kernel

theorem reducedMerge1726Check : reducedMerge1726 = Integer.Sparse.mergeBy masterLess reducedTerm1733 reducedTerm1734 := by decide +kernel

theorem reducedMerge1727Check : reducedMerge1727 = Integer.Sparse.mergeBy masterLess reducedMerge1725 reducedMerge1726 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1728Check : reducedMerge1728 = Integer.Sparse.mergeBy masterLess reducedTerm1735 reducedTerm1736 := by decide +kernel

theorem reducedMerge1729Check : reducedMerge1729 = Integer.Sparse.mergeBy masterLess reducedTerm1737 reducedTerm1738 := by decide +kernel

theorem reducedMerge1730Check : reducedMerge1730 = Integer.Sparse.mergeBy masterLess reducedMerge1728 reducedMerge1729 := by decide +kernel

theorem reducedMerge1731Check : reducedMerge1731 = Integer.Sparse.mergeBy masterLess reducedMerge1727 reducedMerge1730 := by decide +kernel

theorem reducedMerge1732Check : reducedMerge1732 = Integer.Sparse.mergeBy masterLess reducedMerge1724 reducedMerge1731 := by decide +kernel

theorem reducedMerge1733Check : reducedMerge1733 = Integer.Sparse.mergeBy masterLess reducedMerge1718 reducedMerge1732 := by decide +kernel

theorem reducedMerge1734Check : reducedMerge1734 = Integer.Sparse.mergeBy masterLess reducedMerge1704 reducedMerge1733 := by decide +kernel

theorem reducedMerge1735Check : reducedMerge1735 = Integer.Sparse.mergeBy masterLess reducedTerm1740 reducedTerm1741 := by decide +kernel

theorem reducedMerge1736Check : reducedMerge1736 = Integer.Sparse.mergeBy masterLess reducedTerm1739 reducedMerge1735 := by decide +kernel

theorem reducedMerge1737Check : reducedMerge1737 = Integer.Sparse.mergeBy masterLess reducedTerm1742 reducedTerm1743 := by decide +kernel

theorem reducedMerge1738Check : reducedMerge1738 = Integer.Sparse.mergeBy masterLess reducedTerm1744 reducedTerm1745 := by decide +kernel

theorem reducedMerge1739Check : reducedMerge1739 = Integer.Sparse.mergeBy masterLess reducedMerge1737 reducedMerge1738 := by decide +kernel

theorem reducedMerge1740Check : reducedMerge1740 = Integer.Sparse.mergeBy masterLess reducedMerge1736 reducedMerge1739 := by decide +kernel

theorem reducedMerge1741Check : reducedMerge1741 = Integer.Sparse.mergeBy masterLess reducedTerm1746 reducedTerm1747 := by decide +kernel

theorem reducedMerge1742Check : reducedMerge1742 = Integer.Sparse.mergeBy masterLess reducedTerm1748 reducedTerm1749 := by decide +kernel

theorem reducedMerge1743Check : reducedMerge1743 = Integer.Sparse.mergeBy masterLess reducedMerge1741 reducedMerge1742 := by decide +kernel

theorem reducedMerge1744Check : reducedMerge1744 = Integer.Sparse.mergeBy masterLess reducedTerm1750 reducedTerm1751 := by decide +kernel

theorem reducedMerge1745Check : reducedMerge1745 = Integer.Sparse.mergeBy masterLess reducedTerm1752 reducedTerm1753 := by decide +kernel

theorem reducedMerge1746Check : reducedMerge1746 = Integer.Sparse.mergeBy masterLess reducedMerge1744 reducedMerge1745 := by decide +kernel

theorem reducedMerge1747Check : reducedMerge1747 = Integer.Sparse.mergeBy masterLess reducedMerge1743 reducedMerge1746 := by decide +kernel

theorem reducedMerge1748Check : reducedMerge1748 = Integer.Sparse.mergeBy masterLess reducedMerge1740 reducedMerge1747 := by decide +kernel

theorem reducedMerge1749Check : reducedMerge1749 = Integer.Sparse.mergeBy masterLess reducedTerm1755 reducedTerm1756 := by decide +kernel

theorem reducedMerge1750Check : reducedMerge1750 = Integer.Sparse.mergeBy masterLess reducedTerm1754 reducedMerge1749 := by decide +kernel

theorem reducedMerge1751Check : reducedMerge1751 = Integer.Sparse.mergeBy masterLess reducedTerm1757 reducedTerm1758 := by decide +kernel

theorem reducedMerge1752Check : reducedMerge1752 = Integer.Sparse.mergeBy masterLess reducedTerm1759 reducedTerm1760 := by decide +kernel

theorem reducedMerge1753Check : reducedMerge1753 = Integer.Sparse.mergeBy masterLess reducedMerge1751 reducedMerge1752 := by decide +kernel

theorem reducedMerge1754Check : reducedMerge1754 = Integer.Sparse.mergeBy masterLess reducedMerge1750 reducedMerge1753 := by decide +kernel

theorem reducedMerge1755Check : reducedMerge1755 = Integer.Sparse.mergeBy masterLess reducedTerm1761 reducedTerm1762 := by decide +kernel

theorem reducedMerge1756Check : reducedMerge1756 = Integer.Sparse.mergeBy masterLess reducedTerm1763 reducedTerm1764 := by decide +kernel

theorem reducedMerge1757Check : reducedMerge1757 = Integer.Sparse.mergeBy masterLess reducedMerge1755 reducedMerge1756 := by decide +kernel

theorem reducedMerge1758Check : reducedMerge1758 = Integer.Sparse.mergeBy masterLess reducedTerm1765 reducedTerm1766 := by decide +kernel

theorem reducedMerge1759Check : reducedMerge1759 = Integer.Sparse.mergeBy masterLess reducedTerm1767 reducedTerm1768 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1760Check : reducedMerge1760 = Integer.Sparse.mergeBy masterLess reducedMerge1758 reducedMerge1759 := by decide +kernel

theorem reducedMerge1761Check : reducedMerge1761 = Integer.Sparse.mergeBy masterLess reducedMerge1757 reducedMerge1760 := by decide +kernel

theorem reducedMerge1762Check : reducedMerge1762 = Integer.Sparse.mergeBy masterLess reducedMerge1754 reducedMerge1761 := by decide +kernel

theorem reducedMerge1763Check : reducedMerge1763 = Integer.Sparse.mergeBy masterLess reducedMerge1748 reducedMerge1762 := by decide +kernel

theorem reducedMerge1764Check : reducedMerge1764 = Integer.Sparse.mergeBy masterLess reducedTerm1770 reducedTerm1771 := by decide +kernel

theorem reducedMerge1765Check : reducedMerge1765 = Integer.Sparse.mergeBy masterLess reducedTerm1769 reducedMerge1764 := by decide +kernel

theorem reducedMerge1766Check : reducedMerge1766 = Integer.Sparse.mergeBy masterLess reducedTerm1772 reducedTerm1773 := by decide +kernel

theorem reducedMerge1767Check : reducedMerge1767 = Integer.Sparse.mergeBy masterLess reducedTerm1774 reducedTerm1775 := by decide +kernel

theorem reducedMerge1768Check : reducedMerge1768 = Integer.Sparse.mergeBy masterLess reducedMerge1766 reducedMerge1767 := by decide +kernel

theorem reducedMerge1769Check : reducedMerge1769 = Integer.Sparse.mergeBy masterLess reducedMerge1765 reducedMerge1768 := by decide +kernel

theorem reducedMerge1770Check : reducedMerge1770 = Integer.Sparse.mergeBy masterLess reducedTerm1776 reducedTerm1777 := by decide +kernel

theorem reducedMerge1771Check : reducedMerge1771 = Integer.Sparse.mergeBy masterLess reducedTerm1778 reducedTerm1779 := by decide +kernel

theorem reducedMerge1772Check : reducedMerge1772 = Integer.Sparse.mergeBy masterLess reducedMerge1770 reducedMerge1771 := by decide +kernel

theorem reducedMerge1773Check : reducedMerge1773 = Integer.Sparse.mergeBy masterLess reducedTerm1780 reducedTerm1781 := by decide +kernel

theorem reducedMerge1774Check : reducedMerge1774 = Integer.Sparse.mergeBy masterLess reducedTerm1782 reducedTerm1783 := by decide +kernel

theorem reducedMerge1775Check : reducedMerge1775 = Integer.Sparse.mergeBy masterLess reducedMerge1773 reducedMerge1774 := by decide +kernel

theorem reducedMerge1776Check : reducedMerge1776 = Integer.Sparse.mergeBy masterLess reducedMerge1772 reducedMerge1775 := by decide +kernel

theorem reducedMerge1777Check : reducedMerge1777 = Integer.Sparse.mergeBy masterLess reducedMerge1769 reducedMerge1776 := by decide +kernel

theorem reducedMerge1778Check : reducedMerge1778 = Integer.Sparse.mergeBy masterLess reducedTerm1785 reducedTerm1786 := by decide +kernel

theorem reducedMerge1779Check : reducedMerge1779 = Integer.Sparse.mergeBy masterLess reducedTerm1784 reducedMerge1778 := by decide +kernel

theorem reducedMerge1780Check : reducedMerge1780 = Integer.Sparse.mergeBy masterLess reducedTerm1787 reducedTerm1788 := by decide +kernel

theorem reducedMerge1781Check : reducedMerge1781 = Integer.Sparse.mergeBy masterLess reducedTerm1789 reducedTerm1790 := by decide +kernel

theorem reducedMerge1782Check : reducedMerge1782 = Integer.Sparse.mergeBy masterLess reducedMerge1780 reducedMerge1781 := by decide +kernel

theorem reducedMerge1783Check : reducedMerge1783 = Integer.Sparse.mergeBy masterLess reducedMerge1779 reducedMerge1782 := by decide +kernel

theorem reducedMerge1784Check : reducedMerge1784 = Integer.Sparse.mergeBy masterLess reducedTerm1791 reducedTerm1792 := by decide +kernel

theorem reducedMerge1785Check : reducedMerge1785 = Integer.Sparse.mergeBy masterLess reducedTerm1793 reducedTerm1794 := by decide +kernel

theorem reducedMerge1786Check : reducedMerge1786 = Integer.Sparse.mergeBy masterLess reducedMerge1784 reducedMerge1785 := by decide +kernel

theorem reducedMerge1787Check : reducedMerge1787 = Integer.Sparse.mergeBy masterLess reducedTerm1795 reducedTerm1796 := by decide +kernel

theorem reducedMerge1788Check : reducedMerge1788 = Integer.Sparse.mergeBy masterLess reducedTerm1797 reducedTerm1798 := by decide +kernel

theorem reducedMerge1789Check : reducedMerge1789 = Integer.Sparse.mergeBy masterLess reducedMerge1787 reducedMerge1788 := by decide +kernel

theorem reducedMerge1790Check : reducedMerge1790 = Integer.Sparse.mergeBy masterLess reducedMerge1786 reducedMerge1789 := by decide +kernel

theorem reducedMerge1791Check : reducedMerge1791 = Integer.Sparse.mergeBy masterLess reducedMerge1783 reducedMerge1790 := by decide +kernel

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

theorem reducedMerge1792Check : reducedMerge1792 = Integer.Sparse.mergeBy masterLess reducedMerge1777 reducedMerge1791 := by decide +kernel

theorem reducedMerge1793Check : reducedMerge1793 = Integer.Sparse.mergeBy masterLess reducedMerge1763 reducedMerge1792 := by decide +kernel

theorem reducedMerge1794Check : reducedMerge1794 = Integer.Sparse.mergeBy masterLess reducedMerge1734 reducedMerge1793 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1679 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1679 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1679 (originalVector B) := by
  rw [reducedTermArithmetic1679, ← sound4705 B hB hF]
  change (5611114966542188544000 : ℝ) * mixedMoment B node4705 node4705Labels =
    (37623398400 : ℝ) * ((149138972160 : ℝ) * mixedMoment B node4705 node4705Labels + 0)
  ring

theorem reducedTermEval1680 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1680 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1680 (originalVector B) := by
  rw [reducedTermArithmetic1680, ← sound4756 B hB hF]
  change (-4157338039461347328000 : ℝ) * mixedMoment B node4756 node4756Labels =
    (37623398400 : ℝ) * (((-110498737920 : ℤ) : ℝ) * mixedMoment B node4756 node4756Labels + 0)
  ring

theorem reducedTermEval1681 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1681 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1681 (originalVector B) := by
  rw [reducedTermArithmetic1681, ← sound4757 B hB hF]
  change (-9921532838029295616000 : ℝ) * mixedMoment B node4757 node4757Labels =
    (37623398400 : ℝ) * (((-263706450240 : ℤ) : ℝ) * mixedMoment B node4757 node4757Labels + 0)
  ring

theorem reducedTermEval1682 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1682 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1682 (originalVector B) := by
  rw [reducedTermArithmetic1682, ← sound4761 B hB hF]
  change (-9955508355996844032000 : ℝ) * mixedMoment B node4761 node4761Labels =
    (37623398400 : ℝ) * (((-264609492480 : ℤ) : ℝ) * mixedMoment B node4761 node4761Labels + 0)
  ring

theorem reducedTermEval1683 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1683 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1683 (originalVector B) := by
  rw [reducedTermArithmetic1683, ← sound4762 B hB hF]
  change (-3552860462980792320000 : ℝ) * mixedMoment B node4762 node4762Labels =
    (37623398400 : ℝ) * (((-94432204800 : ℤ) : ℝ) * mixedMoment B node4762 node4762Labels + 0)
  ring

theorem reducedTermEval1684 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1684 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1684 (originalVector B) := by
  rw [reducedTermArithmetic1684, ← sound4765 B hB hF]
  change (1531209998492762112000 : ℝ) * mixedMoment B node4765 node4765Labels =
    (37623398400 : ℝ) * ((40698343680 : ℝ) * mixedMoment B node4765 node4765Labels + 0)
  ring

theorem reducedTermEval1685 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1685 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1685 (originalVector B) := by
  rw [reducedTermArithmetic1685, ← sound4768 B hB hF]
  change (-10577125298707365888000 : ℝ) * mixedMoment B node4768 node4768Labels =
    (37623398400 : ℝ) * (((-281131576320 : ℤ) : ℝ) * mixedMoment B node4768 node4768Labels + 0)
  ring

theorem reducedTermEval1686 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1686 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1686 (originalVector B) := by
  rw [reducedTermArithmetic1686, ← sound4771 B hB hF]
  change (-2142501973049475072000 : ℝ) * mixedMoment B node4771 node4771Labels =
    (37623398400 : ℝ) * (((-56945998080 : ℤ) : ℝ) * mixedMoment B node4771 node4771Labels + 0)
  ring

theorem reducedTermEval1687 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1687 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1687 (originalVector B) := by
  rw [reducedTermArithmetic1687, ← sound4772 B hB hF]
  change (-7032198870020653056000 : ℝ) * mixedMoment B node4772 node4772Labels =
    (37623398400 : ℝ) * (((-186910251840 : ℤ) : ℝ) * mixedMoment B node4772 node4772Labels + 0)
  ring

theorem reducedTermEval1688 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1688 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1688 (originalVector B) := by
  rw [reducedTermArithmetic1688, ← sound4773 B hB hF]
  change (2026857879932239872000 : ℝ) * mixedMoment B node4773 node4773Labels =
    (37623398400 : ℝ) * ((53872270080 : ℝ) * mixedMoment B node4773 node4773Labels + 0)
  ring

theorem reducedTermEval1689 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1689 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1689 (originalVector B) := by
  rw [reducedTermArithmetic1689, ← sound4774 B hB hF]
  change (-2118434941245063168000 : ℝ) * mixedMoment B node4774 node4774Labels =
    (37623398400 : ℝ) * (((-56306315520 : ℤ) : ℝ) * mixedMoment B node4774 node4774Labels + 0)
  ring

theorem reducedTermEval1690 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1690 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1690 (originalVector B) := by
  rw [reducedTermArithmetic1690, ← sound4775 B hB hF]
  change (12472080070696501248000 : ℝ) * mixedMoment B node4775 node4775Labels =
    (37623398400 : ℝ) * ((331497966720 : ℝ) * mixedMoment B node4775 node4775Labels + 0)
  ring

theorem reducedTermEval1691 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1691 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1691 (originalVector B) := by
  rw [reducedTermArithmetic1691, ← sound4776 B hB hF]
  change (13670070453059715072000 : ℝ) * mixedMoment B node4776 node4776Labels =
    (37623398400 : ℝ) * ((363339598080 : ℝ) * mixedMoment B node4776 node4776Labels + 0)
  ring

theorem reducedTermEval1692 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1692 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1692 (originalVector B) := by
  rw [reducedTermArithmetic1692, ← sound4777 B hB hF]
  change (1819985088072646656000 : ℝ) * mixedMoment B node4777 node4777Labels =
    (37623398400 : ℝ) * ((48373755840 : ℝ) * mixedMoment B node4777 node4777Labels + 0)
  ring

theorem reducedTermEval1693 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1693 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1693 (originalVector B) := by
  rw [reducedTermArithmetic1693, ← sound4792 B hB hF]
  change (-3874325650567593984000 : ℝ) * mixedMoment B node4792 node4792Labels =
    (37623398400 : ℝ) * (((-102976493760 : ℤ) : ℝ) * mixedMoment B node4792 node4792Labels + 0)
  ring

theorem reducedTermEval1694 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1694 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1694 (originalVector B) := by
  rw [reducedTermArithmetic1694, ← sound4793 B hB hF]
  change (2175984329530540032000 : ℝ) * mixedMoment B node4793 node4793Labels =
    (37623398400 : ℝ) * ((57835932480 : ℝ) * mixedMoment B node4793 node4793Labels + 0)
  ring

theorem reducedTermEval1695 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1695 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1695 (originalVector B) := by
  rw [reducedTermArithmetic1695, ← sound4795 B hB hF]
  change (-657568140574851072000 : ℝ) * mixedMoment B node4795 node4795Labels =
    (37623398400 : ℝ) * (((-17477638080 : ℤ) : ℝ) * mixedMoment B node4795 node4795Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1696 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1696 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1696 (originalVector B) := by
  rw [reducedTermArithmetic1696, ← sound4803 B hB hF]
  change (9126733393928650752000 : ℝ) * mixedMoment B node4803 node4803Labels =
    (37623398400 : ℝ) * ((242581313280 : ℝ) * mixedMoment B node4803 node4803Labels + 0)
  ring

theorem reducedTermEval1697 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1697 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1697 (originalVector B) := by
  rw [reducedTermArithmetic1697, ← sound4808 B hB hF]
  change (6795525312677412864000 : ℝ) * mixedMoment B node4808 node4808Labels =
    (37623398400 : ℝ) * ((180619656960 : ℝ) * mixedMoment B node4808 node4808Labels + 0)
  ring

theorem reducedTermEval1698 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1698 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1698 (originalVector B) := by
  rw [reducedTermArithmetic1698, ← sound4815 B hB hF]
  change (10203027601367236608000 : ℝ) * mixedMoment B node4815 node4815Labels =
    (37623398400 : ℝ) * ((271188357120 : ℝ) * mixedMoment B node4815 node4815Labels + 0)
  ring

theorem reducedTermEval1699 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1699 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1699 (originalVector B) := by
  rw [reducedTermArithmetic1699, ← sound4816 B hB hF]
  change (16684169003853152256000 : ℝ) * mixedMoment B node4816 node4816Labels =
    (37623398400 : ℝ) * ((443451939840 : ℝ) * mixedMoment B node4816 node4816Labels + 0)
  ring

theorem reducedTermEval1700 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1700 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1700 (originalVector B) := by
  rw [reducedTermArithmetic1700, ← sound4817 B hB hF]
  change (-4302249789556260864000 : ℝ) * mixedMoment B node4817 node4817Labels =
    (37623398400 : ℝ) * (((-114350376960 : ℤ) : ℝ) * mixedMoment B node4817 node4817Labels + 0)
  ring

theorem reducedTermEval1701 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1701 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1701 (originalVector B) := by
  rw [reducedTermArithmetic1701, ← sound4819 B hB hF]
  change (-9689775870270504960000 : ℝ) * mixedMoment B node4819 node4819Labels =
    (37623398400 : ℝ) * (((-257546534400 : ℤ) : ℝ) * mixedMoment B node4819 node4819Labels + 0)
  ring

theorem reducedTermEval1702 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1702 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1702 (originalVector B) := by
  rw [reducedTermArithmetic1702, ← sound4821 B hB hF]
  change (24425621100813090816000 : ℝ) * mixedMoment B node4821 node4821Labels =
    (37623398400 : ℝ) * ((649213578240 : ℝ) * mixedMoment B node4821 node4821Labels + 0)
  ring

theorem reducedTermEval1703 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1703 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1703 (originalVector B) := by
  rw [reducedTermArithmetic1703, ← sound4830 B hB hF]
  change (4276208522593566720000 : ℝ) * mixedMoment B node4830 node4830Labels =
    (37623398400 : ℝ) * ((113658220800 : ℝ) * mixedMoment B node4830 node4830Labels + 0)
  ring

theorem reducedTermEval1704 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1704 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1704 (originalVector B) := by
  rw [reducedTermArithmetic1704, ← sound4836 B hB hF]
  change (14865336275325419520000 : ℝ) * mixedMoment B node4836 node4836Labels =
    (37623398400 : ℝ) * ((395108812800 : ℝ) * mixedMoment B node4836 node4836Labels + 0)
  ring

theorem reducedTermEval1705 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1705 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1705 (originalVector B) := by
  rw [reducedTermArithmetic1705, ← sound4844 B hB hF]
  change (-10611725918904778752000 : ℝ) * mixedMoment B node4844 node4844Labels =
    (37623398400 : ℝ) * (((-282051233280 : ℤ) : ℝ) * mixedMoment B node4844 node4844Labels + 0)
  ring

theorem reducedTermEval1706 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1706 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1706 (originalVector B) := by
  rw [reducedTermArithmetic1706, ← sound4851 B hB hF]
  change (-3651536391380140032000 : ℝ) * mixedMoment B node4851 node4851Labels =
    (37623398400 : ℝ) * (((-97054932480 : ℤ) : ℝ) * mixedMoment B node4851 node4851Labels + 0)
  ring

theorem reducedTermEval1707 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1707 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1707 (originalVector B) := by
  rw [reducedTermArithmetic1707, ← sound4852 B hB hF]
  change (25540881314177875968000 : ℝ) * mixedMoment B node4852 node4852Labels =
    (37623398400 : ℝ) * ((678856307520 : ℝ) * mixedMoment B node4852 node4852Labels + 0)
  ring

theorem reducedTermEval1708 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1708 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1708 (originalVector B) := by
  rw [reducedTermArithmetic1708, ← sound4853 B hB hF]
  change (-8931969569439350784000 : ℝ) * mixedMoment B node4853 node4853Labels =
    (37623398400 : ℝ) * (((-237404645760 : ℤ) : ℝ) * mixedMoment B node4853 node4853Labels + 0)
  ring

theorem reducedTermEval1709 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1709 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1709 (originalVector B) := by
  rw [reducedTermArithmetic1709, ← sound4856 B hB hF]
  change (47721697208593809408000 : ℝ) * mixedMoment B node4856 node4856Labels =
    (37623398400 : ℝ) * ((1268404749120 : ℝ) * mixedMoment B node4856 node4856Labels + 0)
  ring

theorem reducedTermEval1710 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1710 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1710 (originalVector B) := by
  rw [reducedTermArithmetic1710, ← sound4863 B hB hF]
  change (3301651066537377792000 : ℝ) * mixedMoment B node4863 node4863Labels =
    (37623398400 : ℝ) * ((87755258880 : ℝ) * mixedMoment B node4863 node4863Labels + 0)
  ring

theorem reducedTermEval1711 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1711 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1711 (originalVector B) := by
  rw [reducedTermArithmetic1711, ← sound4867 B hB hF]
  change (25180426029650411520000 : ℝ) * mixedMoment B node4867 node4867Labels =
    (37623398400 : ℝ) * ((669275692800 : ℝ) * mixedMoment B node4867 node4867Labels + 0)
  ring

theorem reducedTermEval1712 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1712 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1712 (originalVector B) := by
  rw [reducedTermArithmetic1712, ← sound4872 B hB hF]
  change (-1313798019878486016000 : ℝ) * mixedMoment B node4872 node4872Labels =
    (37623398400 : ℝ) * (((-34919706240 : ℤ) : ℝ) * mixedMoment B node4872 node4872Labels + 0)
  ring

theorem reducedTermEval1713 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1713 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1713 (originalVector B) := by
  rw [reducedTermArithmetic1713, ← sound4878 B hB hF]
  change (21125648675937189888000 : ℝ) * mixedMoment B node4878 node4878Labels =
    (37623398400 : ℝ) * ((561502936320 : ℝ) * mixedMoment B node4878 node4878Labels + 0)
  ring

theorem reducedTermEval1714 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1714 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1714 (originalVector B) := by
  rw [reducedTermArithmetic1714, ← sound4879 B hB hF]
  change (58246227271801110528000 : ℝ) * mixedMoment B node4879 node4879Labels =
    (37623398400 : ℝ) * ((1548138385920 : ℝ) * mixedMoment B node4879 node4879Labels + 0)
  ring

theorem reducedTermEval1715 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1715 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1715 (originalVector B) := by
  rw [reducedTermArithmetic1715, ← sound4880 B hB hF]
  change (15911341251193995264000 : ℝ) * mixedMoment B node4880 node4880Labels =
    (37623398400 : ℝ) * ((422910792960 : ℝ) * mixedMoment B node4880 node4880Labels + 0)
  ring

theorem reducedTermEval1716 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1716 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1716 (originalVector B) := by
  rw [reducedTermArithmetic1716, ← sound4881 B hB hF]
  change (9824764650698833920000 : ℝ) * mixedMoment B node4881 node4881Labels =
    (37623398400 : ℝ) * ((261134428800 : ℝ) * mixedMoment B node4881 node4881Labels + 0)
  ring

theorem reducedTermEval1717 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1717 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1717 (originalVector B) := by
  rw [reducedTermArithmetic1717, ← sound4884 B hB hF]
  change (19178062513867063296000 : ℝ) * mixedMoment B node4884 node4884Labels =
    (37623398400 : ℝ) * ((509737645440 : ℝ) * mixedMoment B node4884 node4884Labels + 0)
  ring

theorem reducedTermEval1718 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1718 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1718 (originalVector B) := by
  rw [reducedTermArithmetic1718, ← sound4885 B hB hF]
  change (-1093534813718839296000 : ℝ) * mixedMoment B node4885 node4885Labels =
    (37623398400 : ℝ) * (((-29065285440 : ℤ) : ℝ) * mixedMoment B node4885 node4885Labels + 0)
  ring

theorem reducedTermEval1719 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1719 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1719 (originalVector B) := by
  rw [reducedTermArithmetic1719, ← sound4886 B hB hF]
  change (22163666956793413632000 : ℝ) * mixedMoment B node4886 node4886Labels =
    (37623398400 : ℝ) * ((589092636480 : ℝ) * mixedMoment B node4886 node4886Labels + 0)
  ring

theorem reducedTermEval1720 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1720 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1720 (originalVector B) := by
  rw [reducedTermArithmetic1720, ← sound4887 B hB hF]
  change (-18745268956005924864000 : ℝ) * mixedMoment B node4887 node4887Labels =
    (37623398400 : ℝ) * (((-498234336960 : ℤ) : ℝ) * mixedMoment B node4887 node4887Labels + 0)
  ring

theorem reducedTermEval1721 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1721 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1721 (originalVector B) := by
  rw [reducedTermArithmetic1721, ← sound4888 B hB hF]
  change (-11533811195062517760000 : ℝ) * mixedMoment B node4888 node4888Labels =
    (37623398400 : ℝ) * (((-306559526400 : ℤ) : ℝ) * mixedMoment B node4888 node4888Labels + 0)
  ring

theorem reducedTermEval1722 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1722 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1722 (originalVector B) := by
  rw [reducedTermArithmetic1722, ← sound4889 B hB hF]
  change (16229027400171651072000 : ℝ) * mixedMoment B node4889 node4889Labels =
    (37623398400 : ℝ) * ((431354638080 : ℝ) * mixedMoment B node4889 node4889Labels + 0)
  ring

theorem reducedTermEval1723 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1723 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1723 (originalVector B) := by
  rw [reducedTermArithmetic1723, ← sound4890 B hB hF]
  change (3028045911784685568000 : ℝ) * mixedMoment B node4890 node4890Labels =
    (37623398400 : ℝ) * ((80483051520 : ℝ) * mixedMoment B node4890 node4890Labels + 0)
  ring

theorem reducedTermEval1724 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1724 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1724 (originalVector B) := by
  rw [reducedTermArithmetic1724, ← sound4891 B hB hF]
  change (39451307385118261248000 : ℝ) * mixedMoment B node4891 node4891Labels =
    (37623398400 : ℝ) * ((1048584366720 : ℝ) * mixedMoment B node4891 node4891Labels + 0)
  ring

theorem reducedTermEval1725 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1725 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1725 (originalVector B) := by
  rw [reducedTermArithmetic1725, ← sound4892 B hB hF]
  change (6273766636234997760000 : ℝ) * mixedMoment B node4892 node4892Labels =
    (37623398400 : ℝ) * ((166751726400 : ℝ) * mixedMoment B node4892 node4892Labels + 0)
  ring

theorem reducedTermEval1726 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1726 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1726 (originalVector B) := by
  rw [reducedTermArithmetic1726, ← sound4893 B hB hF]
  change (31615295491978297344000 : ℝ) * mixedMoment B node4893 node4893Labels =
    (37623398400 : ℝ) * ((840309404160 : ℝ) * mixedMoment B node4893 node4893Labels + 0)
  ring

theorem reducedTermEval1727 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1727 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1727 (originalVector B) := by
  rw [reducedTermArithmetic1727, ← sound4894 B hB hF]
  change (36270799555963650048000 : ℝ) * mixedMoment B node4894 node4894Labels =
    (37623398400 : ℝ) * ((964048998720 : ℝ) * mixedMoment B node4894 node4894Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1676 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1676 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1676 (originalVector B) := by
  rw [reducedMerge1676Check, Integer.Sparse.eval_mergeBy, reducedTermEval1680 B hB hF, reducedTermEval1681 B hB hF]
  rw [originalMerge1676, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1677 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1677 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1677 (originalVector B) := by
  rw [reducedMerge1677Check, Integer.Sparse.eval_mergeBy, reducedTermEval1679 B hB hF, reducedMergeEval1676 B hB hF]
  rw [originalMerge1677, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1678 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1678 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1678 (originalVector B) := by
  rw [reducedMerge1678Check, Integer.Sparse.eval_mergeBy, reducedTermEval1682 B hB hF, reducedTermEval1683 B hB hF]
  rw [originalMerge1678, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1679 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1679 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1679 (originalVector B) := by
  rw [reducedMerge1679Check, Integer.Sparse.eval_mergeBy, reducedTermEval1684 B hB hF, reducedTermEval1685 B hB hF]
  rw [originalMerge1679, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1680 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1680 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1680 (originalVector B) := by
  rw [reducedMerge1680Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1678 B hB hF, reducedMergeEval1679 B hB hF]
  rw [originalMerge1680, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1681 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1681 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1681 (originalVector B) := by
  rw [reducedMerge1681Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1677 B hB hF, reducedMergeEval1680 B hB hF]
  rw [originalMerge1681, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1682 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1682 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1682 (originalVector B) := by
  rw [reducedMerge1682Check, Integer.Sparse.eval_mergeBy, reducedTermEval1686 B hB hF, reducedTermEval1687 B hB hF]
  rw [originalMerge1682, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1683 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1683 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1683 (originalVector B) := by
  rw [reducedMerge1683Check, Integer.Sparse.eval_mergeBy, reducedTermEval1688 B hB hF, reducedTermEval1689 B hB hF]
  rw [originalMerge1683, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1684 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1684 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1684 (originalVector B) := by
  rw [reducedMerge1684Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1682 B hB hF, reducedMergeEval1683 B hB hF]
  rw [originalMerge1684, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1685 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1685 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1685 (originalVector B) := by
  rw [reducedMerge1685Check, Integer.Sparse.eval_mergeBy, reducedTermEval1690 B hB hF, reducedTermEval1691 B hB hF]
  rw [originalMerge1685, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1686 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1686 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1686 (originalVector B) := by
  rw [reducedMerge1686Check, Integer.Sparse.eval_mergeBy, reducedTermEval1692 B hB hF, reducedTermEval1693 B hB hF]
  rw [originalMerge1686, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1687 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1687 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1687 (originalVector B) := by
  rw [reducedMerge1687Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1685 B hB hF, reducedMergeEval1686 B hB hF]
  rw [originalMerge1687, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1688 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1688 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1688 (originalVector B) := by
  rw [reducedMerge1688Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1684 B hB hF, reducedMergeEval1687 B hB hF]
  rw [originalMerge1688, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1689 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1689 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1689 (originalVector B) := by
  rw [reducedMerge1689Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1681 B hB hF, reducedMergeEval1688 B hB hF]
  rw [originalMerge1689, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1690 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1690 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1690 (originalVector B) := by
  rw [reducedMerge1690Check, Integer.Sparse.eval_mergeBy, reducedTermEval1695 B hB hF, reducedTermEval1696 B hB hF]
  rw [originalMerge1690, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1691 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1691 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1691 (originalVector B) := by
  rw [reducedMerge1691Check, Integer.Sparse.eval_mergeBy, reducedTermEval1694 B hB hF, reducedMergeEval1690 B hB hF]
  rw [originalMerge1691, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1692 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1692 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1692 (originalVector B) := by
  rw [reducedMerge1692Check, Integer.Sparse.eval_mergeBy, reducedTermEval1697 B hB hF, reducedTermEval1698 B hB hF]
  rw [originalMerge1692, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1693 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1693 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1693 (originalVector B) := by
  rw [reducedMerge1693Check, Integer.Sparse.eval_mergeBy, reducedTermEval1699 B hB hF, reducedTermEval1700 B hB hF]
  rw [originalMerge1693, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1694 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1694 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1694 (originalVector B) := by
  rw [reducedMerge1694Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1692 B hB hF, reducedMergeEval1693 B hB hF]
  rw [originalMerge1694, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1695 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1695 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1695 (originalVector B) := by
  rw [reducedMerge1695Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1691 B hB hF, reducedMergeEval1694 B hB hF]
  rw [originalMerge1695, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1728 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1728 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1728 (originalVector B) := by
  rw [reducedTermArithmetic1728, ← sound4895 B hB hF]
  change (100574139684149526528000 : ℝ) * mixedMoment B node4895 node4895Labels =
    (37623398400 : ℝ) * ((2673180625920 : ℝ) * mixedMoment B node4895 node4895Labels + 0)
  ring

theorem reducedTermEval1729 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1729 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1729 (originalVector B) := by
  rw [reducedTermArithmetic1729, ← sound4896 B hB hF]
  change (6889837408441860096000 : ℝ) * mixedMoment B node4896 node4896Labels =
    (37623398400 : ℝ) * ((183126397440 : ℝ) * mixedMoment B node4896 node4896Labels + 0)
  ring

theorem reducedTermEval1730 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1730 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1730 (originalVector B) := by
  rw [reducedTermArithmetic1730, ← sound4897 B hB hF]
  change (30644085061601722368000 : ℝ) * mixedMoment B node4897 node4897Labels =
    (37623398400 : ℝ) * ((814495403520 : ℝ) * mixedMoment B node4897 node4897Labels + 0)
  ring

theorem reducedTermEval1731 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1731 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1731 (originalVector B) := by
  rw [reducedTermArithmetic1731, ← sound4898 B hB hF]
  change (13107125496566513664000 : ℝ) * mixedMoment B node4898 node4898Labels =
    (37623398400 : ℝ) * ((348376968960 : ℝ) * mixedMoment B node4898 node4898Labels + 0)
  ring

theorem reducedTermEval1732 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1732 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1732 (originalVector B) := by
  rw [reducedTermArithmetic1732, ← sound4899 B hB hF]
  change (-4861253499425390592000 : ℝ) * mixedMoment B node4899 node4899Labels =
    (37623398400 : ℝ) * (((-129208250880 : ℤ) : ℝ) * mixedMoment B node4899 node4899Labels + 0)
  ring

theorem reducedTermEval1733 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1733 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1733 (originalVector B) := by
  rw [reducedTermArithmetic1733, ← sound4900 B hB hF]
  change (-1647434443064868864000 : ℝ) * mixedMoment B node4900 node4900Labels =
    (37623398400 : ℝ) * (((-43787496960 : ℤ) : ℝ) * mixedMoment B node4900 node4900Labels + 0)
  ring

theorem reducedTermEval1734 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1734 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1734 (originalVector B) := by
  rw [reducedTermArithmetic1734, ← sound4901 B hB hF]
  change (9891662941808492544000 : ℝ) * mixedMoment B node4901 node4901Labels =
    (37623398400 : ℝ) * ((262912532160 : ℝ) * mixedMoment B node4901 node4901Labels + 0)
  ring

theorem reducedTermEval1735 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1735 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1735 (originalVector B) := by
  rw [reducedTermArithmetic1735, ← sound4930 B hB hF]
  change (-7941663994208845824000 : ℝ) * mixedMoment B node4930 node4930Labels =
    (37623398400 : ℝ) * (((-211083111360 : ℤ) : ℝ) * mixedMoment B node4930 node4930Labels + 0)
  ring

theorem reducedTermEval1736 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1736 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1736 (originalVector B) := by
  rw [reducedTermArithmetic1736, ← sound4931 B hB hF]
  change (2611987518440079360000 : ℝ) * mixedMoment B node4931 node4931Labels =
    (37623398400 : ℝ) * ((69424550400 : ℝ) * mixedMoment B node4931 node4931Labels + 0)
  ring

theorem reducedTermEval1737 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1737 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1737 (originalVector B) := by
  rw [reducedTermArithmetic1737, ← sound4933 B hB hF]
  change (1421670070005792768000 : ℝ) * mixedMoment B node4933 node4933Labels =
    (37623398400 : ℝ) * ((37786859520 : ℝ) * mixedMoment B node4933 node4933Labels + 0)
  ring

theorem reducedTermEval1738 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1738 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1738 (originalVector B) := by
  rw [reducedTermArithmetic1738, ← sound4934 B hB hF]
  change (-6239960297145630720000 : ℝ) * mixedMoment B node4934 node4934Labels =
    (37623398400 : ℝ) * (((-165853180800 : ℤ) : ℝ) * mixedMoment B node4934 node4934Labels + 0)
  ring

theorem reducedTermEval1739 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1739 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1739 (originalVector B) := by
  rw [reducedTermArithmetic1739, ← sound4935 B hB hF]
  change (3259996962101526528000 : ℝ) * mixedMoment B node4935 node4935Labels =
    (37623398400 : ℝ) * ((86648125920 : ℝ) * mixedMoment B node4935 node4935Labels + 0)
  ring

theorem reducedTermEval1740 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1740 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1740 (originalVector B) := by
  rw [reducedTermArithmetic1740, ← sound4942 B hB hF]
  change (13377767853843283968000 : ℝ) * mixedMoment B node4942 node4942Labels =
    (37623398400 : ℝ) * ((355570427520 : ℝ) * mixedMoment B node4942 node4942Labels + 0)
  ring

theorem reducedTermEval1741 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1741 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1741 (originalVector B) := by
  rw [reducedTermArithmetic1741, ← sound4944 B hB hF]
  change (-11958904477318643712000 : ℝ) * mixedMoment B node4944 node4944Labels =
    (37623398400 : ℝ) * (((-317858167680 : ℤ) : ℝ) * mixedMoment B node4944 node4944Labels + 0)
  ring

theorem reducedTermEval1742 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1742 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1742 (originalVector B) := by
  rw [reducedTermArithmetic1742, ← sound4945 B hB hF]
  change (-127393862378323968000 : ℝ) * mixedMoment B node4945 node4945Labels =
    (37623398400 : ℝ) * (((-3386027520 : ℤ) : ℝ) * mixedMoment B node4945 node4945Labels + 0)
  ring

theorem reducedTermEval1743 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1743 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1743 (originalVector B) := by
  rw [reducedTermArithmetic1743, ← sound4951 B hB hF]
  change (-1418863376524640256000 : ℝ) * mixedMoment B node4951 node4951Labels =
    (37623398400 : ℝ) * (((-37712259840 : ℤ) : ℝ) * mixedMoment B node4951 node4951Labels + 0)
  ring

theorem reducedTermEval1744 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1744 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1744 (originalVector B) := by
  rw [reducedTermArithmetic1744, ← sound4954 B hB hF]
  change (19134699747307683840000 : ℝ) * mixedMoment B node4954 node4954Labels =
    (37623398400 : ℝ) * ((508585097600 : ℝ) * mixedMoment B node4954 node4954Labels + 0)
  ring

theorem reducedTermEval1745 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1745 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1745 (originalVector B) := by
  rw [reducedTermArithmetic1745, ← sound4955 B hB hF]
  change (-5686906574229995520000 : ℝ) * mixedMoment B node4955 node4955Labels =
    (37623398400 : ℝ) * (((-151153452800 : ℤ) : ℝ) * mixedMoment B node4955 node4955Labels + 0)
  ring

theorem reducedTermEval1746 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1746 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1746 (originalVector B) := by
  rw [reducedTermArithmetic1746, ← sound4956 B hB hF]
  change (-5324013064735948800000 : ℝ) * mixedMoment B node4956 node4956Labels =
    (37623398400 : ℝ) * (((-141508032000 : ℤ) : ℝ) * mixedMoment B node4956 node4956Labels + 0)
  ring

theorem reducedTermEval1747 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1747 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1747 (originalVector B) := by
  rw [reducedTermArithmetic1747, ← sound4957 B hB hF]
  change (29561192263900200960000 : ℝ) * mixedMoment B node4957 node4957Labels =
    (37623398400 : ℝ) * ((785712974400 : ℝ) * mixedMoment B node4957 node4957Labels + 0)
  ring

theorem reducedTermEval1748 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1748 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1748 (originalVector B) := by
  rw [reducedTermArithmetic1748, ← sound4958 B hB hF]
  change (-1083441906686361600000 : ℝ) * mixedMoment B node4958 node4958Labels =
    (37623398400 : ℝ) * (((-28797024000 : ℤ) : ℝ) * mixedMoment B node4958 node4958Labels + 0)
  ring

theorem reducedTermEval1749 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1749 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1749 (originalVector B) := by
  rw [reducedTermArithmetic1749, ← sound4959 B hB hF]
  change (-12567225913008979968000 : ℝ) * mixedMoment B node4959 node4959Labels =
    (37623398400 : ℝ) * (((-334026867520 : ℤ) : ℝ) * mixedMoment B node4959 node4959Labels + 0)
  ring

theorem reducedTermEval1750 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1750 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1750 (originalVector B) := by
  rw [reducedTermArithmetic1750, ← sound4963 B hB hF]
  change (-4535331438044381184000 : ℝ) * mixedMoment B node4963 node4963Labels =
    (37623398400 : ℝ) * (((-120545501760 : ℤ) : ℝ) * mixedMoment B node4963 node4963Labels + 0)
  ring

theorem reducedTermEval1751 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1751 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1751 (originalVector B) := by
  rw [reducedTermArithmetic1751, ← sound4964 B hB hF]
  change (-23732159479676928000000 : ℝ) * mixedMoment B node4964 node4964Labels =
    (37623398400 : ℝ) * (((-630781920000 : ℤ) : ℝ) * mixedMoment B node4964 node4964Labels + 0)
  ring

theorem reducedTermEval1752 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1752 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1752 (originalVector B) := by
  rw [reducedTermArithmetic1752, ← sound4965 B hB hF]
  change (-18533635534082801664000 : ℝ) * mixedMoment B node4965 node4965Labels =
    (37623398400 : ℝ) * (((-492609288960 : ℤ) : ℝ) * mixedMoment B node4965 node4965Labels + 0)
  ring

theorem reducedTermEval1753 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1753 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1753 (originalVector B) := by
  rw [reducedTermArithmetic1753, ← sound4966 B hB hF]
  change (-22975789646216429568000 : ℝ) * mixedMoment B node4966 node4966Labels =
    (37623398400 : ℝ) * (((-610678211520 : ℤ) : ℝ) * mixedMoment B node4966 node4966Labels + 0)
  ring

theorem reducedTermEval1754 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1754 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1754 (originalVector B) := by
  rw [reducedTermArithmetic1754, ← sound4975 B hB hF]
  change (-8499226830254899200000 : ℝ) * mixedMoment B node4975 node4975Labels =
    (37623398400 : ℝ) * (((-225902688000 : ℤ) : ℝ) * mixedMoment B node4975 node4975Labels + 0)
  ring

theorem reducedTermEval1755 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1755 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1755 (originalVector B) := by
  rw [reducedTermArithmetic1755, ← sound4976 B hB hF]
  change (-16875309640898838528000 : ℝ) * mixedMoment B node4976 node4976Labels =
    (37623398400 : ℝ) * (((-448532305920 : ℤ) : ℝ) * mixedMoment B node4976 node4976Labels + 0)
  ring

theorem reducedTermEval1756 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1756 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1756 (originalVector B) := by
  rw [reducedTermArithmetic1756, ← sound5034 B hB hF]
  change (2978479197322739712000 : ℝ) * mixedMoment B node5034 node5034Labels =
    (37623398400 : ℝ) * ((79165607680 : ℝ) * mixedMoment B node5034 node5034Labels + 0)
  ring

theorem reducedTermEval1757 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1757 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1757 (originalVector B) := by
  rw [reducedTermArithmetic1757, ← sound5035 B hB hF]
  change (16389072352617431040000 : ℝ) * mixedMoment B node5035 node5035Labels =
    (37623398400 : ℝ) * ((435608505600 : ℝ) * mixedMoment B node5035 node5035Labels + 0)
  ring

theorem reducedTermEval1758 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1758 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1758 (originalVector B) := by
  rw [reducedTermArithmetic1758, ← sound5040 B hB hF]
  change (23233730127482585088000 : ℝ) * mixedMoment B node5040 node5040Labels =
    (37623398400 : ℝ) * ((617534064320 : ℝ) * mixedMoment B node5040 node5040Labels + 0)
  ring

theorem reducedTermEval1759 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1759 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1759 (originalVector B) := by
  rw [reducedTermArithmetic1759, ← sound5041 B hB hF]
  change (92883104915521536000 : ℝ) * mixedMoment B node5041 node5041Labels =
    (37623398400 : ℝ) * ((2468759040 : ℝ) * mixedMoment B node5041 node5041Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1696 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1696 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1696 (originalVector B) := by
  rw [reducedMerge1696Check, Integer.Sparse.eval_mergeBy, reducedTermEval1701 B hB hF, reducedTermEval1702 B hB hF]
  rw [originalMerge1696, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1697 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1697 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1697 (originalVector B) := by
  rw [reducedMerge1697Check, Integer.Sparse.eval_mergeBy, reducedTermEval1703 B hB hF, reducedTermEval1704 B hB hF]
  rw [originalMerge1697, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1698 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1698 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1698 (originalVector B) := by
  rw [reducedMerge1698Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1696 B hB hF, reducedMergeEval1697 B hB hF]
  rw [originalMerge1698, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1699 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1699 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1699 (originalVector B) := by
  rw [reducedMerge1699Check, Integer.Sparse.eval_mergeBy, reducedTermEval1705 B hB hF, reducedTermEval1706 B hB hF]
  rw [originalMerge1699, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1700 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1700 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1700 (originalVector B) := by
  rw [reducedMerge1700Check, Integer.Sparse.eval_mergeBy, reducedTermEval1707 B hB hF, reducedTermEval1708 B hB hF]
  rw [originalMerge1700, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1701 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1701 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1701 (originalVector B) := by
  rw [reducedMerge1701Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1699 B hB hF, reducedMergeEval1700 B hB hF]
  rw [originalMerge1701, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1702 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1702 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1702 (originalVector B) := by
  rw [reducedMerge1702Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1698 B hB hF, reducedMergeEval1701 B hB hF]
  rw [originalMerge1702, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1703 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1703 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1703 (originalVector B) := by
  rw [reducedMerge1703Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1695 B hB hF, reducedMergeEval1702 B hB hF]
  rw [originalMerge1703, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1704 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1704 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1704 (originalVector B) := by
  rw [reducedMerge1704Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1689 B hB hF, reducedMergeEval1703 B hB hF]
  rw [originalMerge1704, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1705 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1705 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1705 (originalVector B) := by
  rw [reducedMerge1705Check, Integer.Sparse.eval_mergeBy, reducedTermEval1710 B hB hF, reducedTermEval1711 B hB hF]
  rw [originalMerge1705, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1706 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1706 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1706 (originalVector B) := by
  rw [reducedMerge1706Check, Integer.Sparse.eval_mergeBy, reducedTermEval1709 B hB hF, reducedMergeEval1705 B hB hF]
  rw [originalMerge1706, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1707 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1707 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1707 (originalVector B) := by
  rw [reducedMerge1707Check, Integer.Sparse.eval_mergeBy, reducedTermEval1712 B hB hF, reducedTermEval1713 B hB hF]
  rw [originalMerge1707, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1708 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1708 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1708 (originalVector B) := by
  rw [reducedMerge1708Check, Integer.Sparse.eval_mergeBy, reducedTermEval1714 B hB hF, reducedTermEval1715 B hB hF]
  rw [originalMerge1708, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1709 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1709 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1709 (originalVector B) := by
  rw [reducedMerge1709Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1707 B hB hF, reducedMergeEval1708 B hB hF]
  rw [originalMerge1709, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1710 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1710 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1710 (originalVector B) := by
  rw [reducedMerge1710Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1706 B hB hF, reducedMergeEval1709 B hB hF]
  rw [originalMerge1710, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1711 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1711 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1711 (originalVector B) := by
  rw [reducedMerge1711Check, Integer.Sparse.eval_mergeBy, reducedTermEval1716 B hB hF, reducedTermEval1717 B hB hF]
  rw [originalMerge1711, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1712 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1712 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1712 (originalVector B) := by
  rw [reducedMerge1712Check, Integer.Sparse.eval_mergeBy, reducedTermEval1718 B hB hF, reducedTermEval1719 B hB hF]
  rw [originalMerge1712, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1713 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1713 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1713 (originalVector B) := by
  rw [reducedMerge1713Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1711 B hB hF, reducedMergeEval1712 B hB hF]
  rw [originalMerge1713, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1714 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1714 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1714 (originalVector B) := by
  rw [reducedMerge1714Check, Integer.Sparse.eval_mergeBy, reducedTermEval1720 B hB hF, reducedTermEval1721 B hB hF]
  rw [originalMerge1714, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1715 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1715 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1715 (originalVector B) := by
  rw [reducedMerge1715Check, Integer.Sparse.eval_mergeBy, reducedTermEval1722 B hB hF, reducedTermEval1723 B hB hF]
  rw [originalMerge1715, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1716 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1716 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1716 (originalVector B) := by
  rw [reducedMerge1716Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1714 B hB hF, reducedMergeEval1715 B hB hF]
  rw [originalMerge1716, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1717 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1717 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1717 (originalVector B) := by
  rw [reducedMerge1717Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1713 B hB hF, reducedMergeEval1716 B hB hF]
  rw [originalMerge1717, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1718 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1718 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1718 (originalVector B) := by
  rw [reducedMerge1718Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1710 B hB hF, reducedMergeEval1717 B hB hF]
  rw [originalMerge1718, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1719 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1719 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1719 (originalVector B) := by
  rw [reducedMerge1719Check, Integer.Sparse.eval_mergeBy, reducedTermEval1725 B hB hF, reducedTermEval1726 B hB hF]
  rw [originalMerge1719, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1720 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1720 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1720 (originalVector B) := by
  rw [reducedMerge1720Check, Integer.Sparse.eval_mergeBy, reducedTermEval1724 B hB hF, reducedMergeEval1719 B hB hF]
  rw [originalMerge1720, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1721 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1721 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1721 (originalVector B) := by
  rw [reducedMerge1721Check, Integer.Sparse.eval_mergeBy, reducedTermEval1727 B hB hF, reducedTermEval1728 B hB hF]
  rw [originalMerge1721, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1722 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1722 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1722 (originalVector B) := by
  rw [reducedMerge1722Check, Integer.Sparse.eval_mergeBy, reducedTermEval1729 B hB hF, reducedTermEval1730 B hB hF]
  rw [originalMerge1722, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1723 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1723 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1723 (originalVector B) := by
  rw [reducedMerge1723Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1721 B hB hF, reducedMergeEval1722 B hB hF]
  rw [originalMerge1723, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1724 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1724 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1724 (originalVector B) := by
  rw [reducedMerge1724Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1720 B hB hF, reducedMergeEval1723 B hB hF]
  rw [originalMerge1724, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1725 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1725 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1725 (originalVector B) := by
  rw [reducedMerge1725Check, Integer.Sparse.eval_mergeBy, reducedTermEval1731 B hB hF, reducedTermEval1732 B hB hF]
  rw [originalMerge1725, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1726 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1726 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1726 (originalVector B) := by
  rw [reducedMerge1726Check, Integer.Sparse.eval_mergeBy, reducedTermEval1733 B hB hF, reducedTermEval1734 B hB hF]
  rw [originalMerge1726, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1727 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1727 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1727 (originalVector B) := by
  rw [reducedMerge1727Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1725 B hB hF, reducedMergeEval1726 B hB hF]
  rw [originalMerge1727, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1760 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1760 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1760 (originalVector B) := by
  rw [reducedTermArithmetic1760, ← sound5042 B hB hF]
  change (-9483177650962563072000 : ℝ) * mixedMoment B node5042 node5042Labels =
    (37623398400 : ℝ) * (((-252055318080 : ℤ) : ℝ) * mixedMoment B node5042 node5042Labels + 0)
  ring

theorem reducedTermEval1761 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1761 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1761 (originalVector B) := by
  rw [reducedTermArithmetic1761, ← sound5043 B hB hF]
  change (-2890541624919588864000 : ℝ) * mixedMoment B node5043 node5043Labels =
    (37623398400 : ℝ) * (((-76828296960 : ℤ) : ℝ) * mixedMoment B node5043 node5043Labels + 0)
  ring

theorem reducedTermEval1762 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1762 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1762 (originalVector B) := by
  rw [reducedTermArithmetic1762, ← sound5044 B hB hF]
  change (-7341806534933348352000 : ℝ) * mixedMoment B node5044 node5044Labels =
    (37623398400 : ℝ) * (((-195139377280 : ℤ) : ℝ) * mixedMoment B node5044 node5044Labels + 0)
  ring

theorem reducedTermEval1763 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1763 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1763 (originalVector B) := by
  rw [reducedTermArithmetic1763, ← sound5065 B hB hF]
  change (-14530652001365262336000 : ℝ) * mixedMoment B node5065 node5065Labels =
    (37623398400 : ℝ) * (((-386213171040 : ℤ) : ℝ) * mixedMoment B node5065 node5065Labels + 0)
  ring

theorem reducedTermEval1764 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1764 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1764 (originalVector B) := by
  rw [reducedTermArithmetic1764, ← sound5067 B hB hF]
  change (7427653233623433216000 : ℝ) * mixedMoment B node5067 node5067Labels =
    (37623398400 : ℝ) * ((197421114240 : ℝ) * mixedMoment B node5067 node5067Labels + 0)
  ring

theorem reducedTermEval1765 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1765 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1765 (originalVector B) := by
  rw [reducedTermArithmetic1765, ← sound5074 B hB hF]
  change (-12264455942580731904000 : ℝ) * mixedMoment B node5074 node5074Labels =
    (37623398400 : ℝ) * (((-325979482560 : ℤ) : ℝ) * mixedMoment B node5074 node5074Labels + 0)
  ring

theorem reducedTermEval1766 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1766 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1766 (originalVector B) := by
  rw [reducedTermArithmetic1766, ← sound5085 B hB hF]
  change (8916509350529335296000 : ℝ) * mixedMoment B node5085 node5085Labels =
    (37623398400 : ℝ) * ((236993725440 : ℝ) * mixedMoment B node5085 node5085Labels + 0)
  ring

theorem reducedTermEval1767 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1767 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1767 (originalVector B) := by
  rw [reducedTermArithmetic1767, ← sound5086 B hB hF]
  change (12233494979845816320000 : ℝ) * mixedMoment B node5086 node5086Labels =
    (37623398400 : ℝ) * ((325156564800 : ℝ) * mixedMoment B node5086 node5086Labels + 0)
  ring

theorem reducedTermEval1768 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1768 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1768 (originalVector B) := by
  rw [reducedTermArithmetic1768, ← sound5087 B hB hF]
  change (2026846219688607744000 : ℝ) * mixedMoment B node5087 node5087Labels =
    (37623398400 : ℝ) * ((53871960160 : ℝ) * mixedMoment B node5087 node5087Labels + 0)
  ring

theorem reducedTermEval1769 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1769 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1769 (originalVector B) := by
  rw [reducedTermArithmetic1769, ← sound5090 B hB hF]
  change (-18907268073784344576000 : ℝ) * mixedMoment B node5090 node5090Labels =
    (37623398400 : ℝ) * (((-502540144640 : ℤ) : ℝ) * mixedMoment B node5090 node5090Labels + 0)
  ring

theorem reducedTermEval1770 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1770 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1770 (originalVector B) := by
  rw [reducedTermArithmetic1770, ← sound5097 B hB hF]
  change (1037405314429747200000 : ℝ) * mixedMoment B node5097 node5097Labels =
    (37623398400 : ℝ) * ((27573408000 : ℝ) * mixedMoment B node5097 node5097Labels + 0)
  ring

theorem reducedTermEval1771 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1771 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1771 (originalVector B) := by
  rw [reducedTermArithmetic1771, ← sound5103 B hB hF]
  change (6797176070885867520000 : ℝ) * mixedMoment B node5103 node5103Labels =
    (37623398400 : ℝ) * ((180663532800 : ℝ) * mixedMoment B node5103 node5103Labels + 0)
  ring

theorem reducedTermEval1772 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1772 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1772 (originalVector B) := by
  rw [reducedTermArithmetic1772, ← sound5112 B hB hF]
  change (-6581206302477778944000 : ℝ) * mixedMoment B node5112 node5112Labels =
    (37623398400 : ℝ) * (((-174923228160 : ℤ) : ℝ) * mixedMoment B node5112 node5112Labels + 0)
  ring

theorem reducedTermEval1773 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1773 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1773 (originalVector B) := by
  rw [reducedTermArithmetic1773, ← sound5116 B hB hF]
  change (1658951609427689472000 : ℝ) * mixedMoment B node5116 node5116Labels =
    (37623398400 : ℝ) * ((44093614080 : ℝ) * mixedMoment B node5116 node5116Labels + 0)
  ring

theorem reducedTermEval1774 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1774 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1774 (originalVector B) := by
  rw [reducedTermArithmetic1774, ← sound5128 B hB hF]
  change (-2003708022304407552000 : ℝ) * mixedMoment B node5128 node5128Labels =
    (37623398400 : ℝ) * (((-53256965280 : ℤ) : ℝ) * mixedMoment B node5128 node5128Labels + 0)
  ring

theorem reducedTermEval1775 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1775 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1775 (originalVector B) := by
  rw [reducedTermArithmetic1775, ← sound5129 B hB hF]
  change (6585849716091125760000 : ℝ) * mixedMoment B node5129 node5129Labels =
    (37623398400 : ℝ) * ((175046646400 : ℝ) * mixedMoment B node5129 node5129Labels + 0)
  ring

theorem reducedTermEval1776 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1776 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1776 (originalVector B) := by
  rw [reducedTermArithmetic1776, ← sound5138 B hB hF]
  change (12127532681381806080000 : ℝ) * mixedMoment B node5138 node5138Labels =
    (37623398400 : ℝ) * ((322340171200 : ℝ) * mixedMoment B node5138 node5138Labels + 0)
  ring

theorem reducedTermEval1777 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1777 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1777 (originalVector B) := by
  rw [reducedTermArithmetic1777, ← sound5139 B hB hF]
  change (-49178321197557350400000 : ℝ) * mixedMoment B node5139 node5139Labels =
    (37623398400 : ℝ) * (((-1307120656000 : ℤ) : ℝ) * mixedMoment B node5139 node5139Labels + 0)
  ring

theorem reducedTermEval1778 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1778 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1778 (originalVector B) := by
  rw [reducedTermArithmetic1778, ← sound5140 B hB hF]
  change (-17211622947812278272000 : ℝ) * mixedMoment B node5140 node5140Labels =
    (37623398400 : ℝ) * (((-457471246080 : ℤ) : ℝ) * mixedMoment B node5140 node5140Labels + 0)
  ring

theorem reducedTermEval1779 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1779 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1779 (originalVector B) := by
  rw [reducedTermArithmetic1779, ← sound5144 B hB hF]
  change (3601578321337909248000 : ℝ) * mixedMoment B node5144 node5144Labels =
    (37623398400 : ℝ) * ((95727086720 : ℝ) * mixedMoment B node5144 node5144Labels + 0)
  ring

theorem reducedTermEval1780 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1780 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1780 (originalVector B) := by
  rw [reducedTermArithmetic1780, ← sound5145 B hB hF]
  change (11949080038817660928000 : ℝ) * mixedMoment B node5145 node5145Labels =
    (37623398400 : ℝ) * ((317597041920 : ℝ) * mixedMoment B node5145 node5145Labels + 0)
  ring

theorem reducedTermEval1781 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1781 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1781 (originalVector B) := by
  rw [reducedTermArithmetic1781, ← sound5147 B hB hF]
  change (26234697751049797632000 : ℝ) * mixedMoment B node5147 node5147Labels =
    (37623398400 : ℝ) * ((697297396480 : ℝ) * mixedMoment B node5147 node5147Labels + 0)
  ring

theorem reducedTermEval1782 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1782 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1782 (originalVector B) := by
  rw [reducedTermArithmetic1782, ← sound5150 B hB hF]
  change (-1803031804161294336000 : ℝ) * mixedMoment B node5150 node5150Labels =
    (37623398400 : ℝ) * (((-47923151040 : ℤ) : ℝ) * mixedMoment B node5150 node5150Labels + 0)
  ring

theorem reducedTermEval1783 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1783 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1783 (originalVector B) := by
  rw [reducedTermArithmetic1783, ← sound5151 B hB hF]
  change (-1219510267957739520000 : ℝ) * mixedMoment B node5151 node5151Labels =
    (37623398400 : ℝ) * (((-32413612800 : ℤ) : ℝ) * mixedMoment B node5151 node5151Labels + 0)
  ring

theorem reducedTermEval1784 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1784 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1784 (originalVector B) := by
  rw [reducedTermArithmetic1784, ← sound5160 B hB hF]
  change (34816216585195487232000 : ℝ) * mixedMoment B node5160 node5160Labels =
    (37623398400 : ℝ) * ((925387340480 : ℝ) * mixedMoment B node5160 node5160Labels + 0)
  ring

theorem reducedTermEval1785 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1785 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1785 (originalVector B) := by
  rw [reducedTermArithmetic1785, ← sound5161 B hB hF]
  change (758866233230622720000 : ℝ) * mixedMoment B node5161 node5161Labels =
    (37623398400 : ℝ) * ((20170060800 : ℝ) * mixedMoment B node5161 node5161Labels + 0)
  ring

theorem reducedTermEval1786 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1786 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1786 (originalVector B) := by
  rw [reducedTermArithmetic1786, ← sound5164 B hB hF]
  change (22613357947383447552000 : ℝ) * mixedMoment B node5164 node5164Labels =
    (37623398400 : ℝ) * ((601045065280 : ℝ) * mixedMoment B node5164 node5164Labels + 0)
  ring

theorem reducedTermEval1787 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1787 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1787 (originalVector B) := by
  rw [reducedTermArithmetic1787, ← sound5173 B hB hF]
  change (13429246920497823744000 : ℝ) * mixedMoment B node5173 node5173Labels =
    (37623398400 : ℝ) * ((356938700160 : ℝ) * mixedMoment B node5173 node5173Labels + 0)
  ring

theorem reducedTermEval1788 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1788 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1788 (originalVector B) := by
  rw [reducedTermArithmetic1788, ← sound5175 B hB hF]
  change (-4064171765800108032000 : ℝ) * mixedMoment B node5175 node5175Labels =
    (37623398400 : ℝ) * (((-108022452480 : ℤ) : ℝ) * mixedMoment B node5175 node5175Labels + 0)
  ring

theorem reducedTermEval1789 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1789 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1789 (originalVector B) := by
  rw [reducedTermArithmetic1789, ← sound5184 B hB hF]
  change (-4291086391493787648000 : ℝ) * mixedMoment B node5184 node5184Labels =
    (37623398400 : ℝ) * (((-114053662720 : ℤ) : ℝ) * mixedMoment B node5184 node5184Labels + 0)
  ring

theorem reducedTermEval1790 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1790 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1790 (originalVector B) := by
  rw [reducedTermArithmetic1790, ← sound5185 B hB hF]
  change (9726337145084313600000 : ℝ) * mixedMoment B node5185 node5185Labels =
    (37623398400 : ℝ) * ((258518304000 : ℝ) * mixedMoment B node5185 node5185Labels + 0)
  ring

theorem reducedTermEval1791 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1791 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1791 (originalVector B) := by
  rw [reducedTermArithmetic1791, ← sound5187 B hB hF]
  change (30794924164413652992000 : ℝ) * mixedMoment B node5187 node5187Labels =
    (37623398400 : ℝ) * ((818504586880 : ℝ) * mixedMoment B node5187 node5187Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1728 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1728 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1728 (originalVector B) := by
  rw [reducedMerge1728Check, Integer.Sparse.eval_mergeBy, reducedTermEval1735 B hB hF, reducedTermEval1736 B hB hF]
  rw [originalMerge1728, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1729 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1729 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1729 (originalVector B) := by
  rw [reducedMerge1729Check, Integer.Sparse.eval_mergeBy, reducedTermEval1737 B hB hF, reducedTermEval1738 B hB hF]
  rw [originalMerge1729, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1730 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1730 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1730 (originalVector B) := by
  rw [reducedMerge1730Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1728 B hB hF, reducedMergeEval1729 B hB hF]
  rw [originalMerge1730, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1731 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1731 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1731 (originalVector B) := by
  rw [reducedMerge1731Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1727 B hB hF, reducedMergeEval1730 B hB hF]
  rw [originalMerge1731, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1732 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1732 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1732 (originalVector B) := by
  rw [reducedMerge1732Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1724 B hB hF, reducedMergeEval1731 B hB hF]
  rw [originalMerge1732, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1733 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1733 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1733 (originalVector B) := by
  rw [reducedMerge1733Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1718 B hB hF, reducedMergeEval1732 B hB hF]
  rw [originalMerge1733, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1734 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1734 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1734 (originalVector B) := by
  rw [reducedMerge1734Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1704 B hB hF, reducedMergeEval1733 B hB hF]
  rw [originalMerge1734, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1735 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1735 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1735 (originalVector B) := by
  rw [reducedMerge1735Check, Integer.Sparse.eval_mergeBy, reducedTermEval1740 B hB hF, reducedTermEval1741 B hB hF]
  rw [originalMerge1735, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1736 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1736 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1736 (originalVector B) := by
  rw [reducedMerge1736Check, Integer.Sparse.eval_mergeBy, reducedTermEval1739 B hB hF, reducedMergeEval1735 B hB hF]
  rw [originalMerge1736, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1737 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1737 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1737 (originalVector B) := by
  rw [reducedMerge1737Check, Integer.Sparse.eval_mergeBy, reducedTermEval1742 B hB hF, reducedTermEval1743 B hB hF]
  rw [originalMerge1737, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1738 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1738 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1738 (originalVector B) := by
  rw [reducedMerge1738Check, Integer.Sparse.eval_mergeBy, reducedTermEval1744 B hB hF, reducedTermEval1745 B hB hF]
  rw [originalMerge1738, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1739 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1739 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1739 (originalVector B) := by
  rw [reducedMerge1739Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1737 B hB hF, reducedMergeEval1738 B hB hF]
  rw [originalMerge1739, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1740 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1740 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1740 (originalVector B) := by
  rw [reducedMerge1740Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1736 B hB hF, reducedMergeEval1739 B hB hF]
  rw [originalMerge1740, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1741 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1741 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1741 (originalVector B) := by
  rw [reducedMerge1741Check, Integer.Sparse.eval_mergeBy, reducedTermEval1746 B hB hF, reducedTermEval1747 B hB hF]
  rw [originalMerge1741, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1742 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1742 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1742 (originalVector B) := by
  rw [reducedMerge1742Check, Integer.Sparse.eval_mergeBy, reducedTermEval1748 B hB hF, reducedTermEval1749 B hB hF]
  rw [originalMerge1742, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1743 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1743 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1743 (originalVector B) := by
  rw [reducedMerge1743Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1741 B hB hF, reducedMergeEval1742 B hB hF]
  rw [originalMerge1743, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1744 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1744 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1744 (originalVector B) := by
  rw [reducedMerge1744Check, Integer.Sparse.eval_mergeBy, reducedTermEval1750 B hB hF, reducedTermEval1751 B hB hF]
  rw [originalMerge1744, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1745 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1745 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1745 (originalVector B) := by
  rw [reducedMerge1745Check, Integer.Sparse.eval_mergeBy, reducedTermEval1752 B hB hF, reducedTermEval1753 B hB hF]
  rw [originalMerge1745, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1746 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1746 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1746 (originalVector B) := by
  rw [reducedMerge1746Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1744 B hB hF, reducedMergeEval1745 B hB hF]
  rw [originalMerge1746, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1747 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1747 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1747 (originalVector B) := by
  rw [reducedMerge1747Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1743 B hB hF, reducedMergeEval1746 B hB hF]
  rw [originalMerge1747, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1748 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1748 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1748 (originalVector B) := by
  rw [reducedMerge1748Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1740 B hB hF, reducedMergeEval1747 B hB hF]
  rw [originalMerge1748, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1749 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1749 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1749 (originalVector B) := by
  rw [reducedMerge1749Check, Integer.Sparse.eval_mergeBy, reducedTermEval1755 B hB hF, reducedTermEval1756 B hB hF]
  rw [originalMerge1749, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1750 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1750 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1750 (originalVector B) := by
  rw [reducedMerge1750Check, Integer.Sparse.eval_mergeBy, reducedTermEval1754 B hB hF, reducedMergeEval1749 B hB hF]
  rw [originalMerge1750, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1751 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1751 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1751 (originalVector B) := by
  rw [reducedMerge1751Check, Integer.Sparse.eval_mergeBy, reducedTermEval1757 B hB hF, reducedTermEval1758 B hB hF]
  rw [originalMerge1751, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1752 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1752 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1752 (originalVector B) := by
  rw [reducedMerge1752Check, Integer.Sparse.eval_mergeBy, reducedTermEval1759 B hB hF, reducedTermEval1760 B hB hF]
  rw [originalMerge1752, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1753 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1753 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1753 (originalVector B) := by
  rw [reducedMerge1753Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1751 B hB hF, reducedMergeEval1752 B hB hF]
  rw [originalMerge1753, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1754 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1754 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1754 (originalVector B) := by
  rw [reducedMerge1754Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1750 B hB hF, reducedMergeEval1753 B hB hF]
  rw [originalMerge1754, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1755 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1755 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1755 (originalVector B) := by
  rw [reducedMerge1755Check, Integer.Sparse.eval_mergeBy, reducedTermEval1761 B hB hF, reducedTermEval1762 B hB hF]
  rw [originalMerge1755, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1756 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1756 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1756 (originalVector B) := by
  rw [reducedMerge1756Check, Integer.Sparse.eval_mergeBy, reducedTermEval1763 B hB hF, reducedTermEval1764 B hB hF]
  rw [originalMerge1756, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1757 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1757 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1757 (originalVector B) := by
  rw [reducedMerge1757Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1755 B hB hF, reducedMergeEval1756 B hB hF]
  rw [originalMerge1757, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1758 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1758 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1758 (originalVector B) := by
  rw [reducedMerge1758Check, Integer.Sparse.eval_mergeBy, reducedTermEval1765 B hB hF, reducedTermEval1766 B hB hF]
  rw [originalMerge1758, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1759 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1759 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1759 (originalVector B) := by
  rw [reducedMerge1759Check, Integer.Sparse.eval_mergeBy, reducedTermEval1767 B hB hF, reducedTermEval1768 B hB hF]
  rw [originalMerge1759, Integer.Sparse.eval_append]
  ring

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

theorem reducedTermEval1792 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1792 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1792 (originalVector B) := by
  rw [reducedTermArithmetic1792, ← sound5188 B hB hF]
  change (5010817572354392064000 : ℝ) * mixedMoment B node5188 node5188Labels =
    (37623398400 : ℝ) * ((133183544960 : ℝ) * mixedMoment B node5188 node5188Labels + 0)
  ring

theorem reducedTermEval1793 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1793 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1793 (originalVector B) := by
  rw [reducedTermArithmetic1793, ← sound5189 B hB hF]
  change (-5752353613478363136000 : ℝ) * mixedMoment B node5189 node5189Labels =
    (37623398400 : ℝ) * (((-152892983040 : ℤ) : ℝ) * mixedMoment B node5189 node5189Labels + 0)
  ring

theorem reducedTermEval1794 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1794 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1794 (originalVector B) := by
  rw [reducedTermArithmetic1794, ← sound5197 B hB hF]
  change (7848902981735940096000 : ℝ) * mixedMoment B node5197 node5197Labels =
    (37623398400 : ℝ) * ((208617597440 : ℝ) * mixedMoment B node5197 node5197Labels + 0)
  ring

theorem reducedTermEval1795 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1795 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1795 (originalVector B) := by
  rw [reducedTermArithmetic1795, ← sound5198 B hB hF]
  change (9732294813230825472000 : ℝ) * mixedMoment B node5198 node5198Labels =
    (37623398400 : ℝ) * ((258676654080 : ℝ) * mixedMoment B node5198 node5198Labels + 0)
  ring

theorem reducedTermEval1796 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1796 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1796 (originalVector B) := by
  rw [reducedTermArithmetic1796, ← sound5199 B hB hF]
  change (55912898410749886464000 : ℝ) * mixedMoment B node5199 node5199Labels =
    (37623398400 : ℝ) * ((1486120360960 : ℝ) * mixedMoment B node5199 node5199Labels + 0)
  ring

theorem reducedTermEval1797 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1797 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1797 (originalVector B) := by
  rw [reducedTermArithmetic1797, ← sound5201 B hB hF]
  change (18198562535170375680000 : ℝ) * mixedMoment B node5201 node5201Labels =
    (37623398400 : ℝ) * ((483703315200 : ℝ) * mixedMoment B node5201 node5201Labels + 0)
  ring

theorem reducedTermEval1798 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1798 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1798 (originalVector B) := by
  rw [reducedTermArithmetic1798, ← sound5205 B hB hF]
  change (16689362260860076032000 : ℝ) * mixedMoment B node5205 node5205Labels =
    (37623398400 : ℝ) * ((443589972480 : ℝ) * mixedMoment B node5205 node5205Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1760 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1760 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1760 (originalVector B) := by
  rw [reducedMerge1760Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1758 B hB hF, reducedMergeEval1759 B hB hF]
  rw [originalMerge1760, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1761 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1761 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1761 (originalVector B) := by
  rw [reducedMerge1761Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1757 B hB hF, reducedMergeEval1760 B hB hF]
  rw [originalMerge1761, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1762 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1762 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1762 (originalVector B) := by
  rw [reducedMerge1762Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1754 B hB hF, reducedMergeEval1761 B hB hF]
  rw [originalMerge1762, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1763 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1763 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1763 (originalVector B) := by
  rw [reducedMerge1763Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1748 B hB hF, reducedMergeEval1762 B hB hF]
  rw [originalMerge1763, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1764 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1764 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1764 (originalVector B) := by
  rw [reducedMerge1764Check, Integer.Sparse.eval_mergeBy, reducedTermEval1770 B hB hF, reducedTermEval1771 B hB hF]
  rw [originalMerge1764, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1765 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1765 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1765 (originalVector B) := by
  rw [reducedMerge1765Check, Integer.Sparse.eval_mergeBy, reducedTermEval1769 B hB hF, reducedMergeEval1764 B hB hF]
  rw [originalMerge1765, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1766 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1766 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1766 (originalVector B) := by
  rw [reducedMerge1766Check, Integer.Sparse.eval_mergeBy, reducedTermEval1772 B hB hF, reducedTermEval1773 B hB hF]
  rw [originalMerge1766, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1767 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1767 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1767 (originalVector B) := by
  rw [reducedMerge1767Check, Integer.Sparse.eval_mergeBy, reducedTermEval1774 B hB hF, reducedTermEval1775 B hB hF]
  rw [originalMerge1767, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1768 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1768 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1768 (originalVector B) := by
  rw [reducedMerge1768Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1766 B hB hF, reducedMergeEval1767 B hB hF]
  rw [originalMerge1768, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1769 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1769 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1769 (originalVector B) := by
  rw [reducedMerge1769Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1765 B hB hF, reducedMergeEval1768 B hB hF]
  rw [originalMerge1769, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1770 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1770 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1770 (originalVector B) := by
  rw [reducedMerge1770Check, Integer.Sparse.eval_mergeBy, reducedTermEval1776 B hB hF, reducedTermEval1777 B hB hF]
  rw [originalMerge1770, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1771 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1771 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1771 (originalVector B) := by
  rw [reducedMerge1771Check, Integer.Sparse.eval_mergeBy, reducedTermEval1778 B hB hF, reducedTermEval1779 B hB hF]
  rw [originalMerge1771, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1772 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1772 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1772 (originalVector B) := by
  rw [reducedMerge1772Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1770 B hB hF, reducedMergeEval1771 B hB hF]
  rw [originalMerge1772, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1773 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1773 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1773 (originalVector B) := by
  rw [reducedMerge1773Check, Integer.Sparse.eval_mergeBy, reducedTermEval1780 B hB hF, reducedTermEval1781 B hB hF]
  rw [originalMerge1773, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1774 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1774 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1774 (originalVector B) := by
  rw [reducedMerge1774Check, Integer.Sparse.eval_mergeBy, reducedTermEval1782 B hB hF, reducedTermEval1783 B hB hF]
  rw [originalMerge1774, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1775 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1775 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1775 (originalVector B) := by
  rw [reducedMerge1775Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1773 B hB hF, reducedMergeEval1774 B hB hF]
  rw [originalMerge1775, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1776 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1776 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1776 (originalVector B) := by
  rw [reducedMerge1776Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1772 B hB hF, reducedMergeEval1775 B hB hF]
  rw [originalMerge1776, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1777 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1777 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1777 (originalVector B) := by
  rw [reducedMerge1777Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1769 B hB hF, reducedMergeEval1776 B hB hF]
  rw [originalMerge1777, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1778 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1778 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1778 (originalVector B) := by
  rw [reducedMerge1778Check, Integer.Sparse.eval_mergeBy, reducedTermEval1785 B hB hF, reducedTermEval1786 B hB hF]
  rw [originalMerge1778, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1779 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1779 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1779 (originalVector B) := by
  rw [reducedMerge1779Check, Integer.Sparse.eval_mergeBy, reducedTermEval1784 B hB hF, reducedMergeEval1778 B hB hF]
  rw [originalMerge1779, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1780 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1780 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1780 (originalVector B) := by
  rw [reducedMerge1780Check, Integer.Sparse.eval_mergeBy, reducedTermEval1787 B hB hF, reducedTermEval1788 B hB hF]
  rw [originalMerge1780, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1781 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1781 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1781 (originalVector B) := by
  rw [reducedMerge1781Check, Integer.Sparse.eval_mergeBy, reducedTermEval1789 B hB hF, reducedTermEval1790 B hB hF]
  rw [originalMerge1781, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1782 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1782 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1782 (originalVector B) := by
  rw [reducedMerge1782Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1780 B hB hF, reducedMergeEval1781 B hB hF]
  rw [originalMerge1782, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1783 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1783 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1783 (originalVector B) := by
  rw [reducedMerge1783Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1779 B hB hF, reducedMergeEval1782 B hB hF]
  rw [originalMerge1783, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1784 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1784 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1784 (originalVector B) := by
  rw [reducedMerge1784Check, Integer.Sparse.eval_mergeBy, reducedTermEval1791 B hB hF, reducedTermEval1792 B hB hF]
  rw [originalMerge1784, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1785 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1785 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1785 (originalVector B) := by
  rw [reducedMerge1785Check, Integer.Sparse.eval_mergeBy, reducedTermEval1793 B hB hF, reducedTermEval1794 B hB hF]
  rw [originalMerge1785, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1786 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1786 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1786 (originalVector B) := by
  rw [reducedMerge1786Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1784 B hB hF, reducedMergeEval1785 B hB hF]
  rw [originalMerge1786, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1787 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1787 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1787 (originalVector B) := by
  rw [reducedMerge1787Check, Integer.Sparse.eval_mergeBy, reducedTermEval1795 B hB hF, reducedTermEval1796 B hB hF]
  rw [originalMerge1787, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1788 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1788 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1788 (originalVector B) := by
  rw [reducedMerge1788Check, Integer.Sparse.eval_mergeBy, reducedTermEval1797 B hB hF, reducedTermEval1798 B hB hF]
  rw [originalMerge1788, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1789 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1789 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1789 (originalVector B) := by
  rw [reducedMerge1789Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1787 B hB hF, reducedMergeEval1788 B hB hF]
  rw [originalMerge1789, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1790 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1790 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1790 (originalVector B) := by
  rw [reducedMerge1790Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1786 B hB hF, reducedMergeEval1789 B hB hF]
  rw [originalMerge1790, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1791 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1791 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1791 (originalVector B) := by
  rw [reducedMerge1791Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1783 B hB hF, reducedMergeEval1790 B hB hF]
  rw [originalMerge1791, Integer.Sparse.eval_append]
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

theorem reducedMergeEval1792 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1792 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1792 (originalVector B) := by
  rw [reducedMerge1792Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1777 B hB hF, reducedMergeEval1791 B hB hF]
  rw [originalMerge1792, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1793 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1793 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1793 (originalVector B) := by
  rw [reducedMerge1793Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1763 B hB hF, reducedMergeEval1792 B hB hF]
  rw [originalMerge1793, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1794_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1794 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1794 (originalVector B) := by
  rw [reducedMerge1794Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1734 B hB hF, reducedMergeEval1793 B hB hF]
  rw [originalMerge1794, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1794_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1794_e_oai
