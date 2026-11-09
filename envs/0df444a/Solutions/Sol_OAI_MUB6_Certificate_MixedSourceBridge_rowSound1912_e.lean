-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:15:09.55647+00:00
-- url     : https://prove2.me/submissions/8284c18c-b6b5-4f77-8844-38c72a55afd5

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E191
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2475 raw2475Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw2475 raw2475Labels = mixedMoment B raw2475step0 raw2475step0Labels := by
      have ha : raw2475step0 = (fun i j => raw2475 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2475step0 raw2475; decide +kernel
      have hl : raw2475step0Labels = raw2475Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2475 raw2475Labels permutation152 permutation4
    mixedMoment B raw2475step0 raw2475step0Labels = mixedMoment B raw2475step1 raw2475step1Labels := by
      have ha : raw2475step1 = raw2475step0 := by apply Matrix.ext; unfold raw2475step1 raw2475step0; decide +kernel
      have hl : raw2475step0Labels = labelEmbedding7 ∘ raw2475step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2475step0 raw2475step0Labels raw2475step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

theorem canonical2476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2476 raw2476Labels = mixedMoment B node3787 node3787Labels := by
  calc
    mixedMoment B raw2476 raw2476Labels = mixedMoment B raw2476step0 raw2476step0Labels := by
      have ha : raw2476step0 = (fun i j => raw2476 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2476step0 raw2476; decide +kernel
      have hl : raw2476step0Labels = raw2476Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2476 raw2476Labels permutation152 permutation4
    _ = mixedMoment B node3787 node3787Labels := by rfl

theorem canonical2477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2477 raw2477Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw2477 raw2477Labels = mixedMoment B raw2477step0 raw2477step0Labels := by
      have ha : raw2477step0 = (fun i j => raw2477 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2477step0 raw2477; decide +kernel
      have hl : raw2477step0Labels = raw2477Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2477 raw2477Labels permutation158 permutation6
    mixedMoment B raw2477step0 raw2477step0Labels = mixedMoment B raw2477step1 raw2477step1Labels := by
      have ha : raw2477step1 = -raw2477step0 := by apply Matrix.ext; change ∀ i j, raw2477step1 i j = -(raw2477step0 i j); unfold raw2477step1 raw2477step0; decide +kernel
      have hl : raw2477step1Labels = raw2477step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2477step1 raw2477step1Labels = mixedMoment B raw2477step2 raw2477step2Labels := by
      have ha : raw2477step2 = raw2477step1 := by apply Matrix.ext; unfold raw2477step2 raw2477step1; decide +kernel
      have hl : raw2477step1Labels = labelEmbedding1 ∘ raw2477step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2477step1 raw2477step1Labels raw2477step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

theorem canonical2481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2481 raw2481Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw2481 raw2481Labels = mixedMoment B raw2481step0 raw2481step0Labels := by
      have ha : raw2481step0 = (fun i j => raw2481 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2481step0 raw2481; decide +kernel
      have hl : raw2481step0Labels = raw2481Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2481 raw2481Labels permutation32 permutation4
    mixedMoment B raw2481step0 raw2481step0Labels = mixedMoment B raw2481step1 raw2481step1Labels := by
      have ha : raw2481step1 = raw2481step0 := by apply Matrix.ext; unfold raw2481step1 raw2481step0; decide +kernel
      have hl : raw2481step0Labels = labelEmbedding7 ∘ raw2481step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2481step0 raw2481step0Labels raw2481step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5404 node5404Labels := by rfl

theorem canonical2482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2482 raw2482Labels = mixedMoment B node3790 node3790Labels := by
  calc
    mixedMoment B raw2482 raw2482Labels = mixedMoment B raw2482step0 raw2482step0Labels := by
      have ha : raw2482step0 = (fun i j => raw2482 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2482step0 raw2482; decide +kernel
      have hl : raw2482step0Labels = raw2482Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2482 raw2482Labels permutation32 permutation4
    _ = mixedMoment B node3790 node3790Labels := by rfl

theorem canonical2483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2483 raw2483Labels = mixedMoment B node3815 node3815Labels := by
  calc
    mixedMoment B raw2483 raw2483Labels = mixedMoment B raw2483step0 raw2483step0Labels := by
      have ha : raw2483step0 = (fun i j => raw2483 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2483step0 raw2483; decide +kernel
      have hl : raw2483step0Labels = raw2483Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2483 raw2483Labels permutation32 permutation6
    mixedMoment B raw2483step0 raw2483step0Labels = mixedMoment B raw2483step1 raw2483step1Labels := by
      have ha : raw2483step1 = -raw2483step0 := by apply Matrix.ext; change ∀ i j, raw2483step1 i j = -(raw2483step0 i j); unfold raw2483step1 raw2483step0; decide +kernel
      have hl : raw2483step1Labels = raw2483step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2483step1 raw2483step1Labels = mixedMoment B raw2483step2 raw2483step2Labels := by
      have ha : raw2483step2 = raw2483step1 := by apply Matrix.ext; unfold raw2483step2 raw2483step1; decide +kernel
      have hl : raw2483step1Labels = labelEmbedding1 ∘ raw2483step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2483step1 raw2483step1Labels raw2483step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3815 node3815Labels := by rfl

theorem canonical2538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2538 raw2538Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw2538 raw2538Labels = mixedMoment B raw2538step0 raw2538step0Labels := by
      have ha : raw2538step0 = (fun i j => raw2538 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2538step0 raw2538; decide +kernel
      have hl : raw2538step0Labels = raw2538Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2538 raw2538Labels permutation32 permutation4
    mixedMoment B raw2538step0 raw2538step0Labels = mixedMoment B raw2538step1 raw2538step1Labels := by
      have ha : raw2538step1 = raw2538step0 := by apply Matrix.ext; unfold raw2538step1 raw2538step0; decide +kernel
      have hl : raw2538step0Labels = labelEmbedding7 ∘ raw2538step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2538step0 raw2538step0Labels raw2538step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical2539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2539 raw2539Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw2539 raw2539Labels = mixedMoment B raw2539step0 raw2539step0Labels := by
      have ha : raw2539step0 = (fun i j => raw2539 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2539step0 raw2539; decide +kernel
      have hl : raw2539step0Labels = raw2539Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2539 raw2539Labels permutation32 permutation4
    _ = mixedMoment B node3857 node3857Labels := by rfl

theorem canonical2540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2540 raw2540Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw2540 raw2540Labels = mixedMoment B raw2540step0 raw2540step0Labels := by
      have ha : raw2540step0 = (fun i j => raw2540 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2540step0 raw2540; decide +kernel
      have hl : raw2540step0Labels = raw2540Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2540 raw2540Labels permutation38 permutation6
    mixedMoment B raw2540step0 raw2540step0Labels = mixedMoment B raw2540step1 raw2540step1Labels := by
      have ha : raw2540step1 = -raw2540step0 := by apply Matrix.ext; change ∀ i j, raw2540step1 i j = -(raw2540step0 i j); unfold raw2540step1 raw2540step0; decide +kernel
      have hl : raw2540step1Labels = raw2540step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2540step1 raw2540step1Labels = mixedMoment B raw2540step2 raw2540step2Labels := by
      have ha : raw2540step2 = raw2540step1 := by apply Matrix.ext; unfold raw2540step2 raw2540step1; decide +kernel
      have hl : raw2540step1Labels = labelEmbedding1 ∘ raw2540step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2540step1 raw2540step1Labels raw2540step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

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

theorem canonical2607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2607 raw2607Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw2607 raw2607Labels = mixedMoment B raw2607step0 raw2607step0Labels := by
      have ha : raw2607step0 = (fun i j => raw2607 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2607step0 raw2607; decide +kernel
      have hl : raw2607step0Labels = raw2607Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2607 raw2607Labels permutation32 permutation4
    mixedMoment B raw2607step0 raw2607step0Labels = mixedMoment B raw2607step1 raw2607step1Labels := by
      have ha : raw2607step1 = raw2607step0 := by apply Matrix.ext; unfold raw2607step1 raw2607step0; decide +kernel
      have hl : raw2607step0Labels = labelEmbedding7 ∘ raw2607step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2607step0 raw2607step0Labels raw2607step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

theorem canonical2608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2608 raw2608Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw2608 raw2608Labels = mixedMoment B raw2608step0 raw2608step0Labels := by
      have ha : raw2608step0 = (fun i j => raw2608 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2608step0 raw2608; decide +kernel
      have hl : raw2608step0Labels = raw2608Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2608 raw2608Labels permutation32 permutation4
    _ = mixedMoment B node3983 node3983Labels := by rfl

theorem canonical2609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2609 raw2609Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw2609 raw2609Labels = mixedMoment B raw2609step0 raw2609step0Labels := by
      have ha : raw2609step0 = (fun i j => raw2609 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2609step0 raw2609; decide +kernel
      have hl : raw2609step0Labels = raw2609Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2609 raw2609Labels permutation151 permutation6
    mixedMoment B raw2609step0 raw2609step0Labels = mixedMoment B raw2609step1 raw2609step1Labels := by
      have ha : raw2609step1 = raw2609step0 := by apply Matrix.ext; unfold raw2609step1 raw2609step0; decide +kernel
      have hl : raw2609step0Labels = labelEmbedding1 ∘ raw2609step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2609step0 raw2609step0Labels raw2609step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3983 node3983Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical250
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32124 raw32124Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw32124 raw32124Labels = mixedMoment B raw32124step0 raw32124step0Labels := by
      have hz : ∀ j, raw32124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32124step0 = (fun i j => raw32124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32124step0 raw32124; decide +kernel
      have hl : raw32124step0Labels = raw32124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32124 raw32124Labels permutation346 hz
    mixedMoment B raw32124step0 raw32124step0Labels = mixedMoment B raw32124step1 raw32124step1Labels := by
      have ha : raw32124step1 = (fun i j => raw32124step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32124step1 raw32124step0; decide +kernel
      have hl : raw32124step1Labels = raw32124step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32124step0 raw32124step0Labels permutation144 permutation2
    mixedMoment B raw32124step1 raw32124step1Labels = mixedMoment B raw32124step2 raw32124step2Labels := by
      have ha : raw32124step2 = -raw32124step1 := by apply Matrix.ext; change ∀ i j, raw32124step2 i j = -(raw32124step1 i j); unfold raw32124step2 raw32124step1; decide +kernel
      have hl : raw32124step2Labels = raw32124step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5404 node5404Labels := by rfl

theorem canonical32125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32125 raw32125Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw32125 raw32125Labels = mixedMoment B raw32125step0 raw32125step0Labels := by
      have ha : raw32125step0 = (fun i j => raw32125 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32125step0 raw32125; decide +kernel
      have hl : raw32125step0Labels = raw32125Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32125 raw32125Labels permutation664 permutation2
    mixedMoment B raw32125step0 raw32125step0Labels = mixedMoment B raw32125step1 raw32125step1Labels := by
      have ha : raw32125step1 = -raw32125step0 := by apply Matrix.ext; change ∀ i j, raw32125step1 i j = -(raw32125step0 i j); unfold raw32125step1 raw32125step0; decide +kernel
      have hl : raw32125step1Labels = raw32125step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5401 node5401Labels := by rfl

theorem canonical32126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32126 raw32126Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw32126 raw32126Labels = mixedMoment B raw32126step0 raw32126step0Labels := by
      have hz : ∀ j, raw32126 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32126step0 = (fun i j => raw32126 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32126step0 raw32126; decide +kernel
      have hl : raw32126step0Labels = raw32126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32126 raw32126Labels permutation346 hz
    mixedMoment B raw32126step0 raw32126step0Labels = mixedMoment B raw32126step1 raw32126step1Labels := by
      have ha : raw32126step1 = (fun i j => raw32126step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32126step1 raw32126step0; decide +kernel
      have hl : raw32126step1Labels = raw32126step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32126step0 raw32126step0Labels permutation145 permutation7
    mixedMoment B raw32126step1 raw32126step1Labels = mixedMoment B raw32126step2 raw32126step2Labels := by
      have ha : raw32126step2 = raw32126step1 := by apply Matrix.ext; unfold raw32126step2 raw32126step1; decide +kernel
      have hl : raw32126step1Labels = labelEmbedding10 ∘ raw32126step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32126step1 raw32126step1Labels raw32126step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical32127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32127 raw32127Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw32127 raw32127Labels = mixedMoment B raw32127step0 raw32127step0Labels := by
      have hz : ∀ j, raw32127 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32127step0 = (fun i j => raw32127 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32127step0 raw32127; decide +kernel
      have hl : raw32127step0Labels = raw32127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32127 raw32127Labels permutation346 hz
    mixedMoment B raw32127step0 raw32127step0Labels = mixedMoment B raw32127step1 raw32127step1Labels := by
      have ha : raw32127step1 = (fun i j => raw32127step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32127step1 raw32127step0; decide +kernel
      have hl : raw32127step1Labels = raw32127step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32127step0 raw32127step0Labels permutation145 permutation2
    mixedMoment B raw32127step1 raw32127step1Labels = mixedMoment B raw32127step2 raw32127step2Labels := by
      have ha : raw32127step2 = -raw32127step1 := by apply Matrix.ext; change ∀ i j, raw32127step2 i j = -(raw32127step1 i j); unfold raw32127step2 raw32127step1; decide +kernel
      have hl : raw32127step2Labels = raw32127step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5410 node5410Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical251
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32128 raw32128Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw32128 raw32128Labels = mixedMoment B raw32128step0 raw32128step0Labels := by
      have hz : ∀ j, raw32128 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32128step0 = (fun i j => raw32128 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32128step0 raw32128; decide +kernel
      have hl : raw32128step0Labels = raw32128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32128 raw32128Labels permutation346 hz
    mixedMoment B raw32128step0 raw32128step0Labels = mixedMoment B raw32128step1 raw32128step1Labels := by
      have ha : raw32128step1 = (fun i j => raw32128step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32128step1 raw32128step0; decide +kernel
      have hl : raw32128step1Labels = raw32128step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32128step0 raw32128step0Labels permutation34 permutation2
    _ = mixedMoment B node5484 node5484Labels := by rfl

theorem canonical32129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32129 raw32129Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw32129 raw32129Labels = mixedMoment B raw32129step0 raw32129step0Labels := by
      have hz : ∀ j, raw32129 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32129step0 = (fun i j => raw32129 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32129step0 raw32129; decide +kernel
      have hl : raw32129step0Labels = raw32129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32129 raw32129Labels permutation346 hz
    mixedMoment B raw32129step0 raw32129step0Labels = mixedMoment B raw32129step1 raw32129step1Labels := by
      have ha : raw32129step1 = (fun i j => raw32129step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32129step1 raw32129step0; decide +kernel
      have hl : raw32129step1Labels = raw32129step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32129step0 raw32129step0Labels permutation32 permutation3
    mixedMoment B raw32129step1 raw32129step1Labels = mixedMoment B raw32129step2 raw32129step2Labels := by
      have ha : raw32129step2 = raw32129step1 := by apply Matrix.ext; unfold raw32129step2 raw32129step1; decide +kernel
      have hl : raw32129step1Labels = labelEmbedding6 ∘ raw32129step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32129step1 raw32129step1Labels raw32129step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4459 node4459Labels := by rfl

theorem canonical32130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32130 raw32130Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw32130 raw32130Labels = mixedMoment B raw32130step0 raw32130step0Labels := by
      have ha : raw32130step0 = (fun i j => raw32130 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32130step0 raw32130; decide +kernel
      have hl : raw32130step0Labels = raw32130Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32130 raw32130Labels permutation176 permutation3
    mixedMoment B raw32130step0 raw32130step0Labels = mixedMoment B raw32130step1 raw32130step1Labels := by
      have ha : raw32130step1 = raw32130step0 := by apply Matrix.ext; unfold raw32130step1 raw32130step0; decide +kernel
      have hl : raw32130step0Labels = labelEmbedding6 ∘ raw32130step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32130step0 raw32130step0Labels raw32130step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5074 node5074Labels := by rfl

theorem canonical32131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32131 raw32131Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw32131 raw32131Labels = mixedMoment B raw32131step0 raw32131step0Labels := by
      have hz : ∀ j, raw32131 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32131step0 = (fun i j => raw32131 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32131step0 raw32131; decide +kernel
      have hl : raw32131step0Labels = raw32131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32131 raw32131Labels permutation346 hz
    mixedMoment B raw32131step0 raw32131step0Labels = mixedMoment B raw32131step1 raw32131step1Labels := by
      have ha : raw32131step1 = (fun i j => raw32131step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32131step1 raw32131step0; decide +kernel
      have hl : raw32131step1Labels = raw32131step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32131step0 raw32131step0Labels permutation38 permutation3
    mixedMoment B raw32131step1 raw32131step1Labels = mixedMoment B raw32131step2 raw32131step2Labels := by
      have ha : raw32131step2 = raw32131step1 := by apply Matrix.ext; unfold raw32131step2 raw32131step1; decide +kernel
      have hl : raw32131step1Labels = labelEmbedding6 ∘ raw32131step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32131step1 raw32131step1Labels raw32131step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

theorem canonical32132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32132 raw32132Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw32132 raw32132Labels = mixedMoment B raw32132step0 raw32132step0Labels := by
      have hz : ∀ j, raw32132 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32132step0 = (fun i j => raw32132 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32132step0 raw32132; decide +kernel
      have hl : raw32132step0Labels = raw32132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32132 raw32132Labels permutation346 hz
    mixedMoment B raw32132step0 raw32132step0Labels = mixedMoment B raw32132step1 raw32132step1Labels := by
      have ha : raw32132step1 = (fun i j => raw32132step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32132step1 raw32132step0; decide +kernel
      have hl : raw32132step1Labels = raw32132step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32132step0 raw32132step0Labels permutation34 permutation3
    mixedMoment B raw32132step1 raw32132step1Labels = mixedMoment B raw32132step2 raw32132step2Labels := by
      have ha : raw32132step2 = raw32132step1 := by apply Matrix.ext; unfold raw32132step2 raw32132step1; decide +kernel
      have hl : raw32132step1Labels = labelEmbedding6 ∘ raw32132step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32132step1 raw32132step1Labels raw32132step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical32133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32133 raw32133Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw32133 raw32133Labels = mixedMoment B raw32133step0 raw32133step0Labels := by
      have hz : ∀ j, raw32133 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32133step0 = (fun i j => raw32133 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32133step0 raw32133; decide +kernel
      have hl : raw32133step0Labels = raw32133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32133 raw32133Labels permutation346 hz
    mixedMoment B raw32133step0 raw32133step0Labels = mixedMoment B raw32133step1 raw32133step1Labels := by
      have ha : raw32133step1 = (fun i j => raw32133step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32133step1 raw32133step0; decide +kernel
      have hl : raw32133step1Labels = raw32133step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32133step0 raw32133step0Labels permutation36 permutation3
    mixedMoment B raw32133step1 raw32133step1Labels = mixedMoment B raw32133step2 raw32133step2Labels := by
      have ha : raw32133step2 = raw32133step1 := by apply Matrix.ext; unfold raw32133step2 raw32133step1; decide +kernel
      have hl : raw32133step1Labels = labelEmbedding6 ∘ raw32133step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32133step1 raw32133step1Labels raw32133step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

theorem canonical32134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32134 raw32134Labels = mixedMoment B node4345 node4345Labels := by
  calc
    mixedMoment B raw32134 raw32134Labels = mixedMoment B raw32134step0 raw32134step0Labels := by
      have ha : raw32134step0 = (fun i j => raw32134 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32134step0 raw32134; decide +kernel
      have hl : raw32134step0Labels = raw32134Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32134 raw32134Labels permutation158 permutation3
    mixedMoment B raw32134step0 raw32134step0Labels = mixedMoment B raw32134step1 raw32134step1Labels := by
      have ha : raw32134step1 = raw32134step0 := by apply Matrix.ext; unfold raw32134step1 raw32134step0; decide +kernel
      have hl : raw32134step0Labels = labelEmbedding6 ∘ raw32134step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32134step0 raw32134step0Labels raw32134step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4345 node4345Labels := by rfl

theorem canonical32135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32135 raw32135Labels = mixedMoment B node4942 node4942Labels := by
  calc
    mixedMoment B raw32135 raw32135Labels = mixedMoment B raw32135step0 raw32135step0Labels := by
      have ha : raw32135step0 = (fun i j => raw32135 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32135step0 raw32135; decide +kernel
      have hl : raw32135step0Labels = raw32135Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32135 raw32135Labels permutation158 permutation3
    mixedMoment B raw32135step0 raw32135step0Labels = mixedMoment B raw32135step1 raw32135step1Labels := by
      have ha : raw32135step1 = raw32135step0 := by apply Matrix.ext; unfold raw32135step1 raw32135step0; decide +kernel
      have hl : raw32135step0Labels = labelEmbedding6 ∘ raw32135step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32135step0 raw32135step0Labels raw32135step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4942 node4942Labels := by rfl

theorem canonical32136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32136 raw32136Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw32136 raw32136Labels = mixedMoment B raw32136step0 raw32136step0Labels := by
      have ha : raw32136step0 = (fun i j => raw32136 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32136step0 raw32136; decide +kernel
      have hl : raw32136step0Labels = raw32136Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32136 raw32136Labels permutation158 permutation3
    mixedMoment B raw32136step0 raw32136step0Labels = mixedMoment B raw32136step1 raw32136step1Labels := by
      have ha : raw32136step1 = raw32136step0 := by apply Matrix.ext; unfold raw32136step1 raw32136step0; decide +kernel
      have hl : raw32136step0Labels = labelEmbedding6 ∘ raw32136step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32136step0 raw32136step0Labels raw32136step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5138 node5138Labels := by rfl

theorem canonical32137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32137 raw32137Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw32137 raw32137Labels = mixedMoment B raw32137step0 raw32137step0Labels := by
      have ha : raw32137step0 = (fun i j => raw32137 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32137step0 raw32137; decide +kernel
      have hl : raw32137step0Labels = raw32137Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32137 raw32137Labels permutation166 permutation3
    mixedMoment B raw32137step0 raw32137step0Labels = mixedMoment B raw32137step1 raw32137step1Labels := by
      have ha : raw32137step1 = raw32137step0 := by apply Matrix.ext; unfold raw32137step1 raw32137step0; decide +kernel
      have hl : raw32137step0Labels = labelEmbedding6 ∘ raw32137step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32137step0 raw32137step0Labels raw32137step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

theorem canonical32138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32138 raw32138Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw32138 raw32138Labels = mixedMoment B raw32138step0 raw32138step0Labels := by
      have ha : raw32138step0 = (fun i j => raw32138 (permutation172 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32138step0 raw32138; decide +kernel
      have hl : raw32138step0Labels = raw32138Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32138 raw32138Labels permutation172 permutation3
    mixedMoment B raw32138step0 raw32138step0Labels = mixedMoment B raw32138step1 raw32138step1Labels := by
      have ha : raw32138step1 = raw32138step0 := by apply Matrix.ext; unfold raw32138step1 raw32138step0; decide +kernel
      have hl : raw32138step0Labels = labelEmbedding6 ∘ raw32138step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32138step0 raw32138step0Labels raw32138step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5160 node5160Labels := by rfl

theorem canonical32139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32139 raw32139Labels = mixedMoment B node4357 node4357Labels := by
  calc
    mixedMoment B raw32139 raw32139Labels = mixedMoment B raw32139step0 raw32139step0Labels := by
      have hz : ∀ j, raw32139 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32139step0 = (fun i j => raw32139 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32139step0 raw32139; decide +kernel
      have hl : raw32139step0Labels = raw32139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32139 raw32139Labels permutation346 hz
    mixedMoment B raw32139step0 raw32139step0Labels = mixedMoment B raw32139step1 raw32139step1Labels := by
      have ha : raw32139step1 = (fun i j => raw32139step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32139step1 raw32139step0; decide +kernel
      have hl : raw32139step1Labels = raw32139step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32139step0 raw32139step0Labels permutation35 permutation3
    mixedMoment B raw32139step1 raw32139step1Labels = mixedMoment B raw32139step2 raw32139step2Labels := by
      have ha : raw32139step2 = raw32139step1 := by apply Matrix.ext; unfold raw32139step2 raw32139step1; decide +kernel
      have hl : raw32139step1Labels = labelEmbedding6 ∘ raw32139step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32139step1 raw32139step1Labels raw32139step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4357 node4357Labels := by rfl

theorem canonical32140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32140 raw32140Labels = mixedMoment B node4951 node4951Labels := by
  calc
    mixedMoment B raw32140 raw32140Labels = mixedMoment B raw32140step0 raw32140step0Labels := by
      have hz : ∀ j, raw32140 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32140step0 = (fun i j => raw32140 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32140step0 raw32140; decide +kernel
      have hl : raw32140step0Labels = raw32140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32140 raw32140Labels permutation346 hz
    mixedMoment B raw32140step0 raw32140step0Labels = mixedMoment B raw32140step1 raw32140step1Labels := by
      have ha : raw32140step1 = (fun i j => raw32140step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32140step1 raw32140step0; decide +kernel
      have hl : raw32140step1Labels = raw32140step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32140step0 raw32140step0Labels permutation35 permutation3
    mixedMoment B raw32140step1 raw32140step1Labels = mixedMoment B raw32140step2 raw32140step2Labels := by
      have ha : raw32140step2 = raw32140step1 := by apply Matrix.ext; unfold raw32140step2 raw32140step1; decide +kernel
      have hl : raw32140step1Labels = labelEmbedding6 ∘ raw32140step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32140step1 raw32140step1Labels raw32140step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4951 node4951Labels := by rfl

theorem canonical32141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32141 raw32141Labels = mixedMoment B node5040 node5040Labels := by
  calc
    mixedMoment B raw32141 raw32141Labels = mixedMoment B raw32141step0 raw32141step0Labels := by
      have ha : raw32141step0 = (fun i j => raw32141 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32141step0 raw32141; decide +kernel
      have hl : raw32141step0Labels = raw32141Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32141 raw32141Labels permutation179 permutation3
    mixedMoment B raw32141step0 raw32141step0Labels = mixedMoment B raw32141step1 raw32141step1Labels := by
      have ha : raw32141step1 = raw32141step0 := by apply Matrix.ext; unfold raw32141step1 raw32141step0; decide +kernel
      have hl : raw32141step0Labels = labelEmbedding6 ∘ raw32141step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32141step0 raw32141step0Labels raw32141step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5040 node5040Labels := by rfl

theorem canonical32142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32142 raw32142Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw32142 raw32142Labels = mixedMoment B raw32142step0 raw32142step0Labels := by
      have hz : ∀ j, raw32142 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32142step0 = (fun i j => raw32142 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32142step0 raw32142; decide +kernel
      have hl : raw32142step0Labels = raw32142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32142 raw32142Labels permutation346 hz
    mixedMoment B raw32142step0 raw32142step0Labels = mixedMoment B raw32142step1 raw32142step1Labels := by
      have ha : raw32142step1 = (fun i j => raw32142step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32142step1 raw32142step0; decide +kernel
      have hl : raw32142step1Labels = raw32142step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32142step0 raw32142step0Labels permutation35 permutation3
    mixedMoment B raw32142step1 raw32142step1Labels = mixedMoment B raw32142step2 raw32142step2Labels := by
      have ha : raw32142step2 = raw32142step1 := by apply Matrix.ext; unfold raw32142step2 raw32142step1; decide +kernel
      have hl : raw32142step1Labels = labelEmbedding6 ∘ raw32142step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32142step1 raw32142step1Labels raw32142step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

theorem canonical32143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32143 raw32143Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw32143 raw32143Labels = mixedMoment B raw32143step0 raw32143step0Labels := by
      have hz : ∀ j, raw32143 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32143step0 = (fun i j => raw32143 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32143step0 raw32143; decide +kernel
      have hl : raw32143step0Labels = raw32143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32143 raw32143Labels permutation346 hz
    mixedMoment B raw32143step0 raw32143step0Labels = mixedMoment B raw32143step1 raw32143step1Labels := by
      have ha : raw32143step1 = (fun i j => raw32143step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32143step1 raw32143step0; decide +kernel
      have hl : raw32143step1Labels = raw32143step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32143step0 raw32143step0Labels permutation37 permutation3
    mixedMoment B raw32143step1 raw32143step1Labels = mixedMoment B raw32143step2 raw32143step2Labels := by
      have ha : raw32143step2 = raw32143step1 := by apply Matrix.ext; unfold raw32143step2 raw32143step1; decide +kernel
      have hl : raw32143step1Labels = labelEmbedding6 ∘ raw32143step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32143step1 raw32143step1Labels raw32143step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5164 node5164Labels := by rfl

theorem canonical32144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32144 raw32144Labels = mixedMoment B node4348 node4348Labels := by
  calc
    mixedMoment B raw32144 raw32144Labels = mixedMoment B raw32144step0 raw32144step0Labels := by
      have hz : ∀ j, raw32144 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32144step0 = (fun i j => raw32144 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32144step0 raw32144; decide +kernel
      have hl : raw32144step0Labels = raw32144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32144 raw32144Labels permutation346 hz
    mixedMoment B raw32144step0 raw32144step0Labels = mixedMoment B raw32144step1 raw32144step1Labels := by
      have ha : raw32144step1 = (fun i j => raw32144step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32144step1 raw32144step0; decide +kernel
      have hl : raw32144step1Labels = raw32144step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32144step0 raw32144step0Labels permutation33 permutation3
    mixedMoment B raw32144step1 raw32144step1Labels = mixedMoment B raw32144step2 raw32144step2Labels := by
      have ha : raw32144step2 = raw32144step1 := by apply Matrix.ext; unfold raw32144step2 raw32144step1; decide +kernel
      have hl : raw32144step1Labels = labelEmbedding6 ∘ raw32144step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32144step1 raw32144step1Labels raw32144step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4348 node4348Labels := by rfl

theorem canonical32145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32145 raw32145Labels = mixedMoment B node4945 node4945Labels := by
  calc
    mixedMoment B raw32145 raw32145Labels = mixedMoment B raw32145step0 raw32145step0Labels := by
      have hz : ∀ j, raw32145 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32145step0 = (fun i j => raw32145 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32145step0 raw32145; decide +kernel
      have hl : raw32145step0Labels = raw32145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32145 raw32145Labels permutation346 hz
    mixedMoment B raw32145step0 raw32145step0Labels = mixedMoment B raw32145step1 raw32145step1Labels := by
      have ha : raw32145step1 = (fun i j => raw32145step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32145step1 raw32145step0; decide +kernel
      have hl : raw32145step1Labels = raw32145step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32145step0 raw32145step0Labels permutation33 permutation3
    mixedMoment B raw32145step1 raw32145step1Labels = mixedMoment B raw32145step2 raw32145step2Labels := by
      have ha : raw32145step2 = raw32145step1 := by apply Matrix.ext; unfold raw32145step2 raw32145step1; decide +kernel
      have hl : raw32145step1Labels = labelEmbedding6 ∘ raw32145step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32145step1 raw32145step1Labels raw32145step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4945 node4945Labels := by rfl

theorem canonical32146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32146 raw32146Labels = mixedMoment B node5035 node5035Labels := by
  calc
    mixedMoment B raw32146 raw32146Labels = mixedMoment B raw32146step0 raw32146step0Labels := by
      have ha : raw32146step0 = (fun i j => raw32146 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32146step0 raw32146; decide +kernel
      have hl : raw32146step0Labels = raw32146Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32146 raw32146Labels permutation177 permutation3
    mixedMoment B raw32146step0 raw32146step0Labels = mixedMoment B raw32146step1 raw32146step1Labels := by
      have ha : raw32146step1 = raw32146step0 := by apply Matrix.ext; unfold raw32146step1 raw32146step0; decide +kernel
      have hl : raw32146step0Labels = labelEmbedding6 ∘ raw32146step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32146step0 raw32146step0Labels raw32146step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5035 node5035Labels := by rfl

theorem canonical32147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32147 raw32147Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw32147 raw32147Labels = mixedMoment B raw32147step0 raw32147step0Labels := by
      have hz : ∀ j, raw32147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32147step0 = (fun i j => raw32147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32147step0 raw32147; decide +kernel
      have hl : raw32147step0Labels = raw32147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32147 raw32147Labels permutation346 hz
    mixedMoment B raw32147step0 raw32147step0Labels = mixedMoment B raw32147step1 raw32147step1Labels := by
      have ha : raw32147step1 = (fun i j => raw32147step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32147step1 raw32147step0; decide +kernel
      have hl : raw32147step1Labels = raw32147step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32147step0 raw32147step0Labels permutation33 permutation3
    mixedMoment B raw32147step1 raw32147step1Labels = mixedMoment B raw32147step2 raw32147step2Labels := by
      have ha : raw32147step2 = raw32147step1 := by apply Matrix.ext; unfold raw32147step2 raw32147step1; decide +kernel
      have hl : raw32147step1Labels = labelEmbedding6 ∘ raw32147step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32147step1 raw32147step1Labels raw32147step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5140 node5140Labels := by rfl

theorem canonical32148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32148 raw32148Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw32148 raw32148Labels = mixedMoment B raw32148step0 raw32148step0Labels := by
      have hz : ∀ j, raw32148 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32148step0 = (fun i j => raw32148 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32148step0 raw32148; decide +kernel
      have hl : raw32148step0Labels = raw32148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32148 raw32148Labels permutation346 hz
    mixedMoment B raw32148step0 raw32148step0Labels = mixedMoment B raw32148step1 raw32148step1Labels := by
      have ha : raw32148step1 = (fun i j => raw32148step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32148step1 raw32148step0; decide +kernel
      have hl : raw32148step1Labels = raw32148step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32148step0 raw32148step0Labels permutation36 permutation3
    mixedMoment B raw32148step1 raw32148step1Labels = mixedMoment B raw32148step2 raw32148step2Labels := by
      have ha : raw32148step2 = raw32148step1 := by apply Matrix.ext; unfold raw32148step2 raw32148step1; decide +kernel
      have hl : raw32148step1Labels = labelEmbedding6 ∘ raw32148step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32148step1 raw32148step1Labels raw32148step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5161 node5161Labels := by rfl

theorem canonical32149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32149 raw32149Labels = mixedMoment B node4347 node4347Labels := by
  calc
    mixedMoment B raw32149 raw32149Labels = mixedMoment B raw32149step0 raw32149step0Labels := by
      have hz : ∀ j, raw32149 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32149step0 = (fun i j => raw32149 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32149step0 raw32149; decide +kernel
      have hl : raw32149step0Labels = raw32149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32149 raw32149Labels permutation346 hz
    mixedMoment B raw32149step0 raw32149step0Labels = mixedMoment B raw32149step1 raw32149step1Labels := by
      have ha : raw32149step1 = (fun i j => raw32149step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32149step1 raw32149step0; decide +kernel
      have hl : raw32149step1Labels = raw32149step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32149step0 raw32149step0Labels permutation32 permutation3
    mixedMoment B raw32149step1 raw32149step1Labels = mixedMoment B raw32149step2 raw32149step2Labels := by
      have ha : raw32149step2 = raw32149step1 := by apply Matrix.ext; unfold raw32149step2 raw32149step1; decide +kernel
      have hl : raw32149step1Labels = labelEmbedding6 ∘ raw32149step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32149step1 raw32149step1Labels raw32149step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4347 node4347Labels := by rfl

theorem canonical32150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32150 raw32150Labels = mixedMoment B node4944 node4944Labels := by
  calc
    mixedMoment B raw32150 raw32150Labels = mixedMoment B raw32150step0 raw32150step0Labels := by
      have hz : ∀ j, raw32150 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32150step0 = (fun i j => raw32150 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32150step0 raw32150; decide +kernel
      have hl : raw32150step0Labels = raw32150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32150 raw32150Labels permutation346 hz
    mixedMoment B raw32150step0 raw32150step0Labels = mixedMoment B raw32150step1 raw32150step1Labels := by
      have ha : raw32150step1 = (fun i j => raw32150step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32150step1 raw32150step0; decide +kernel
      have hl : raw32150step1Labels = raw32150step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32150step0 raw32150step0Labels permutation32 permutation3
    mixedMoment B raw32150step1 raw32150step1Labels = mixedMoment B raw32150step2 raw32150step2Labels := by
      have ha : raw32150step2 = raw32150step1 := by apply Matrix.ext; unfold raw32150step2 raw32150step1; decide +kernel
      have hl : raw32150step1Labels = labelEmbedding6 ∘ raw32150step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32150step1 raw32150step1Labels raw32150step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4944 node4944Labels := by rfl

theorem canonical32151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32151 raw32151Labels = mixedMoment B node5034 node5034Labels := by
  calc
    mixedMoment B raw32151 raw32151Labels = mixedMoment B raw32151step0 raw32151step0Labels := by
      have ha : raw32151step0 = (fun i j => raw32151 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32151step0 raw32151; decide +kernel
      have hl : raw32151step0Labels = raw32151Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32151 raw32151Labels permutation176 permutation3
    mixedMoment B raw32151step0 raw32151step0Labels = mixedMoment B raw32151step1 raw32151step1Labels := by
      have ha : raw32151step1 = raw32151step0 := by apply Matrix.ext; unfold raw32151step1 raw32151step0; decide +kernel
      have hl : raw32151step0Labels = labelEmbedding6 ∘ raw32151step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32151step0 raw32151step0Labels raw32151step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5034 node5034Labels := by rfl

theorem canonical32152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32152 raw32152Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw32152 raw32152Labels = mixedMoment B raw32152step0 raw32152step0Labels := by
      have hz : ∀ j, raw32152 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32152step0 = (fun i j => raw32152 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32152step0 raw32152; decide +kernel
      have hl : raw32152step0Labels = raw32152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32152 raw32152Labels permutation346 hz
    mixedMoment B raw32152step0 raw32152step0Labels = mixedMoment B raw32152step1 raw32152step1Labels := by
      have ha : raw32152step1 = (fun i j => raw32152step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32152step1 raw32152step0; decide +kernel
      have hl : raw32152step1Labels = raw32152step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32152step0 raw32152step0Labels permutation32 permutation3
    mixedMoment B raw32152step1 raw32152step1Labels = mixedMoment B raw32152step2 raw32152step2Labels := by
      have ha : raw32152step2 = raw32152step1 := by apply Matrix.ext; unfold raw32152step2 raw32152step1; decide +kernel
      have hl : raw32152step1Labels = labelEmbedding6 ∘ raw32152step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32152step1 raw32152step1Labels raw32152step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5139 node5139Labels := by rfl

theorem canonical32153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32153 raw32153Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw32153 raw32153Labels = mixedMoment B raw32153step0 raw32153step0Labels := by
      have hz : ∀ j, raw32153 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32153step0 = (fun i j => raw32153 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32153step0 raw32153; decide +kernel
      have hl : raw32153step0Labels = raw32153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32153 raw32153Labels permutation346 hz
    mixedMoment B raw32153step0 raw32153step0Labels = mixedMoment B raw32153step1 raw32153step1Labels := by
      have ha : raw32153step1 = (fun i j => raw32153step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32153step1 raw32153step0; decide +kernel
      have hl : raw32153step1Labels = raw32153step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32153step0 raw32153step0Labels permutation145 permutation2
    mixedMoment B raw32153step1 raw32153step1Labels = mixedMoment B raw32153step2 raw32153step2Labels := by
      have ha : raw32153step2 = -raw32153step1 := by apply Matrix.ext; change ∀ i j, raw32153step2 i j = -(raw32153step1 i j); unfold raw32153step2 raw32153step1; decide +kernel
      have hl : raw32153step2Labels = raw32153step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5078 node5078Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5401 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5401 node5401Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3787 node3787Labels + mixedMoment B node3804 node3804Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2475 singletonSmall5401
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5401) = raw2475Labels := by decide +kernel
  rw [hl, canonical2475 B hB] at h
  have hc0 : mixedMoment B raw2475 (Fin.cases (0 : Fin 2) singletonSmall5401) =
      mixedMoment B node3787 node3787Labels := by
    have ha : raw2475 = raw2476 := by apply Matrix.ext; unfold raw2475 raw2476; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5401 = raw2476Labels := by decide +kernel
    rw [ha, hj, canonical2476 B hB]
  have hc1 : mixedMoment B raw2475 (Fin.cases (1 : Fin 2) singletonSmall5401) =
      mixedMoment B node3804 node3804Labels := by
    have ha : raw2475 = raw2477 := by apply Matrix.ext; unfold raw2475 raw2477; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5401 = raw2477Labels := by decide +kernel
    rw [ha, hj, canonical2477 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5404 node5404Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3790 node3790Labels + mixedMoment B node3815 node3815Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2481 singletonSmall5404
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5404) = raw2481Labels := by decide +kernel
  rw [hl, canonical2481 B hB] at h
  have hc0 : mixedMoment B raw2481 (Fin.cases (0 : Fin 2) singletonSmall5404) =
      mixedMoment B node3790 node3790Labels := by
    have ha : raw2481 = raw2482 := by apply Matrix.ext; unfold raw2481 raw2482; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5404 = raw2482Labels := by decide +kernel
    rw [ha, hj, canonical2482 B hB]
  have hc1 : mixedMoment B raw2481 (Fin.cases (1 : Fin 2) singletonSmall5404) =
      mixedMoment B node3815 node3815Labels := by
    have ha : raw2481 = raw2483 := by apply Matrix.ext; unfold raw2481 raw2483; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5404 = raw2483Labels := by decide +kernel
    rw [ha, hj, canonical2483 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5438 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5438 node5438Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3857 node3857Labels + mixedMoment B node3876 node3876Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2538 singletonSmall5438
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5438) = raw2538Labels := by decide +kernel
  rw [hl, canonical2538 B hB] at h
  have hc0 : mixedMoment B raw2538 (Fin.cases (0 : Fin 2) singletonSmall5438) =
      mixedMoment B node3857 node3857Labels := by
    have ha : raw2538 = raw2539 := by apply Matrix.ext; unfold raw2538 raw2539; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5438 = raw2539Labels := by decide +kernel
    rw [ha, hj, canonical2539 B hB]
  have hc1 : mixedMoment B raw2538 (Fin.cases (1 : Fin 2) singletonSmall5438) =
      mixedMoment B node3876 node3876Labels := by
    have ha : raw2538 = raw2540 := by apply Matrix.ext; unfold raw2538 raw2540; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5438 = raw2540Labels := by decide +kernel
    rw [ha, hj, canonical2540 B hB]
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

theorem singleton5484 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5484 node5484Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3983 node3983Labels + mixedMoment B node3983 node3983Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2607 singletonSmall5484
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5484) = raw2607Labels := by decide +kernel
  rw [hl, canonical2607 B hB] at h
  have hc0 : mixedMoment B raw2607 (Fin.cases (0 : Fin 2) singletonSmall5484) =
      mixedMoment B node3983 node3983Labels := by
    have ha : raw2607 = raw2608 := by apply Matrix.ext; unfold raw2607 raw2608; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5484 = raw2608Labels := by decide +kernel
    rw [ha, hj, canonical2608 B hB]
  have hc1 : mixedMoment B raw2607 (Fin.cases (1 : Fin 2) singletonSmall5484) =
      mixedMoment B node3983 node3983Labels := by
    have ha : raw2607 = raw2609 := by apply Matrix.ext; unfold raw2607 raw2609; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5484 = raw2609Labels := by decide +kernel
    rw [ha, hj, canonical2609 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

theorem sound3605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3605 node3605Labels = Sparse.eval nodeValue3605 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3605) = mixedMoment B node3605 node3605Labels := rfl
  simpa [nodeValue3605, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3787 node3787Labels = Sparse.eval nodeValue3787 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3787) = mixedMoment B node3787 node3787Labels := rfl
  simpa [nodeValue3787, Sparse.eval] using hc.symm

theorem sound3790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3790 node3790Labels = Sparse.eval nodeValue3790 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3790) = mixedMoment B node3790 node3790Labels := rfl
  simpa [nodeValue3790, Sparse.eval] using hc.symm

theorem sound3804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3804 node3804Labels = Sparse.eval nodeValue3804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3804) = mixedMoment B node3804 node3804Labels := rfl
  simpa [nodeValue3804, Sparse.eval] using hc.symm

theorem sound3815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3815 node3815Labels = Sparse.eval nodeValue3815 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3815) = mixedMoment B node3815 node3815Labels := rfl
  simpa [nodeValue3815, Sparse.eval] using hc.symm

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

theorem sound3857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3857 node3857Labels = Sparse.eval nodeValue3857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3857) = mixedMoment B node3857 node3857Labels := rfl
  simpa [nodeValue3857, Sparse.eval] using hc.symm

theorem sound3876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3876 node3876Labels = Sparse.eval nodeValue3876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3876) = mixedMoment B node3876 node3876Labels := rfl
  simpa [nodeValue3876, Sparse.eval] using hc.symm

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

theorem sound3983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3983 node3983Labels = Sparse.eval nodeValue3983 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3983) = mixedMoment B node3983 node3983Labels := rfl
  simpa [nodeValue3983, Sparse.eval] using hc.symm

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

theorem sound4345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4345 node4345Labels = Sparse.eval nodeValue4345 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4345) = mixedMoment B node4345 node4345Labels := rfl
  simpa [nodeValue4345, Sparse.eval] using hc.symm

theorem sound4347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4347 node4347Labels = Sparse.eval nodeValue4347 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4347) = mixedMoment B node4347 node4347Labels := rfl
  simpa [nodeValue4347, Sparse.eval] using hc.symm

theorem sound4348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4348 node4348Labels = Sparse.eval nodeValue4348 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4348) = mixedMoment B node4348 node4348Labels := rfl
  simpa [nodeValue4348, Sparse.eval] using hc.symm

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

theorem sound4459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4459 node4459Labels = Sparse.eval nodeValue4459 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4459) = mixedMoment B node4459 node4459Labels := rfl
  simpa [nodeValue4459, Sparse.eval] using hc.symm

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

theorem sound5074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5074 node5074Labels = Sparse.eval nodeValue5074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5074) = mixedMoment B node5074 node5074Labels := rfl
  simpa [nodeValue5074, Sparse.eval] using hc.symm

theorem sound5078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5078 node5078Labels = Sparse.eval nodeValue5078 (mixedVector B) := by
  have h := singleton5078 B _hB
  rw [sound2485 B _hB _hF, sound3481 B _hB _hF] at h
  norm_num [nodeValue5078, nodeValue2485, nodeValue3481, Sparse.eval] at h ⊢
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

theorem sound5260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5260 node5260Labels = Sparse.eval nodeValue5260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5260) = mixedMoment B node5260 node5260Labels := rfl
  simpa [nodeValue5260, Sparse.eval] using hc.symm

theorem sound5284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5284 node5284Labels = Sparse.eval nodeValue5284 (mixedVector B) := by
  have h := singleton5284 B _hB
  rw [sound3077 B _hB _hF, sound3625 B _hB _hF] at h
  norm_num [nodeValue5284, nodeValue3077, nodeValue3625, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5289 node5289Labels = Sparse.eval nodeValue5289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5289) = mixedMoment B node5289 node5289Labels := rfl
  simpa [nodeValue5289, Sparse.eval] using hc.symm

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

theorem sound5401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5401 node5401Labels = Sparse.eval nodeValue5401 (mixedVector B) := by
  have h := singleton5401 B _hB
  rw [sound3787 B _hB _hF, sound3804 B _hB _hF] at h
  norm_num [nodeValue5401, nodeValue3787, nodeValue3804, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5404 node5404Labels = Sparse.eval nodeValue5404 (mixedVector B) := by
  have h := singleton5404 B _hB
  rw [sound3790 B _hB _hF, sound3815 B _hB _hF] at h
  norm_num [nodeValue5404, nodeValue3790, nodeValue3815, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5410 node5410Labels = Sparse.eval nodeValue5410 (mixedVector B) := by
  simpa only [nodeValue5410, Sparse.eval_nil] using zero5410 B _hB _hF

theorem sound5438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5438 node5438Labels = Sparse.eval nodeValue5438 (mixedVector B) := by
  have h := singleton5438 B _hB
  rw [sound3857 B _hB _hF, sound3876 B _hB _hF] at h
  norm_num [nodeValue5438, nodeValue3857, nodeValue3876, Sparse.eval] at h ⊢
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

theorem sound5484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5484 node5484Labels = Sparse.eval nodeValue5484 (mixedVector B) := by
  have h := singleton5484 B _hB
  rw [sound3983 B _hB _hF] at h
  norm_num [nodeValue5484, nodeValue3983, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources73
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2348 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2348 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2348 + difference 0 1) (sourceB2348 + difference 1 0) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA2348 + difference 0 1) (sourceB2348 + difference 1 0) sourceC2348) = raw32124 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32124; decide +kernel
    rw [ha]
    exact (canonical32124 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2348 + difference 0 2) (sourceB2348 + difference 2 0) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA2348 + difference 0 2) (sourceB2348 + difference 2 0) sourceC2348) = raw32125 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32125; decide +kernel
    rw [ha]
    exact (canonical32125 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2348 + difference 0 3) (sourceB2348 + difference 3 0) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA2348 + difference 0 3) (sourceB2348 + difference 3 0) sourceC2348) = raw32126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32126; decide +kernel
    rw [ha]
    exact (canonical32126 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2348 + difference 0 4) (sourceB2348 + difference 4 0) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA2348 + difference 0 4) (sourceB2348 + difference 4 0) sourceC2348) = raw32127 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32127; decide +kernel
    rw [ha]
    exact (canonical32127 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2348 + difference 0 5) (sourceB2348 + difference 5 0) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA2348 + difference 0 5) (sourceB2348 + difference 5 0) sourceC2348) = raw32128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32128; decide +kernel
    rw [ha]
    exact (canonical32128 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2348 + difference 1 0) (sourceB2348 + difference 0 1) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA2348 + difference 1 0) (sourceB2348 + difference 0 1) sourceC2348) = raw32129 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32129; decide +kernel
    rw [ha]
    exact (canonical32129 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2348 + difference 1 2) (sourceB2348 + difference 2 1) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA2348 + difference 1 2) (sourceB2348 + difference 2 1) sourceC2348) = raw32130 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32130; decide +kernel
    rw [ha]
    exact (canonical32130 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2348 + difference 1 3) (sourceB2348 + difference 3 1) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA2348 + difference 1 3) (sourceB2348 + difference 3 1) sourceC2348) = raw32131 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32131; decide +kernel
    rw [ha]
    exact (canonical32131 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2348 + difference 1 4) (sourceB2348 + difference 4 1) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA2348 + difference 1 4) (sourceB2348 + difference 4 1) sourceC2348) = raw32132 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32132; decide +kernel
    rw [ha]
    exact (canonical32132 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2348 + difference 1 5) (sourceB2348 + difference 5 1) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA2348 + difference 1 5) (sourceB2348 + difference 5 1) sourceC2348) = raw32133 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32133; decide +kernel
    rw [ha]
    exact (canonical32133 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2348 + difference 2 0) (sourceB2348 + difference 0 2) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4345) := by
    have ha : (tripleCharges (sourceA2348 + difference 2 0) (sourceB2348 + difference 0 2) sourceC2348) = raw32134 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32134; decide +kernel
    rw [ha]
    exact (canonical32134 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2348 + difference 2 1) (sourceB2348 + difference 1 2) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4942) := by
    have ha : (tripleCharges (sourceA2348 + difference 2 1) (sourceB2348 + difference 1 2) sourceC2348) = raw32135 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32135; decide +kernel
    rw [ha]
    exact (canonical32135 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2348 + difference 2 3) (sourceB2348 + difference 3 2) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA2348 + difference 2 3) (sourceB2348 + difference 3 2) sourceC2348) = raw32136 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32136; decide +kernel
    rw [ha]
    exact (canonical32136 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2348 + difference 2 4) (sourceB2348 + difference 4 2) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2348 + difference 2 4) (sourceB2348 + difference 4 2) sourceC2348) = raw32137 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32137; decide +kernel
    rw [ha]
    exact (canonical32137 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2348 + difference 2 5) (sourceB2348 + difference 5 2) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5160) := by
    have ha : (tripleCharges (sourceA2348 + difference 2 5) (sourceB2348 + difference 5 2) sourceC2348) = raw32138 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32138; decide +kernel
    rw [ha]
    exact (canonical32138 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2348 + difference 3 0) (sourceB2348 + difference 0 3) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4357) := by
    have ha : (tripleCharges (sourceA2348 + difference 3 0) (sourceB2348 + difference 0 3) sourceC2348) = raw32139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32139; decide +kernel
    rw [ha]
    exact (canonical32139 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2348 + difference 3 1) (sourceB2348 + difference 1 3) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4951) := by
    have ha : (tripleCharges (sourceA2348 + difference 3 1) (sourceB2348 + difference 1 3) sourceC2348) = raw32140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32140; decide +kernel
    rw [ha]
    exact (canonical32140 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2348 + difference 3 2) (sourceB2348 + difference 2 3) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5040) := by
    have ha : (tripleCharges (sourceA2348 + difference 3 2) (sourceB2348 + difference 2 3) sourceC2348) = raw32141 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32141; decide +kernel
    rw [ha]
    exact (canonical32141 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2348 + difference 3 4) (sourceB2348 + difference 4 3) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2348 + difference 3 4) (sourceB2348 + difference 4 3) sourceC2348) = raw32142 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32142; decide +kernel
    rw [ha]
    exact (canonical32142 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2348 + difference 3 5) (sourceB2348 + difference 5 3) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA2348 + difference 3 5) (sourceB2348 + difference 5 3) sourceC2348) = raw32143 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32143; decide +kernel
    rw [ha]
    exact (canonical32143 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2348 + difference 4 0) (sourceB2348 + difference 0 4) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4348) := by
    have ha : (tripleCharges (sourceA2348 + difference 4 0) (sourceB2348 + difference 0 4) sourceC2348) = raw32144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32144; decide +kernel
    rw [ha]
    exact (canonical32144 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2348 + difference 4 1) (sourceB2348 + difference 1 4) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4945) := by
    have ha : (tripleCharges (sourceA2348 + difference 4 1) (sourceB2348 + difference 1 4) sourceC2348) = raw32145 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32145; decide +kernel
    rw [ha]
    exact (canonical32145 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2348 + difference 4 2) (sourceB2348 + difference 2 4) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5035) := by
    have ha : (tripleCharges (sourceA2348 + difference 4 2) (sourceB2348 + difference 2 4) sourceC2348) = raw32146 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32146; decide +kernel
    rw [ha]
    exact (canonical32146 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2348 + difference 4 3) (sourceB2348 + difference 3 4) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA2348 + difference 4 3) (sourceB2348 + difference 3 4) sourceC2348) = raw32147 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32147; decide +kernel
    rw [ha]
    exact (canonical32147 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2348 + difference 4 5) (sourceB2348 + difference 5 4) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA2348 + difference 4 5) (sourceB2348 + difference 5 4) sourceC2348) = raw32148 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32148; decide +kernel
    rw [ha]
    exact (canonical32148 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2348 + difference 5 0) (sourceB2348 + difference 0 5) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4347) := by
    have ha : (tripleCharges (sourceA2348 + difference 5 0) (sourceB2348 + difference 0 5) sourceC2348) = raw32149 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32149; decide +kernel
    rw [ha]
    exact (canonical32149 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2348 + difference 5 1) (sourceB2348 + difference 1 5) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4944) := by
    have ha : (tripleCharges (sourceA2348 + difference 5 1) (sourceB2348 + difference 1 5) sourceC2348) = raw32150 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32150; decide +kernel
    rw [ha]
    exact (canonical32150 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2348 + difference 5 2) (sourceB2348 + difference 2 5) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5034) := by
    have ha : (tripleCharges (sourceA2348 + difference 5 2) (sourceB2348 + difference 2 5) sourceC2348) = raw32151 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32151; decide +kernel
    rw [ha]
    exact (canonical32151 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2348 + difference 5 3) (sourceB2348 + difference 3 5) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA2348 + difference 5 3) (sourceB2348 + difference 3 5) sourceC2348) = raw32152 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32152; decide +kernel
    rw [ha]
    exact (canonical32152 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2348 + difference 5 4) (sourceB2348 + difference 4 5) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA2348 + difference 5 4) (sourceB2348 + difference 4 5) sourceC2348) = raw32153 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32153; decide +kernel
    rw [ha]
    exact (canonical32153 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2348 sourceB2348 sourceC2348
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2348, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic119
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1912 : Integer.Sparse.reindex keyMap MixedData.row1912 = numericRow1912 := by decide +kernel

theorem numericCheck1912 (x : Master → ℝ) : Integer.Sparse.eval numericRow1912 x =
    (4 : ℝ) * reducedSource1912 x := by
  norm_num [numericRow1912, reducedSource1912, Integer.Sparse.eval, Sparse.eval, nodeValue4345, nodeValue4347, nodeValue4348, nodeValue4357, nodeValue4459, nodeValue4942, nodeValue4944, nodeValue4945, nodeValue4951, nodeValue5034, nodeValue5035, nodeValue5040, nodeValue5074, nodeValue5078, nodeValue5138, nodeValue5139, nodeValue5140, nodeValue5149, nodeValue5152, nodeValue5160, nodeValue5161, nodeValue5164, nodeValue5260, nodeValue5284, nodeValue5289, nodeValue5401, nodeValue5404, nodeValue5410, nodeValue5438, nodeValue5484]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows119
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1912 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1912 (mixedVector B) = 0 := by
  have h4345 : mixedVector B (Sum.inr 4345) = Sparse.eval nodeValue4345 (mixedVector B) := by
    change mixedMoment B node4345 node4345Labels = _
    exact sound4345 B hB hF
  have h4347 : mixedVector B (Sum.inr 4347) = Sparse.eval nodeValue4347 (mixedVector B) := by
    change mixedMoment B node4347 node4347Labels = _
    exact sound4347 B hB hF
  have h4348 : mixedVector B (Sum.inr 4348) = Sparse.eval nodeValue4348 (mixedVector B) := by
    change mixedMoment B node4348 node4348Labels = _
    exact sound4348 B hB hF
  have h4357 : mixedVector B (Sum.inr 4357) = Sparse.eval nodeValue4357 (mixedVector B) := by
    change mixedMoment B node4357 node4357Labels = _
    exact sound4357 B hB hF
  have h4459 : mixedVector B (Sum.inr 4459) = Sparse.eval nodeValue4459 (mixedVector B) := by
    change mixedMoment B node4459 node4459Labels = _
    exact sound4459 B hB hF
  have h4942 : mixedVector B (Sum.inr 4942) = Sparse.eval nodeValue4942 (mixedVector B) := by
    change mixedMoment B node4942 node4942Labels = _
    exact sound4942 B hB hF
  have h4944 : mixedVector B (Sum.inr 4944) = Sparse.eval nodeValue4944 (mixedVector B) := by
    change mixedMoment B node4944 node4944Labels = _
    exact sound4944 B hB hF
  have h4945 : mixedVector B (Sum.inr 4945) = Sparse.eval nodeValue4945 (mixedVector B) := by
    change mixedMoment B node4945 node4945Labels = _
    exact sound4945 B hB hF
  have h4951 : mixedVector B (Sum.inr 4951) = Sparse.eval nodeValue4951 (mixedVector B) := by
    change mixedMoment B node4951 node4951Labels = _
    exact sound4951 B hB hF
  have h5034 : mixedVector B (Sum.inr 5034) = Sparse.eval nodeValue5034 (mixedVector B) := by
    change mixedMoment B node5034 node5034Labels = _
    exact sound5034 B hB hF
  have h5035 : mixedVector B (Sum.inr 5035) = Sparse.eval nodeValue5035 (mixedVector B) := by
    change mixedMoment B node5035 node5035Labels = _
    exact sound5035 B hB hF
  have h5040 : mixedVector B (Sum.inr 5040) = Sparse.eval nodeValue5040 (mixedVector B) := by
    change mixedMoment B node5040 node5040Labels = _
    exact sound5040 B hB hF
  have h5074 : mixedVector B (Sum.inr 5074) = Sparse.eval nodeValue5074 (mixedVector B) := by
    change mixedMoment B node5074 node5074Labels = _
    exact sound5074 B hB hF
  have h5078 : mixedVector B (Sum.inr 5078) = Sparse.eval nodeValue5078 (mixedVector B) := by
    change mixedMoment B node5078 node5078Labels = _
    exact sound5078 B hB hF
  have h5138 : mixedVector B (Sum.inr 5138) = Sparse.eval nodeValue5138 (mixedVector B) := by
    change mixedMoment B node5138 node5138Labels = _
    exact sound5138 B hB hF
  have h5139 : mixedVector B (Sum.inr 5139) = Sparse.eval nodeValue5139 (mixedVector B) := by
    change mixedMoment B node5139 node5139Labels = _
    exact sound5139 B hB hF
  have h5140 : mixedVector B (Sum.inr 5140) = Sparse.eval nodeValue5140 (mixedVector B) := by
    change mixedMoment B node5140 node5140Labels = _
    exact sound5140 B hB hF
  have h5149 : mixedVector B (Sum.inr 5149) = Sparse.eval nodeValue5149 (mixedVector B) := by
    change mixedMoment B node5149 node5149Labels = _
    exact sound5149 B hB hF
  have h5152 : mixedVector B (Sum.inr 5152) = Sparse.eval nodeValue5152 (mixedVector B) := by
    change mixedMoment B node5152 node5152Labels = _
    exact sound5152 B hB hF
  have h5160 : mixedVector B (Sum.inr 5160) = Sparse.eval nodeValue5160 (mixedVector B) := by
    change mixedMoment B node5160 node5160Labels = _
    exact sound5160 B hB hF
  have h5161 : mixedVector B (Sum.inr 5161) = Sparse.eval nodeValue5161 (mixedVector B) := by
    change mixedMoment B node5161 node5161Labels = _
    exact sound5161 B hB hF
  have h5164 : mixedVector B (Sum.inr 5164) = Sparse.eval nodeValue5164 (mixedVector B) := by
    change mixedMoment B node5164 node5164Labels = _
    exact sound5164 B hB hF
  have h5260 : mixedVector B (Sum.inr 5260) = Sparse.eval nodeValue5260 (mixedVector B) := by
    change mixedMoment B node5260 node5260Labels = _
    exact sound5260 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5289 : mixedVector B (Sum.inr 5289) = Sparse.eval nodeValue5289 (mixedVector B) := by
    change mixedMoment B node5289 node5289Labels = _
    exact sound5289 B hB hF
  have h5401 : mixedVector B (Sum.inr 5401) = Sparse.eval nodeValue5401 (mixedVector B) := by
    change mixedMoment B node5401 node5401Labels = _
    exact sound5401 B hB hF
  have h5404 : mixedVector B (Sum.inr 5404) = Sparse.eval nodeValue5404 (mixedVector B) := by
    change mixedMoment B node5404 node5404Labels = _
    exact sound5404 B hB hF
  have h5410 : mixedVector B (Sum.inr 5410) = Sparse.eval nodeValue5410 (mixedVector B) := by
    change mixedMoment B node5410 node5410Labels = _
    exact sound5410 B hB hF
  have h5438 : mixedVector B (Sum.inr 5438) = Sparse.eval nodeValue5438 (mixedVector B) := by
    change mixedMoment B node5438 node5438Labels = _
    exact sound5438 B hB hF
  have h5484 : mixedVector B (Sum.inr 5484) = Sparse.eval nodeValue5484 (mixedVector B) := by
    change mixedMoment B node5484 node5484Labels = _
    exact sound5484 B hB hF
  simpa only [sourceForm2348, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4345, h4347, h4348, h4357, h4459, h4942, h4944, h4945, h4951, h5034, h5035, h5040, h5074, h5078, h5138, h5139, h5140, h5149, h5152, h5160, h5161, h5164, h5260, h5284, h5289, h5401, h5404, h5410, h5438, h5484, reducedSource1912] using sourceEq2348 B hB

theorem rowSound1912_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1912 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1912, numericCheck1912, reducedZero1912 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912_e_oai
