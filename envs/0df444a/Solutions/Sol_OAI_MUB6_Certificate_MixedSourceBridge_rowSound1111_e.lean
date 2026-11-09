-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T20:09:35.585698+00:00
-- url     : https://prove2.me/submissions/0b4a5b4b-9ee1-4aed-8be4-2525222d04e1

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E124
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical60 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw60 raw60Labels = mixedMoment B node1271 node1271Labels := by
  calc
    mixedMoment B raw60 raw60Labels = mixedMoment B raw60step0 raw60step0Labels := by
      have ha : raw60step0 = (fun i j => raw60 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw60step0 raw60; decide +kernel
      have hl : raw60step0Labels = raw60Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw60 raw60Labels permutation8 permutation5
    mixedMoment B raw60step0 raw60step0Labels = mixedMoment B raw60step1 raw60step1Labels := by
      have ha : raw60step1 = raw60step0 := by apply Matrix.ext; unfold raw60step1 raw60step0; decide +kernel
      have hl : raw60step0Labels = labelEmbedding1 ∘ raw60step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw60step0 raw60step0Labels raw60step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1271 node1271Labels := by rfl

theorem canonical61 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw61 raw61Labels = mixedMoment B node143 node143Labels := by
  calc
    mixedMoment B raw61 raw61Labels = mixedMoment B raw61step0 raw61step0Labels := by
      have ha : raw61step0 = (fun i j => raw61 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw61step0 raw61; decide +kernel
      have hl : raw61step0Labels = raw61Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw61 raw61Labels permutation8 permutation4
    _ = mixedMoment B node143 node143Labels := by rfl

theorem canonical86 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw86 raw86Labels = mixedMoment B node1307 node1307Labels := by
  calc
    mixedMoment B raw86 raw86Labels = mixedMoment B raw86step0 raw86step0Labels := by
      have ha : raw86step0 = (fun i j => raw86 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw86step0 raw86; decide +kernel
      have hl : raw86step0Labels = raw86Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw86 raw86Labels permutation2 permutation5
    mixedMoment B raw86step0 raw86step0Labels = mixedMoment B raw86step1 raw86step1Labels := by
      have ha : raw86step1 = raw86step0 := by apply Matrix.ext; unfold raw86step1 raw86step0; decide +kernel
      have hl : raw86step0Labels = labelEmbedding1 ∘ raw86step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw86step0 raw86step0Labels raw86step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1307 node1307Labels := by rfl

theorem canonical87 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw87 raw87Labels = mixedMoment B node158 node158Labels := by
  calc
    mixedMoment B raw87 raw87Labels = mixedMoment B raw87step0 raw87step0Labels := by
      have ha : raw87step0 = (fun i j => raw87 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw87step0 raw87; decide +kernel
      have hl : raw87step0Labels = raw87Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw87 raw87Labels permutation2 permutation4
    _ = mixedMoment B node158 node158Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw138 raw138Labels = mixedMoment B node1417 node1417Labels := by
  calc
    mixedMoment B raw138 raw138Labels = mixedMoment B raw138step0 raw138step0Labels := by
      have ha : raw138step0 = (fun i j => raw138 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw138step0 raw138; decide +kernel
      have hl : raw138step0Labels = raw138Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw138 raw138Labels permutation8 permutation5
    mixedMoment B raw138step0 raw138step0Labels = mixedMoment B raw138step1 raw138step1Labels := by
      have ha : raw138step1 = raw138step0 := by apply Matrix.ext; unfold raw138step1 raw138step0; decide +kernel
      have hl : raw138step0Labels = labelEmbedding1 ∘ raw138step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw138step0 raw138step0Labels raw138step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1417 node1417Labels := by rfl

theorem canonical139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw139 raw139Labels = mixedMoment B node90 node90Labels := by
  calc
    mixedMoment B raw139 raw139Labels = mixedMoment B raw139step0 raw139step0Labels := by
      have ha : raw139step0 = (fun i j => raw139 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw139step0 raw139; decide +kernel
      have hl : raw139step0Labels = raw139Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw139 raw139Labels permutation8 permutation4
    _ = mixedMoment B node90 node90Labels := by rfl

theorem canonical166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw166 raw166Labels = mixedMoment B node1453 node1453Labels := by
  calc
    mixedMoment B raw166 raw166Labels = mixedMoment B raw166step0 raw166step0Labels := by
      have ha : raw166step0 = (fun i j => raw166 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw166step0 raw166; decide +kernel
      have hl : raw166step0Labels = raw166Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw166 raw166Labels permutation2 permutation5
    mixedMoment B raw166step0 raw166step0Labels = mixedMoment B raw166step1 raw166step1Labels := by
      have ha : raw166step1 = raw166step0 := by apply Matrix.ext; unfold raw166step1 raw166step0; decide +kernel
      have hl : raw166step0Labels = labelEmbedding1 ∘ raw166step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw166step0 raw166step0Labels raw166step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1453 node1453Labels := by rfl

theorem canonical167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw167 raw167Labels = mixedMoment B node107 node107Labels := by
  calc
    mixedMoment B raw167 raw167Labels = mixedMoment B raw167step0 raw167step0Labels := by
      have ha : raw167step0 = (fun i j => raw167 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw167step0 raw167; decide +kernel
      have hl : raw167step0Labels = raw167Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw167 raw167Labels permutation2 permutation4
    _ = mixedMoment B node107 node107Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical159
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20447 raw20447Labels = mixedMoment B node1091 node1091Labels := by
  calc
    mixedMoment B raw20447 raw20447Labels = mixedMoment B raw20447step0 raw20447step0Labels := by
      have hz : ∀ j, raw20447 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20447step0 = (fun i j => raw20447 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20447step0 raw20447; decide +kernel
      have hl : raw20447step0Labels = raw20447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20447 raw20447Labels permutation434 hz
    mixedMoment B raw20447step0 raw20447step0Labels = mixedMoment B raw20447step1 raw20447step1Labels := by
      have hz : ∀ j, raw20447step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20447step1 = (fun i j => raw20447step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20447step1 raw20447step0; decide +kernel
      have hl : raw20447step1Labels = raw20447step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20447step0 raw20447step0Labels permutation80 hz
    mixedMoment B raw20447step1 raw20447step1Labels = mixedMoment B raw20447step2 raw20447step2Labels := by
      have hz : ∀ j, raw20447step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20447step2 = (fun i j => raw20447step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20447step2 raw20447step1; decide +kernel
      have hl : raw20447step2Labels = raw20447step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20447step1 raw20447step1Labels permutation14 hz
    mixedMoment B raw20447step2 raw20447step2Labels = mixedMoment B raw20447step3 raw20447step3Labels := by
      have ha : raw20447step3 = (fun i j => raw20447step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20447step3 raw20447step2; decide +kernel
      have hl : raw20447step3Labels = raw20447step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20447step2 raw20447step2Labels permutation2 permutation7
    mixedMoment B raw20447step3 raw20447step3Labels = mixedMoment B raw20447step4 raw20447step4Labels := by
      have ha : raw20447step4 = raw20447step3 := by apply Matrix.ext; unfold raw20447step4 raw20447step3; decide +kernel
      have hl : raw20447step3Labels = labelEmbedding1 ∘ raw20447step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20447step3 raw20447step3Labels raw20447step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1091 node1091Labels := by rfl

theorem canonical20452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20452 raw20452Labels = mixedMoment B node1243 node1243Labels := by
  calc
    mixedMoment B raw20452 raw20452Labels = mixedMoment B raw20452step0 raw20452step0Labels := by
      have hz : ∀ j, raw20452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20452step0 = (fun i j => raw20452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20452step0 raw20452; decide +kernel
      have hl : raw20452step0Labels = raw20452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20452 raw20452Labels permutation434 hz
    mixedMoment B raw20452step0 raw20452step0Labels = mixedMoment B raw20452step1 raw20452step1Labels := by
      have hz : ∀ j, raw20452step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20452step1 = (fun i j => raw20452step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20452step1 raw20452step0; decide +kernel
      have hl : raw20452step1Labels = raw20452step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20452step0 raw20452step0Labels permutation80 hz
    mixedMoment B raw20452step1 raw20452step1Labels = mixedMoment B raw20452step2 raw20452step2Labels := by
      have ha : raw20452step2 = (fun i j => raw20452step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20452step2 raw20452step1; decide +kernel
      have hl : raw20452step2Labels = raw20452step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20452step1 raw20452step1Labels permutation8 permutation7
    mixedMoment B raw20452step2 raw20452step2Labels = mixedMoment B raw20452step3 raw20452step3Labels := by
      have ha : raw20452step3 = raw20452step2 := by apply Matrix.ext; unfold raw20452step3 raw20452step2; decide +kernel
      have hl : raw20452step2Labels = labelEmbedding1 ∘ raw20452step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20452step2 raw20452step2Labels raw20452step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1243 node1243Labels := by rfl

theorem canonical20457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20457 raw20457Labels = mixedMoment B node1243 node1243Labels := by
  calc
    mixedMoment B raw20457 raw20457Labels = mixedMoment B raw20457step0 raw20457step0Labels := by
      have hz : ∀ j, raw20457 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20457step0 = (fun i j => raw20457 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20457step0 raw20457; decide +kernel
      have hl : raw20457step0Labels = raw20457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20457 raw20457Labels permutation434 hz
    mixedMoment B raw20457step0 raw20457step0Labels = mixedMoment B raw20457step1 raw20457step1Labels := by
      have hz : ∀ j, raw20457step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20457step1 = (fun i j => raw20457step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20457step1 raw20457step0; decide +kernel
      have hl : raw20457step1Labels = raw20457step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20457step0 raw20457step0Labels permutation56 hz
    mixedMoment B raw20457step1 raw20457step1Labels = mixedMoment B raw20457step2 raw20457step2Labels := by
      have ha : raw20457step2 = (fun i j => raw20457step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20457step2 raw20457step1; decide +kernel
      have hl : raw20457step2Labels = raw20457step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20457step1 raw20457step1Labels permutation8 permutation7
    mixedMoment B raw20457step2 raw20457step2Labels = mixedMoment B raw20457step3 raw20457step3Labels := by
      have ha : raw20457step3 = raw20457step2 := by apply Matrix.ext; unfold raw20457step3 raw20457step2; decide +kernel
      have hl : raw20457step2Labels = labelEmbedding1 ∘ raw20457step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20457step2 raw20457step2Labels raw20457step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1243 node1243Labels := by rfl

theorem canonical20462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20462 raw20462Labels = mixedMoment B node1243 node1243Labels := by
  calc
    mixedMoment B raw20462 raw20462Labels = mixedMoment B raw20462step0 raw20462step0Labels := by
      have hz : ∀ j, raw20462 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20462step0 = (fun i j => raw20462 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20462step0 raw20462; decide +kernel
      have hl : raw20462step0Labels = raw20462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20462 raw20462Labels permutation346 hz
    mixedMoment B raw20462step0 raw20462step0Labels = mixedMoment B raw20462step1 raw20462step1Labels := by
      have hz : ∀ j, raw20462step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20462step1 = (fun i j => raw20462step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20462step1 raw20462step0; decide +kernel
      have hl : raw20462step1Labels = raw20462step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20462step0 raw20462step0Labels permutation56 hz
    mixedMoment B raw20462step1 raw20462step1Labels = mixedMoment B raw20462step2 raw20462step2Labels := by
      have ha : raw20462step2 = (fun i j => raw20462step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20462step2 raw20462step1; decide +kernel
      have hl : raw20462step2Labels = raw20462step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20462step1 raw20462step1Labels permutation8 permutation7
    mixedMoment B raw20462step2 raw20462step2Labels = mixedMoment B raw20462step3 raw20462step3Labels := by
      have ha : raw20462step3 = raw20462step2 := by apply Matrix.ext; unfold raw20462step3 raw20462step2; decide +kernel
      have hl : raw20462step2Labels = labelEmbedding1 ∘ raw20462step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20462step2 raw20462step2Labels raw20462step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1243 node1243Labels := by rfl

theorem canonical20469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20469 raw20469Labels = mixedMoment B node1452 node1452Labels := by
  calc
    mixedMoment B raw20469 raw20469Labels = mixedMoment B raw20469step0 raw20469step0Labels := by
      have hz : ∀ j, raw20469 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20469step0 = (fun i j => raw20469 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20469step0 raw20469; decide +kernel
      have hl : raw20469step0Labels = raw20469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20469 raw20469Labels permutation434 hz
    mixedMoment B raw20469step0 raw20469step0Labels = mixedMoment B raw20469step1 raw20469step1Labels := by
      have hz : ∀ j, raw20469step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20469step1 = (fun i j => raw20469step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20469step1 raw20469step0; decide +kernel
      have hl : raw20469step1Labels = raw20469step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20469step0 raw20469step0Labels permutation80 hz
    mixedMoment B raw20469step1 raw20469step1Labels = mixedMoment B raw20469step2 raw20469step2Labels := by
      have hz : ∀ j, raw20469step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20469step2 = (fun i j => raw20469step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20469step2 raw20469step1; decide +kernel
      have hl : raw20469step2Labels = raw20469step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20469step1 raw20469step1Labels permutation14 hz
    mixedMoment B raw20469step2 raw20469step2Labels = mixedMoment B raw20469step3 raw20469step3Labels := by
      have ha : raw20469step3 = (fun i j => raw20469step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20469step3 raw20469step2; decide +kernel
      have hl : raw20469step3Labels = raw20469step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20469step2 raw20469step2Labels permutation2 permutation7
    mixedMoment B raw20469step3 raw20469step3Labels = mixedMoment B raw20469step4 raw20469step4Labels := by
      have ha : raw20469step4 = raw20469step3 := by apply Matrix.ext; unfold raw20469step4 raw20469step3; decide +kernel
      have hl : raw20469step3Labels = labelEmbedding1 ∘ raw20469step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20469step3 raw20469step3Labels raw20469step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1452 node1452Labels := by rfl

theorem canonical20470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20470 raw20470Labels = mixedMoment B node1271 node1271Labels := by
  calc
    mixedMoment B raw20470 raw20470Labels = mixedMoment B raw20470step0 raw20470step0Labels := by
      have hz : ∀ j, raw20470 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20470step0 = (fun i j => raw20470 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20470step0 raw20470; decide +kernel
      have hl : raw20470step0Labels = raw20470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20470 raw20470Labels permutation434 hz
    mixedMoment B raw20470step0 raw20470step0Labels = mixedMoment B raw20470step1 raw20470step1Labels := by
      have hz : ∀ j, raw20470step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20470step1 = (fun i j => raw20470step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20470step1 raw20470step0; decide +kernel
      have hl : raw20470step1Labels = raw20470step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20470step0 raw20470step0Labels permutation80 hz
    mixedMoment B raw20470step1 raw20470step1Labels = mixedMoment B raw20470step2 raw20470step2Labels := by
      have ha : raw20470step2 = (fun i j => raw20470step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20470step2 raw20470step1; decide +kernel
      have hl : raw20470step2Labels = raw20470step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20470step1 raw20470step1Labels permutation8 permutation7
    mixedMoment B raw20470step2 raw20470step2Labels = mixedMoment B raw20470step3 raw20470step3Labels := by
      have ha : raw20470step3 = raw20470step2 := by apply Matrix.ext; unfold raw20470step3 raw20470step2; decide +kernel
      have hl : raw20470step2Labels = labelEmbedding1 ∘ raw20470step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20470step2 raw20470step2Labels raw20470step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1271 node1271Labels := by rfl

theorem canonical20471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20471 raw20471Labels = mixedMoment B node1271 node1271Labels := by
  calc
    mixedMoment B raw20471 raw20471Labels = mixedMoment B raw20471step0 raw20471step0Labels := by
      have hz : ∀ j, raw20471 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20471step0 = (fun i j => raw20471 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20471step0 raw20471; decide +kernel
      have hl : raw20471step0Labels = raw20471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20471 raw20471Labels permutation434 hz
    mixedMoment B raw20471step0 raw20471step0Labels = mixedMoment B raw20471step1 raw20471step1Labels := by
      have hz : ∀ j, raw20471step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20471step1 = (fun i j => raw20471step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20471step1 raw20471step0; decide +kernel
      have hl : raw20471step1Labels = raw20471step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20471step0 raw20471step0Labels permutation56 hz
    mixedMoment B raw20471step1 raw20471step1Labels = mixedMoment B raw20471step2 raw20471step2Labels := by
      have ha : raw20471step2 = (fun i j => raw20471step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20471step2 raw20471step1; decide +kernel
      have hl : raw20471step2Labels = raw20471step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20471step1 raw20471step1Labels permutation8 permutation7
    mixedMoment B raw20471step2 raw20471step2Labels = mixedMoment B raw20471step3 raw20471step3Labels := by
      have ha : raw20471step3 = raw20471step2 := by apply Matrix.ext; unfold raw20471step3 raw20471step2; decide +kernel
      have hl : raw20471step2Labels = labelEmbedding1 ∘ raw20471step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20471step2 raw20471step2Labels raw20471step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1271 node1271Labels := by rfl

theorem canonical20472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20472 raw20472Labels = mixedMoment B node1271 node1271Labels := by
  calc
    mixedMoment B raw20472 raw20472Labels = mixedMoment B raw20472step0 raw20472step0Labels := by
      have hz : ∀ j, raw20472 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20472step0 = (fun i j => raw20472 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20472step0 raw20472; decide +kernel
      have hl : raw20472step0Labels = raw20472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20472 raw20472Labels permutation346 hz
    mixedMoment B raw20472step0 raw20472step0Labels = mixedMoment B raw20472step1 raw20472step1Labels := by
      have hz : ∀ j, raw20472step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20472step1 = (fun i j => raw20472step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20472step1 raw20472step0; decide +kernel
      have hl : raw20472step1Labels = raw20472step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20472step0 raw20472step0Labels permutation56 hz
    mixedMoment B raw20472step1 raw20472step1Labels = mixedMoment B raw20472step2 raw20472step2Labels := by
      have ha : raw20472step2 = (fun i j => raw20472step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20472step2 raw20472step1; decide +kernel
      have hl : raw20472step2Labels = raw20472step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20472step1 raw20472step1Labels permutation8 permutation7
    mixedMoment B raw20472step2 raw20472step2Labels = mixedMoment B raw20472step3 raw20472step3Labels := by
      have ha : raw20472step3 = raw20472step2 := by apply Matrix.ext; unfold raw20472step3 raw20472step2; decide +kernel
      have hl : raw20472step2Labels = labelEmbedding1 ∘ raw20472step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20472step2 raw20472step2Labels raw20472step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1271 node1271Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20620 raw20620Labels = mixedMoment B node1047 node1047Labels := by
  calc
    mixedMoment B raw20620 raw20620Labels = mixedMoment B raw20620step0 raw20620step0Labels := by
      have hz : ∀ j, raw20620 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20620step0 = (fun i j => raw20620 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20620step0 raw20620; decide +kernel
      have hl : raw20620step0Labels = raw20620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20620 raw20620Labels permutation434 hz
    mixedMoment B raw20620step0 raw20620step0Labels = mixedMoment B raw20620step1 raw20620step1Labels := by
      have hz : ∀ j, raw20620step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20620step1 = (fun i j => raw20620step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20620step1 raw20620step0; decide +kernel
      have hl : raw20620step1Labels = raw20620step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20620step0 raw20620step0Labels permutation80 hz
    mixedMoment B raw20620step1 raw20620step1Labels = mixedMoment B raw20620step2 raw20620step2Labels := by
      have ha : raw20620step2 = (fun i j => raw20620step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20620step2 raw20620step1; decide +kernel
      have hl : raw20620step2Labels = raw20620step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20620step1 raw20620step1Labels permutation8 permutation7
    mixedMoment B raw20620step2 raw20620step2Labels = mixedMoment B raw20620step3 raw20620step3Labels := by
      have ha : raw20620step3 = raw20620step2 := by apply Matrix.ext; unfold raw20620step3 raw20620step2; decide +kernel
      have hl : raw20620step2Labels = labelEmbedding1 ∘ raw20620step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20620step2 raw20620step2Labels raw20620step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1047 node1047Labels := by rfl

theorem canonical20621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20621 raw20621Labels = mixedMoment B node1047 node1047Labels := by
  calc
    mixedMoment B raw20621 raw20621Labels = mixedMoment B raw20621step0 raw20621step0Labels := by
      have hz : ∀ j, raw20621 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20621step0 = (fun i j => raw20621 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20621step0 raw20621; decide +kernel
      have hl : raw20621step0Labels = raw20621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20621 raw20621Labels permutation434 hz
    mixedMoment B raw20621step0 raw20621step0Labels = mixedMoment B raw20621step1 raw20621step1Labels := by
      have hz : ∀ j, raw20621step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20621step1 = (fun i j => raw20621step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20621step1 raw20621step0; decide +kernel
      have hl : raw20621step1Labels = raw20621step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20621step0 raw20621step0Labels permutation56 hz
    mixedMoment B raw20621step1 raw20621step1Labels = mixedMoment B raw20621step2 raw20621step2Labels := by
      have ha : raw20621step2 = (fun i j => raw20621step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20621step2 raw20621step1; decide +kernel
      have hl : raw20621step2Labels = raw20621step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20621step1 raw20621step1Labels permutation8 permutation7
    mixedMoment B raw20621step2 raw20621step2Labels = mixedMoment B raw20621step3 raw20621step3Labels := by
      have ha : raw20621step3 = raw20621step2 := by apply Matrix.ext; unfold raw20621step3 raw20621step2; decide +kernel
      have hl : raw20621step2Labels = labelEmbedding1 ∘ raw20621step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20621step2 raw20621step2Labels raw20621step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1047 node1047Labels := by rfl

theorem canonical20622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20622 raw20622Labels = mixedMoment B node1047 node1047Labels := by
  calc
    mixedMoment B raw20622 raw20622Labels = mixedMoment B raw20622step0 raw20622step0Labels := by
      have hz : ∀ j, raw20622 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20622step0 = (fun i j => raw20622 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20622step0 raw20622; decide +kernel
      have hl : raw20622step0Labels = raw20622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20622 raw20622Labels permutation346 hz
    mixedMoment B raw20622step0 raw20622step0Labels = mixedMoment B raw20622step1 raw20622step1Labels := by
      have hz : ∀ j, raw20622step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20622step1 = (fun i j => raw20622step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20622step1 raw20622step0; decide +kernel
      have hl : raw20622step1Labels = raw20622step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20622step0 raw20622step0Labels permutation56 hz
    mixedMoment B raw20622step1 raw20622step1Labels = mixedMoment B raw20622step2 raw20622step2Labels := by
      have ha : raw20622step2 = (fun i j => raw20622step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20622step2 raw20622step1; decide +kernel
      have hl : raw20622step2Labels = raw20622step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20622step1 raw20622step1Labels permutation8 permutation7
    mixedMoment B raw20622step2 raw20622step2Labels = mixedMoment B raw20622step3 raw20622step3Labels := by
      have ha : raw20622step3 = raw20622step2 := by apply Matrix.ext; unfold raw20622step3 raw20622step2; decide +kernel
      have hl : raw20622step2Labels = labelEmbedding1 ∘ raw20622step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20622step2 raw20622step2Labels raw20622step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1047 node1047Labels := by rfl

theorem canonical20623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20623 raw20623Labels = mixedMoment B node1092 node1092Labels := by
  calc
    mixedMoment B raw20623 raw20623Labels = mixedMoment B raw20623step0 raw20623step0Labels := by
      have hz : ∀ j, raw20623 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20623step0 = (fun i j => raw20623 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20623step0 raw20623; decide +kernel
      have hl : raw20623step0Labels = raw20623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20623 raw20623Labels permutation434 hz
    mixedMoment B raw20623step0 raw20623step0Labels = mixedMoment B raw20623step1 raw20623step1Labels := by
      have hz : ∀ j, raw20623step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20623step1 = (fun i j => raw20623step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20623step1 raw20623step0; decide +kernel
      have hl : raw20623step1Labels = raw20623step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20623step0 raw20623step0Labels permutation80 hz
    mixedMoment B raw20623step1 raw20623step1Labels = mixedMoment B raw20623step2 raw20623step2Labels := by
      have hz : ∀ j, raw20623step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20623step2 = (fun i j => raw20623step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20623step2 raw20623step1; decide +kernel
      have hl : raw20623step2Labels = raw20623step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20623step1 raw20623step1Labels permutation14 hz
    mixedMoment B raw20623step2 raw20623step2Labels = mixedMoment B raw20623step3 raw20623step3Labels := by
      have ha : raw20623step3 = (fun i j => raw20623step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20623step3 raw20623step2; decide +kernel
      have hl : raw20623step3Labels = raw20623step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20623step2 raw20623step2Labels permutation2 permutation7
    mixedMoment B raw20623step3 raw20623step3Labels = mixedMoment B raw20623step4 raw20623step4Labels := by
      have ha : raw20623step4 = raw20623step3 := by apply Matrix.ext; unfold raw20623step4 raw20623step3; decide +kernel
      have hl : raw20623step3Labels = labelEmbedding1 ∘ raw20623step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20623step3 raw20623step3Labels raw20623step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1092 node1092Labels := by rfl

theorem canonical20624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20624 raw20624Labels = mixedMoment B node1417 node1417Labels := by
  calc
    mixedMoment B raw20624 raw20624Labels = mixedMoment B raw20624step0 raw20624step0Labels := by
      have hz : ∀ j, raw20624 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20624step0 = (fun i j => raw20624 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20624step0 raw20624; decide +kernel
      have hl : raw20624step0Labels = raw20624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20624 raw20624Labels permutation434 hz
    mixedMoment B raw20624step0 raw20624step0Labels = mixedMoment B raw20624step1 raw20624step1Labels := by
      have hz : ∀ j, raw20624step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20624step1 = (fun i j => raw20624step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20624step1 raw20624step0; decide +kernel
      have hl : raw20624step1Labels = raw20624step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20624step0 raw20624step0Labels permutation80 hz
    mixedMoment B raw20624step1 raw20624step1Labels = mixedMoment B raw20624step2 raw20624step2Labels := by
      have ha : raw20624step2 = (fun i j => raw20624step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20624step2 raw20624step1; decide +kernel
      have hl : raw20624step2Labels = raw20624step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20624step1 raw20624step1Labels permutation8 permutation7
    mixedMoment B raw20624step2 raw20624step2Labels = mixedMoment B raw20624step3 raw20624step3Labels := by
      have ha : raw20624step3 = raw20624step2 := by apply Matrix.ext; unfold raw20624step3 raw20624step2; decide +kernel
      have hl : raw20624step2Labels = labelEmbedding1 ∘ raw20624step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20624step2 raw20624step2Labels raw20624step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1417 node1417Labels := by rfl

theorem canonical20625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20625 raw20625Labels = mixedMoment B node1218 node1218Labels := by
  calc
    mixedMoment B raw20625 raw20625Labels = mixedMoment B raw20625step0 raw20625step0Labels := by
      have hz : ∀ j, raw20625 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20625step0 = (fun i j => raw20625 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20625step0 raw20625; decide +kernel
      have hl : raw20625step0Labels = raw20625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20625 raw20625Labels permutation434 hz
    mixedMoment B raw20625step0 raw20625step0Labels = mixedMoment B raw20625step1 raw20625step1Labels := by
      have ha : raw20625step1 = (fun i j => raw20625step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20625step1 raw20625step0; decide +kernel
      have hl : raw20625step1Labels = raw20625step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20625step0 raw20625step0Labels permutation32 permutation7
    mixedMoment B raw20625step1 raw20625step1Labels = mixedMoment B raw20625step2 raw20625step2Labels := by
      have ha : raw20625step2 = raw20625step1 := by apply Matrix.ext; unfold raw20625step2 raw20625step1; decide +kernel
      have hl : raw20625step1Labels = labelEmbedding1 ∘ raw20625step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20625step1 raw20625step1Labels raw20625step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1218 node1218Labels := by rfl

theorem canonical20626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20626 raw20626Labels = mixedMoment B node1218 node1218Labels := by
  calc
    mixedMoment B raw20626 raw20626Labels = mixedMoment B raw20626step0 raw20626step0Labels := by
      have hz : ∀ j, raw20626 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20626step0 = (fun i j => raw20626 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20626step0 raw20626; decide +kernel
      have hl : raw20626step0Labels = raw20626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20626 raw20626Labels permutation346 hz
    mixedMoment B raw20626step0 raw20626step0Labels = mixedMoment B raw20626step1 raw20626step1Labels := by
      have ha : raw20626step1 = (fun i j => raw20626step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20626step1 raw20626step0; decide +kernel
      have hl : raw20626step1Labels = raw20626step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20626step0 raw20626step0Labels permutation32 permutation7
    mixedMoment B raw20626step1 raw20626step1Labels = mixedMoment B raw20626step2 raw20626step2Labels := by
      have ha : raw20626step2 = raw20626step1 := by apply Matrix.ext; unfold raw20626step2 raw20626step1; decide +kernel
      have hl : raw20626step1Labels = labelEmbedding1 ∘ raw20626step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20626step1 raw20626step1Labels raw20626step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1218 node1218Labels := by rfl

theorem canonical20627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20627 raw20627Labels = mixedMoment B node1244 node1244Labels := by
  calc
    mixedMoment B raw20627 raw20627Labels = mixedMoment B raw20627step0 raw20627step0Labels := by
      have hz : ∀ j, raw20627 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20627step0 = (fun i j => raw20627 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20627step0 raw20627; decide +kernel
      have hl : raw20627step0Labels = raw20627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20627 raw20627Labels permutation434 hz
    mixedMoment B raw20627step0 raw20627step0Labels = mixedMoment B raw20627step1 raw20627step1Labels := by
      have hz : ∀ j, raw20627step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20627step1 = (fun i j => raw20627step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20627step1 raw20627step0; decide +kernel
      have hl : raw20627step1Labels = raw20627step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20627step0 raw20627step0Labels permutation80 hz
    mixedMoment B raw20627step1 raw20627step1Labels = mixedMoment B raw20627step2 raw20627step2Labels := by
      have ha : raw20627step2 = (fun i j => raw20627step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20627step2 raw20627step1; decide +kernel
      have hl : raw20627step2Labels = raw20627step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20627step1 raw20627step1Labels permutation8 permutation7
    mixedMoment B raw20627step2 raw20627step2Labels = mixedMoment B raw20627step3 raw20627step3Labels := by
      have ha : raw20627step3 = raw20627step2 := by apply Matrix.ext; unfold raw20627step3 raw20627step2; decide +kernel
      have hl : raw20627step2Labels = labelEmbedding1 ∘ raw20627step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20627step2 raw20627step2Labels raw20627step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1244 node1244Labels := by rfl

theorem canonical20628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20628 raw20628Labels = mixedMoment B node1417 node1417Labels := by
  calc
    mixedMoment B raw20628 raw20628Labels = mixedMoment B raw20628step0 raw20628step0Labels := by
      have hz : ∀ j, raw20628 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20628step0 = (fun i j => raw20628 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20628step0 raw20628; decide +kernel
      have hl : raw20628step0Labels = raw20628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20628 raw20628Labels permutation434 hz
    mixedMoment B raw20628step0 raw20628step0Labels = mixedMoment B raw20628step1 raw20628step1Labels := by
      have hz : ∀ j, raw20628step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20628step1 = (fun i j => raw20628step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20628step1 raw20628step0; decide +kernel
      have hl : raw20628step1Labels = raw20628step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20628step0 raw20628step0Labels permutation56 hz
    mixedMoment B raw20628step1 raw20628step1Labels = mixedMoment B raw20628step2 raw20628step2Labels := by
      have ha : raw20628step2 = (fun i j => raw20628step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20628step2 raw20628step1; decide +kernel
      have hl : raw20628step2Labels = raw20628step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20628step1 raw20628step1Labels permutation8 permutation7
    mixedMoment B raw20628step2 raw20628step2Labels = mixedMoment B raw20628step3 raw20628step3Labels := by
      have ha : raw20628step3 = raw20628step2 := by apply Matrix.ext; unfold raw20628step3 raw20628step2; decide +kernel
      have hl : raw20628step2Labels = labelEmbedding1 ∘ raw20628step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20628step2 raw20628step2Labels raw20628step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1417 node1417Labels := by rfl

theorem canonical20629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20629 raw20629Labels = mixedMoment B node1218 node1218Labels := by
  calc
    mixedMoment B raw20629 raw20629Labels = mixedMoment B raw20629step0 raw20629step0Labels := by
      have hz : ∀ j, raw20629 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20629step0 = (fun i j => raw20629 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20629step0 raw20629; decide +kernel
      have hl : raw20629step0Labels = raw20629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20629 raw20629Labels permutation434 hz
    mixedMoment B raw20629step0 raw20629step0Labels = mixedMoment B raw20629step1 raw20629step1Labels := by
      have ha : raw20629step1 = (fun i j => raw20629step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20629step1 raw20629step0; decide +kernel
      have hl : raw20629step1Labels = raw20629step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20629step0 raw20629step0Labels permutation38 permutation7
    mixedMoment B raw20629step1 raw20629step1Labels = mixedMoment B raw20629step2 raw20629step2Labels := by
      have ha : raw20629step2 = raw20629step1 := by apply Matrix.ext; unfold raw20629step2 raw20629step1; decide +kernel
      have hl : raw20629step1Labels = labelEmbedding1 ∘ raw20629step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20629step1 raw20629step1Labels raw20629step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1218 node1218Labels := by rfl

theorem canonical20630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20630 raw20630Labels = mixedMoment B node1218 node1218Labels := by
  calc
    mixedMoment B raw20630 raw20630Labels = mixedMoment B raw20630step0 raw20630step0Labels := by
      have hz : ∀ j, raw20630 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20630step0 = (fun i j => raw20630 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20630step0 raw20630; decide +kernel
      have hl : raw20630step0Labels = raw20630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20630 raw20630Labels permutation265 hz
    mixedMoment B raw20630step0 raw20630step0Labels = mixedMoment B raw20630step1 raw20630step1Labels := by
      have ha : raw20630step1 = (fun i j => raw20630step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20630step1 raw20630step0; decide +kernel
      have hl : raw20630step1Labels = raw20630step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20630step0 raw20630step0Labels permutation32 permutation7
    mixedMoment B raw20630step1 raw20630step1Labels = mixedMoment B raw20630step2 raw20630step2Labels := by
      have ha : raw20630step2 = raw20630step1 := by apply Matrix.ext; unfold raw20630step2 raw20630step1; decide +kernel
      have hl : raw20630step1Labels = labelEmbedding1 ∘ raw20630step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20630step1 raw20630step1Labels raw20630step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1218 node1218Labels := by rfl

theorem canonical20631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20631 raw20631Labels = mixedMoment B node1244 node1244Labels := by
  calc
    mixedMoment B raw20631 raw20631Labels = mixedMoment B raw20631step0 raw20631step0Labels := by
      have hz : ∀ j, raw20631 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20631step0 = (fun i j => raw20631 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20631step0 raw20631; decide +kernel
      have hl : raw20631step0Labels = raw20631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20631 raw20631Labels permutation434 hz
    mixedMoment B raw20631step0 raw20631step0Labels = mixedMoment B raw20631step1 raw20631step1Labels := by
      have hz : ∀ j, raw20631step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20631step1 = (fun i j => raw20631step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20631step1 raw20631step0; decide +kernel
      have hl : raw20631step1Labels = raw20631step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20631step0 raw20631step0Labels permutation56 hz
    mixedMoment B raw20631step1 raw20631step1Labels = mixedMoment B raw20631step2 raw20631step2Labels := by
      have ha : raw20631step2 = (fun i j => raw20631step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20631step2 raw20631step1; decide +kernel
      have hl : raw20631step2Labels = raw20631step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20631step1 raw20631step1Labels permutation8 permutation7
    mixedMoment B raw20631step2 raw20631step2Labels = mixedMoment B raw20631step3 raw20631step3Labels := by
      have ha : raw20631step3 = raw20631step2 := by apply Matrix.ext; unfold raw20631step3 raw20631step2; decide +kernel
      have hl : raw20631step2Labels = labelEmbedding1 ∘ raw20631step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20631step2 raw20631step2Labels raw20631step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1244 node1244Labels := by rfl

theorem canonical20632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20632 raw20632Labels = mixedMoment B node1417 node1417Labels := by
  calc
    mixedMoment B raw20632 raw20632Labels = mixedMoment B raw20632step0 raw20632step0Labels := by
      have hz : ∀ j, raw20632 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20632step0 = (fun i j => raw20632 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20632step0 raw20632; decide +kernel
      have hl : raw20632step0Labels = raw20632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20632 raw20632Labels permutation346 hz
    mixedMoment B raw20632step0 raw20632step0Labels = mixedMoment B raw20632step1 raw20632step1Labels := by
      have hz : ∀ j, raw20632step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20632step1 = (fun i j => raw20632step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20632step1 raw20632step0; decide +kernel
      have hl : raw20632step1Labels = raw20632step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20632step0 raw20632step0Labels permutation56 hz
    mixedMoment B raw20632step1 raw20632step1Labels = mixedMoment B raw20632step2 raw20632step2Labels := by
      have ha : raw20632step2 = (fun i j => raw20632step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20632step2 raw20632step1; decide +kernel
      have hl : raw20632step2Labels = raw20632step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20632step1 raw20632step1Labels permutation8 permutation7
    mixedMoment B raw20632step2 raw20632step2Labels = mixedMoment B raw20632step3 raw20632step3Labels := by
      have ha : raw20632step3 = raw20632step2 := by apply Matrix.ext; unfold raw20632step3 raw20632step2; decide +kernel
      have hl : raw20632step2Labels = labelEmbedding1 ∘ raw20632step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20632step2 raw20632step2Labels raw20632step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1417 node1417Labels := by rfl

theorem canonical20633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20633 raw20633Labels = mixedMoment B node1218 node1218Labels := by
  calc
    mixedMoment B raw20633 raw20633Labels = mixedMoment B raw20633step0 raw20633step0Labels := by
      have hz : ∀ j, raw20633 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20633step0 = (fun i j => raw20633 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20633step0 raw20633; decide +kernel
      have hl : raw20633step0Labels = raw20633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20633 raw20633Labels permutation346 hz
    mixedMoment B raw20633step0 raw20633step0Labels = mixedMoment B raw20633step1 raw20633step1Labels := by
      have ha : raw20633step1 = (fun i j => raw20633step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20633step1 raw20633step0; decide +kernel
      have hl : raw20633step1Labels = raw20633step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20633step0 raw20633step0Labels permutation38 permutation7
    mixedMoment B raw20633step1 raw20633step1Labels = mixedMoment B raw20633step2 raw20633step2Labels := by
      have ha : raw20633step2 = raw20633step1 := by apply Matrix.ext; unfold raw20633step2 raw20633step1; decide +kernel
      have hl : raw20633step1Labels = labelEmbedding1 ∘ raw20633step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20633step1 raw20633step1Labels raw20633step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1218 node1218Labels := by rfl

theorem canonical20634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20634 raw20634Labels = mixedMoment B node1218 node1218Labels := by
  calc
    mixedMoment B raw20634 raw20634Labels = mixedMoment B raw20634step0 raw20634step0Labels := by
      have hz : ∀ j, raw20634 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20634step0 = (fun i j => raw20634 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20634step0 raw20634; decide +kernel
      have hl : raw20634step0Labels = raw20634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20634 raw20634Labels permutation265 hz
    mixedMoment B raw20634step0 raw20634step0Labels = mixedMoment B raw20634step1 raw20634step1Labels := by
      have ha : raw20634step1 = (fun i j => raw20634step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20634step1 raw20634step0; decide +kernel
      have hl : raw20634step1Labels = raw20634step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20634step0 raw20634step0Labels permutation38 permutation7
    mixedMoment B raw20634step1 raw20634step1Labels = mixedMoment B raw20634step2 raw20634step2Labels := by
      have ha : raw20634step2 = raw20634step1 := by apply Matrix.ext; unfold raw20634step2 raw20634step1; decide +kernel
      have hl : raw20634step1Labels = labelEmbedding1 ∘ raw20634step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20634step1 raw20634step1Labels raw20634step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1218 node1218Labels := by rfl

theorem canonical20635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20635 raw20635Labels = mixedMoment B node1244 node1244Labels := by
  calc
    mixedMoment B raw20635 raw20635Labels = mixedMoment B raw20635step0 raw20635step0Labels := by
      have hz : ∀ j, raw20635 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20635step0 = (fun i j => raw20635 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20635step0 raw20635; decide +kernel
      have hl : raw20635step0Labels = raw20635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20635 raw20635Labels permutation346 hz
    mixedMoment B raw20635step0 raw20635step0Labels = mixedMoment B raw20635step1 raw20635step1Labels := by
      have hz : ∀ j, raw20635step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20635step1 = (fun i j => raw20635step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20635step1 raw20635step0; decide +kernel
      have hl : raw20635step1Labels = raw20635step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20635step0 raw20635step0Labels permutation56 hz
    mixedMoment B raw20635step1 raw20635step1Labels = mixedMoment B raw20635step2 raw20635step2Labels := by
      have ha : raw20635step2 = (fun i j => raw20635step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20635step2 raw20635step1; decide +kernel
      have hl : raw20635step2Labels = raw20635step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20635step1 raw20635step1Labels permutation8 permutation7
    mixedMoment B raw20635step2 raw20635step2Labels = mixedMoment B raw20635step3 raw20635step3Labels := by
      have ha : raw20635step3 = raw20635step2 := by apply Matrix.ext; unfold raw20635step3 raw20635step2; decide +kernel
      have hl : raw20635step2Labels = labelEmbedding1 ∘ raw20635step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20635step2 raw20635step2Labels raw20635step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1244 node1244Labels := by rfl

theorem canonical20636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20636 raw20636Labels = mixedMoment B node1307 node1307Labels := by
  calc
    mixedMoment B raw20636 raw20636Labels = mixedMoment B raw20636step0 raw20636step0Labels := by
      have hz : ∀ j, raw20636 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20636step0 = (fun i j => raw20636 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20636step0 raw20636; decide +kernel
      have hl : raw20636step0Labels = raw20636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20636 raw20636Labels permutation434 hz
    mixedMoment B raw20636step0 raw20636step0Labels = mixedMoment B raw20636step1 raw20636step1Labels := by
      have hz : ∀ j, raw20636step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20636step1 = (fun i j => raw20636step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20636step1 raw20636step0; decide +kernel
      have hl : raw20636step1Labels = raw20636step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20636step0 raw20636step0Labels permutation80 hz
    mixedMoment B raw20636step1 raw20636step1Labels = mixedMoment B raw20636step2 raw20636step2Labels := by
      have hz : ∀ j, raw20636step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20636step2 = (fun i j => raw20636step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20636step2 raw20636step1; decide +kernel
      have hl : raw20636step2Labels = raw20636step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20636step1 raw20636step1Labels permutation14 hz
    mixedMoment B raw20636step2 raw20636step2Labels = mixedMoment B raw20636step3 raw20636step3Labels := by
      have ha : raw20636step3 = (fun i j => raw20636step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20636step3 raw20636step2; decide +kernel
      have hl : raw20636step3Labels = raw20636step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20636step2 raw20636step2Labels permutation2 permutation7
    mixedMoment B raw20636step3 raw20636step3Labels = mixedMoment B raw20636step4 raw20636step4Labels := by
      have ha : raw20636step4 = raw20636step3 := by apply Matrix.ext; unfold raw20636step4 raw20636step3; decide +kernel
      have hl : raw20636step3Labels = labelEmbedding1 ∘ raw20636step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20636step3 raw20636step3Labels raw20636step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1307 node1307Labels := by rfl

theorem canonical20637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20637 raw20637Labels = mixedMoment B node1453 node1453Labels := by
  calc
    mixedMoment B raw20637 raw20637Labels = mixedMoment B raw20637step0 raw20637step0Labels := by
      have hz : ∀ j, raw20637 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20637step0 = (fun i j => raw20637 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20637step0 raw20637; decide +kernel
      have hl : raw20637step0Labels = raw20637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20637 raw20637Labels permutation434 hz
    mixedMoment B raw20637step0 raw20637step0Labels = mixedMoment B raw20637step1 raw20637step1Labels := by
      have hz : ∀ j, raw20637step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20637step1 = (fun i j => raw20637step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20637step1 raw20637step0; decide +kernel
      have hl : raw20637step1Labels = raw20637step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20637step0 raw20637step0Labels permutation80 hz
    mixedMoment B raw20637step1 raw20637step1Labels = mixedMoment B raw20637step2 raw20637step2Labels := by
      have hz : ∀ j, raw20637step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20637step2 = (fun i j => raw20637step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20637step2 raw20637step1; decide +kernel
      have hl : raw20637step2Labels = raw20637step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20637step1 raw20637step1Labels permutation14 hz
    mixedMoment B raw20637step2 raw20637step2Labels = mixedMoment B raw20637step3 raw20637step3Labels := by
      have ha : raw20637step3 = (fun i j => raw20637step2 (permutation7 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20637step3 raw20637step2; decide +kernel
      have hl : raw20637step3Labels = raw20637step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20637step2 raw20637step2Labels permutation7 permutation5
    mixedMoment B raw20637step3 raw20637step3Labels = mixedMoment B raw20637step4 raw20637step4Labels := by
      have ha : raw20637step4 = raw20637step3 := by apply Matrix.ext; unfold raw20637step4 raw20637step3; decide +kernel
      have hl : raw20637step3Labels = labelEmbedding1 ∘ raw20637step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20637step3 raw20637step3Labels raw20637step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1453 node1453Labels := by rfl

theorem canonical20638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20638 raw20638Labels = mixedMoment B node1272 node1272Labels := by
  calc
    mixedMoment B raw20638 raw20638Labels = mixedMoment B raw20638step0 raw20638step0Labels := by
      have hz : ∀ j, raw20638 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20638step0 = (fun i j => raw20638 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20638step0 raw20638; decide +kernel
      have hl : raw20638step0Labels = raw20638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20638 raw20638Labels permutation434 hz
    mixedMoment B raw20638step0 raw20638step0Labels = mixedMoment B raw20638step1 raw20638step1Labels := by
      have hz : ∀ j, raw20638step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20638step1 = (fun i j => raw20638step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20638step1 raw20638step0; decide +kernel
      have hl : raw20638step1Labels = raw20638step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20638step0 raw20638step0Labels permutation80 hz
    mixedMoment B raw20638step1 raw20638step1Labels = mixedMoment B raw20638step2 raw20638step2Labels := by
      have ha : raw20638step2 = (fun i j => raw20638step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20638step2 raw20638step1; decide +kernel
      have hl : raw20638step2Labels = raw20638step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20638step1 raw20638step1Labels permutation8 permutation7
    mixedMoment B raw20638step2 raw20638step2Labels = mixedMoment B raw20638step3 raw20638step3Labels := by
      have ha : raw20638step3 = raw20638step2 := by apply Matrix.ext; unfold raw20638step3 raw20638step2; decide +kernel
      have hl : raw20638step2Labels = labelEmbedding1 ∘ raw20638step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20638step2 raw20638step2Labels raw20638step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1272 node1272Labels := by rfl

theorem canonical20639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20639 raw20639Labels = mixedMoment B node1272 node1272Labels := by
  calc
    mixedMoment B raw20639 raw20639Labels = mixedMoment B raw20639step0 raw20639step0Labels := by
      have hz : ∀ j, raw20639 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20639step0 = (fun i j => raw20639 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20639step0 raw20639; decide +kernel
      have hl : raw20639step0Labels = raw20639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20639 raw20639Labels permutation434 hz
    mixedMoment B raw20639step0 raw20639step0Labels = mixedMoment B raw20639step1 raw20639step1Labels := by
      have hz : ∀ j, raw20639step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20639step1 = (fun i j => raw20639step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20639step1 raw20639step0; decide +kernel
      have hl : raw20639step1Labels = raw20639step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20639step0 raw20639step0Labels permutation56 hz
    mixedMoment B raw20639step1 raw20639step1Labels = mixedMoment B raw20639step2 raw20639step2Labels := by
      have ha : raw20639step2 = (fun i j => raw20639step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20639step2 raw20639step1; decide +kernel
      have hl : raw20639step2Labels = raw20639step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20639step1 raw20639step1Labels permutation8 permutation7
    mixedMoment B raw20639step2 raw20639step2Labels = mixedMoment B raw20639step3 raw20639step3Labels := by
      have ha : raw20639step3 = raw20639step2 := by apply Matrix.ext; unfold raw20639step3 raw20639step2; decide +kernel
      have hl : raw20639step2Labels = labelEmbedding1 ∘ raw20639step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20639step2 raw20639step2Labels raw20639step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1272 node1272Labels := by rfl

theorem canonical20640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20640 raw20640Labels = mixedMoment B node1272 node1272Labels := by
  calc
    mixedMoment B raw20640 raw20640Labels = mixedMoment B raw20640step0 raw20640step0Labels := by
      have hz : ∀ j, raw20640 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20640step0 = (fun i j => raw20640 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20640step0 raw20640; decide +kernel
      have hl : raw20640step0Labels = raw20640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20640 raw20640Labels permutation346 hz
    mixedMoment B raw20640step0 raw20640step0Labels = mixedMoment B raw20640step1 raw20640step1Labels := by
      have hz : ∀ j, raw20640step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20640step1 = (fun i j => raw20640step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20640step1 raw20640step0; decide +kernel
      have hl : raw20640step1Labels = raw20640step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20640step0 raw20640step0Labels permutation56 hz
    mixedMoment B raw20640step1 raw20640step1Labels = mixedMoment B raw20640step2 raw20640step2Labels := by
      have ha : raw20640step2 = (fun i j => raw20640step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20640step2 raw20640step1; decide +kernel
      have hl : raw20640step2Labels = raw20640step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20640step1 raw20640step1Labels permutation8 permutation7
    mixedMoment B raw20640step2 raw20640step2Labels = mixedMoment B raw20640step3 raw20640step3Labels := by
      have ha : raw20640step3 = raw20640step2 := by apply Matrix.ext; unfold raw20640step3 raw20640step2; decide +kernel
      have hl : raw20640step2Labels = labelEmbedding1 ∘ raw20640step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20640step2 raw20640step2Labels raw20640step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1272 node1272Labels := by rfl

theorem canonical20641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20641 raw20641Labels = mixedMoment B node1309 node1309Labels := by
  calc
    mixedMoment B raw20641 raw20641Labels = mixedMoment B raw20641step0 raw20641step0Labels := by
      have hz : ∀ j, raw20641 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20641step0 = (fun i j => raw20641 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20641step0 raw20641; decide +kernel
      have hl : raw20641step0Labels = raw20641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20641 raw20641Labels permutation434 hz
    mixedMoment B raw20641step0 raw20641step0Labels = mixedMoment B raw20641step1 raw20641step1Labels := by
      have hz : ∀ j, raw20641step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20641step1 = (fun i j => raw20641step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20641step1 raw20641step0; decide +kernel
      have hl : raw20641step1Labels = raw20641step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20641step0 raw20641step0Labels permutation80 hz
    mixedMoment B raw20641step1 raw20641step1Labels = mixedMoment B raw20641step2 raw20641step2Labels := by
      have hz : ∀ j, raw20641step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20641step2 = (fun i j => raw20641step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20641step2 raw20641step1; decide +kernel
      have hl : raw20641step2Labels = raw20641step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20641step1 raw20641step1Labels permutation14 hz
    mixedMoment B raw20641step2 raw20641step2Labels = mixedMoment B raw20641step3 raw20641step3Labels := by
      have ha : raw20641step3 = (fun i j => raw20641step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20641step3 raw20641step2; decide +kernel
      have hl : raw20641step3Labels = raw20641step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20641step2 raw20641step2Labels permutation2 permutation7
    mixedMoment B raw20641step3 raw20641step3Labels = mixedMoment B raw20641step4 raw20641step4Labels := by
      have ha : raw20641step4 = raw20641step3 := by apply Matrix.ext; unfold raw20641step4 raw20641step3; decide +kernel
      have hl : raw20641step3Labels = labelEmbedding1 ∘ raw20641step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20641step3 raw20641step3Labels raw20641step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1309 node1309Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical240
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7685 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7685 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7685 = injectiveMoment H raw7685step0 := by
      have hz : ∀ j, raw7685 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7685step0 = (fun i j => raw7685 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7685 permutation27 hz
    injectiveMoment H raw7685step0 = injectiveMoment H raw7685step1 := by
      have heq : raw7685step1 = (fun i j => raw7685step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7685step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

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

theorem canonical903 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw903 = injectiveMoment H node24 := by
  calc
    injectiveMoment H raw903 = injectiveMoment H raw903step0 := by
      have heq : raw903step0 = (fun i j => raw903 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw903 permutation11 permutation1
    _ = injectiveMoment H node24 := by rfl

theorem canonical917 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw917 = injectiveMoment H node10 := by
  rfl

theorem canonical926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw926 = injectiveMoment H node3 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical108 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw108 = injectiveMoment H node221 := by
  calc
    injectiveMoment H raw108 = injectiveMoment H raw108step0 := by
      have heq : raw108step0 = (fun i j => raw108 (permutation26 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw108 permutation26 permutation6
    _ = injectiveMoment H node221 := by rfl

theorem canonical125 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw125 = injectiveMoment H node42 := by
  calc
    injectiveMoment H raw125 = injectiveMoment H raw125step0 := by
      have heq : raw125step0 = (fun i j => raw125 (permutation5 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw125 permutation5 permutation5
    _ = injectiveMoment H node42 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical198 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw198 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw198 = injectiveMoment H raw198step0 := by
      have hz : ∀ j, raw198 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw198step0 = (fun i j => raw198 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw198 permutation15 hz
    _ = injectiveMoment H node8 := by rfl

theorem canonical211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw211 = injectiveMoment H node8 := by
  rfl

theorem canonical215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw215 = injectiveMoment H node2 := by
  rfl

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

theorem canonical5210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5210 = injectiveMoment H node4 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical173
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5550 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5550 = injectiveMoment H node53 := by
  rfl

theorem canonical5556 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5556 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw5556 = injectiveMoment H raw5556step0 := by
      have heq : raw5556step0 = raw5556.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5556).symm
    injectiveMoment H raw5556step0 = injectiveMoment H raw5556step1 := by
      have heq : raw5556step1 = (fun i j => raw5556step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5556step0 permutation7 permutation2
    _ = injectiveMoment H node8 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical841 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw841 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw841 = injectiveMoment H raw841step0 := by
      have heq : raw841step0 = raw841.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw841).symm
    injectiveMoment H raw841step0 = injectiveMoment H raw841step1 := by
      have heq : raw841step1 = (fun i j => raw841step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw841step0 permutation4 permutation1
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical161 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw161 = injectiveMoment H node155 := by
  calc
    injectiveMoment H raw161 = injectiveMoment H raw161step0 := by
      have heq : raw161step0 = -raw161 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw161).symm
    injectiveMoment H raw161step0 = injectiveMoment H raw161step1 := by
      have heq : raw161step1 = (fun i j => raw161step0 (permutation13 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw161step0 permutation13 permutation6
    _ = injectiveMoment H node155 := by rfl

theorem canonical176 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw176 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw176 = injectiveMoment H raw176step0 := by
      have heq : raw176step0 = raw176.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw176).symm
    injectiveMoment H raw176step0 = injectiveMoment H raw176step1 := by
      have heq : raw176step1 = -raw176step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw176step0).symm
    injectiveMoment H raw176step1 = injectiveMoment H raw176step2 := by
      have heq : raw176step2 = (fun i j => raw176step1 (permutation4 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw176step1 permutation4 permutation6
    _ = injectiveMoment H node52 := by rfl

theorem canonical180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw180 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw180 = injectiveMoment H raw180step0 := by
      have heq : raw180step0 = raw180.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw180).symm
    _ = injectiveMoment H node9 := by rfl

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

theorem sound2 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node2 = Sparse.eval value2 (momentVector H) := by
  have hc : momentVector H 6 = injectiveMoment H node2 := rfl
  simp [value2, Sparse.eval, hc]

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

theorem sound8 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node8 = Sparse.eval value8 (momentVector H) := by
  have heq : pivotMatrix8 = (fun u v => node8 (pivotPermutation8 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node8 = injectiveMoment H pivotMatrix8 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix8 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix8 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix8 (0 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix8 (0 : Fin 2) = raw926 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical926 hH).trans (sound3 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix8 (1 : Fin 2)) =
      Sparse.eval value2 (momentVector H) := by
    have heq : mergeFirst pivotMatrix8 (1 : Fin 2) = raw215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical215 hH).trans (sound2 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node8 + (injectiveMoment H (mergeFirst pivotMatrix8 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix8 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value8, value2, value3, Sparse.eval] at hc ⊢
  linarith

theorem sound9 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node9 = Sparse.eval value9 (momentVector H) := by
  have hc : momentVector H 5 = injectiveMoment H node9 := rfl
  simp [value9, Sparse.eval, hc]

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

theorem sound24 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node24 = Sparse.eval value24 (momentVector H) := by
  have heq : pivotMatrix24 = (fun u v => node24 (pivotPermutation24 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node24 = injectiveMoment H pivotMatrix24 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix24 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix24 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix24 (0 : Fin 3)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix24 (0 : Fin 3) = raw211 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical211 hH).trans (sound8 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix24 (1 : Fin 3)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix24 (1 : Fin 3) = raw900 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical900 hH).trans (sound3 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix24 (2 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix24 (2 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node24 + (injectiveMoment H (mergeFirst pivotMatrix24 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix24 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix24 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value24, value10, value3, value8, Sparse.eval] at hc ⊢
  linarith

theorem sound32 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node32 = Sparse.eval value32 (momentVector H) := by
  have hc : momentVector H 35 = injectiveMoment H node32 := rfl
  simp [value32, Sparse.eval, hc]

theorem sound42 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node42 = Sparse.eval value42 (momentVector H) := by
  have hc : momentVector H 11 = injectiveMoment H node42 := rfl
  simp [value42, Sparse.eval, hc]

theorem sound52 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node52 = Sparse.eval value52 (momentVector H) := by
  have heq : pivotMatrix52 = (fun u v => node52.transpose (pivotPermutation52 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node52 = injectiveMoment H pivotMatrix52 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix52 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix52 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix52 (0 : Fin 2)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix52 (0 : Fin 2) = raw180 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical180 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix52 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix52 (1 : Fin 2) = raw841 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical841 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node52 + (injectiveMoment H (mergeFirst pivotMatrix52 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix52 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value52, value10, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound53 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node53 = Sparse.eval value53 (momentVector H) := by
  have heq : pivotMatrix53 = (fun u v => node53 (pivotPermutation53 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node53 = injectiveMoment H pivotMatrix53 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix53 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix53 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix53 (0 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix53 (0 : Fin 2) = raw8005 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8005 hH).trans (sound3 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix53 (1 : Fin 2)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix53 (1 : Fin 2) = raw5556 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5556 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node53 + (injectiveMoment H (mergeFirst pivotMatrix53 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix53 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value53, value3, value8, Sparse.eval] at hc ⊢
  linarith

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

theorem canonical873 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw873 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw873 = injectiveMoment H raw873step0 := by
      have heq : raw873step0 = (fun i j => raw873 (permutation8 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw873 permutation8 permutation2
    _ = injectiveMoment H node8 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1439 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1439 = injectiveMoment H node32 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1450 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1450 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1450 = injectiveMoment H raw1450step0 := by
      have heq : raw1450step0 = raw1450.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1450).symm
    injectiveMoment H raw1450step0 = injectiveMoment H raw1450step1 := by
      have heq : raw1450step1 = (fun i j => raw1450step0 (permutation8 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1450step0 permutation8 permutation8
    _ = injectiveMoment H node52 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical153
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4908 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4908 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw4908 = injectiveMoment H raw4908step0 := by
      have heq : raw4908step0 = -raw4908 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4908).symm
    injectiveMoment H raw4908step0 = injectiveMoment H raw4908step1 := by
      have heq : raw4908step1 = (fun i j => raw4908step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4908step0 permutation8 permutation3
    _ = injectiveMoment H node32 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4963 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4963 = injectiveMoment H node42 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical231
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7408 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7408 = injectiveMoment H node53 := by
  calc
    injectiveMoment H raw7408 = injectiveMoment H raw7408step0 := by
      have heq : raw7408step0 = -raw7408 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7408).symm
    injectiveMoment H raw7408step0 = injectiveMoment H raw7408step1 := by
      have heq : raw7408step1 = (fun i j => raw7408step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7408step0 permutation8 permutation3
    _ = injectiveMoment H node53 := by rfl

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

theorem sound155 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node155 = Sparse.eval value155 (momentVector H) := by
  have heq : pivotMatrix155 = (fun u v => node155 (pivotPermutation155 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node155 = injectiveMoment H pivotMatrix155 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix155 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix155 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix155 (0 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix155 (0 : Fin 3) = raw5550 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5550 hH).trans (sound53 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix155 (1 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix155 (1 : Fin 3) = raw1450 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1450 hH).trans (sound52 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix155 (2 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix155 (2 : Fin 3) = raw1439 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1439 hH).trans (sound32 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node155 + (injectiveMoment H (mergeFirst pivotMatrix155 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix155 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix155 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value155, value32, value52, value53, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5132 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5132 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5132 = injectiveMoment H raw5132step0 := by
      have hz : ∀ j, raw5132 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5132step0 = (fun i j => raw5132 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5132 permutation21 hz
    injectiveMoment H raw5132step0 = injectiveMoment H raw5132step1 := by
      have heq : raw5132step1 = (fun i j => raw5132step0 (permutation8 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5132step0 permutation8 permutation2
    _ = injectiveMoment H node10 := by rfl

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

theorem sound221 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node221 = Sparse.eval value221 (momentVector H) := by
  have heq : pivotMatrix221 = (fun u v => node221 (pivotPermutation221 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node221 = injectiveMoment H pivotMatrix221 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix221 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix221 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix221 (0 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix221 (0 : Fin 3) = raw7408 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7408 hH).trans (sound53 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix221 (1 : Fin 3)) =
      Sparse.eval value42 (momentVector H) := by
    have heq : mergeFirst pivotMatrix221 (1 : Fin 3) = raw4963 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4963 hH).trans (sound42 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix221 (2 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix221 (2 : Fin 3) = raw4908 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4908 hH).trans (sound32 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node221 + (injectiveMoment H (mergeFirst pivotMatrix221 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix221 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix221 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value221, value32, value42, value53, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical242
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7749 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7749 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7749 = injectiveMoment H raw7749step0 := by
      have heq : raw7749step0 = (fun i j => raw7749 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7749 permutation5 permutation2
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair90 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node90 node90Labels = Sparse.eval singlePairValue90 (familyPairVector B) := by
  have hp := single_label_three B hB node90
  have hl : node90Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node90 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node90 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node90 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node90 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node90 (EqualityPatterns.family3.label 1) = PairSemantics.raw903 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node90 PairSemantics.raw903; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical903 hH).trans (PairSemantics.sound24 hH)
  have hm2 : familyPairMoment B (groupedColumns node90 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node90 (EqualityPatterns.family3.label 2) = PairSemantics.raw7685 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node90 PairSemantics.raw7685; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7685 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node90 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node90 (EqualityPatterns.family3.label 3) = PairSemantics.raw198 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node90 PairSemantics.raw198; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical198 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node90 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value221 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node90 (EqualityPatterns.family3.label 4) = PairSemantics.raw108 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node90 PairSemantics.raw108; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical108 hH).trans (PairSemantics.sound221 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue90, PairSemantics.value0, PairSemantics.value8, PairSemantics.value11, PairSemantics.value24, PairSemantics.value221, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair107 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node107 node107Labels = Sparse.eval singlePairValue107 (familyPairVector B) := by
  have hp := single_label_three B hB node107
  have hl : node107Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node107 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node107 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node107 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node107 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node107 (EqualityPatterns.family3.label 1) = PairSemantics.raw873 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node107 PairSemantics.raw873; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical873 hH).trans (PairSemantics.sound8 hH)
  have hm2 : familyPairMoment B (groupedColumns node107 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node107 (EqualityPatterns.family3.label 2) = PairSemantics.raw7749 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node107 PairSemantics.raw7749; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7749 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node107 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node107 (EqualityPatterns.family3.label 3) = PairSemantics.raw211 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node107 PairSemantics.raw211; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical211 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node107 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value42 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node107 (EqualityPatterns.family3.label 4) = PairSemantics.raw125 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node107 PairSemantics.raw125; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical125 hH).trans (PairSemantics.sound42 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue107, PairSemantics.value0, PairSemantics.value8, PairSemantics.value11, PairSemantics.value42, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair143 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node143 node143Labels = Sparse.eval singlePairValue143 (familyPairVector B) := by
  have hp := single_label_three B hB node143
  have hl : node143Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node143 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node143 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node143 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node143 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node143 (EqualityPatterns.family3.label 1) = PairSemantics.raw5132 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node143 PairSemantics.raw5132
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5132 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node143 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node143 (EqualityPatterns.family3.label 2) = PairSemantics.raw5204 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node143 PairSemantics.raw5204
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5204 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node143 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node143 (EqualityPatterns.family3.label 3) = PairSemantics.raw198 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node143 PairSemantics.raw198
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical198 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node143 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value155 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node143 (EqualityPatterns.family3.label 4) = PairSemantics.raw161 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node143 PairSemantics.raw161
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical161 hH).trans (PairSemantics.sound155 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue143, PairSemantics.value0, PairSemantics.value8, PairSemantics.value10, PairSemantics.value11, PairSemantics.value155, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair158 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node158 node158Labels = Sparse.eval singlePairValue158 (familyPairVector B) := by
  have hp := single_label_three B hB node158
  have hl : node158Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node158 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node158 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node158 PairSemantics.raw7979
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node158 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node158 (EqualityPatterns.family3.label 1) = PairSemantics.raw5183 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node158 PairSemantics.raw5183
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5183 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node158 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node158 (EqualityPatterns.family3.label 2) = PairSemantics.raw5199 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node158 PairSemantics.raw5199
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5199 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node158 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node158 (EqualityPatterns.family3.label 3) = PairSemantics.raw211 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node158 PairSemantics.raw211
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical211 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node158 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value52 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node158 (EqualityPatterns.family3.label 4) = PairSemantics.raw176 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node158 PairSemantics.raw176
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical176 hH).trans (PairSemantics.sound52 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue158, PairSemantics.value0, PairSemantics.value4, PairSemantics.value8, PairSemantics.value11, PairSemantics.value52, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton1271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1271 node1271Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node143 node143Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw60 singletonSmall1271
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1271) = raw60Labels := by decide +kernel
  rw [hl, canonical60 B hB] at h
  have hc0 : mixedMoment B raw60 (Fin.cases (0 : Fin 1) singletonSmall1271) =
      mixedMoment B node143 node143Labels := by
    have ha : raw60 = raw61 := by apply Matrix.ext; unfold raw60 raw61; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1271 = raw61Labels := by decide +kernel
    rw [ha, hj, canonical61 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton1307 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1307 node1307Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node158 node158Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw86 singletonSmall1307
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1307) = raw86Labels := by decide +kernel
  rw [hl, canonical86 B hB] at h
  have hc0 : mixedMoment B raw86 (Fin.cases (0 : Fin 1) singletonSmall1307) =
      mixedMoment B node158 node158Labels := by
    have ha : raw86 = raw87 := by apply Matrix.ext; unfold raw86 raw87; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1307 = raw87Labels := by decide +kernel
    rw [ha, hj, canonical87 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton1417 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1417 node1417Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node90 node90Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw138 singletonSmall1417
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1417) = raw138Labels := by decide +kernel
  rw [hl, canonical138 B hB] at h
  have hc0 : mixedMoment B raw138 (Fin.cases (0 : Fin 1) singletonSmall1417) =
      mixedMoment B node90 node90Labels := by
    have ha : raw138 = raw139 := by apply Matrix.ext; unfold raw138 raw139; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1417 = raw139Labels := by decide +kernel
    rw [ha, hj, canonical139 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton1453 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1453 node1453Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node107 node107Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw166 singletonSmall1453
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1453) = raw166Labels := by decide +kernel
  rw [hl, canonical166 B hB] at h
  have hc0 : mixedMoment B raw166 (Fin.cases (0 : Fin 1) singletonSmall1453) =
      mixedMoment B node107 node107Labels := by
    have ha : raw166 = raw167 := by apply Matrix.ext; unfold raw166 raw167; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1453 = raw167Labels := by decide +kernel
    rw [ha, hj, canonical167 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound90 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node90 node90Labels = Sparse.eval nodeValue90 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue90 (familyPairVector B) := singlePair90 B _hB
    _ = _ := by norm_num [singlePairValue90, nodeValue90, Sparse.eval, mixedVector] <;> ring

theorem sound107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node107 node107Labels = Sparse.eval nodeValue107 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue107 (familyPairVector B) := singlePair107 B _hB
    _ = _ := by norm_num [singlePairValue107, nodeValue107, Sparse.eval, mixedVector] <;> ring

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

theorem sound1047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1047 node1047Labels = Sparse.eval nodeValue1047 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1047) = mixedMoment B node1047 node1047Labels := rfl
  simpa [nodeValue1047, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1091 node1091Labels = Sparse.eval nodeValue1091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1091) = mixedMoment B node1091 node1091Labels := rfl
  simpa [nodeValue1091, Sparse.eval] using hc.symm

theorem sound1092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1092 node1092Labels = Sparse.eval nodeValue1092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1092) = mixedMoment B node1092 node1092Labels := rfl
  simpa [nodeValue1092, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node143 node143Labels = Sparse.eval nodeValue143 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue143 (familyPairVector B) := singlePair143 B _hB
    _ = _ := by
      norm_num [singlePairValue143, nodeValue143, Sparse.eval, mixedVector]
      ring

theorem sound158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node158 node158Labels = Sparse.eval nodeValue158 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue158 (familyPairVector B) := singlePair158 B _hB
    _ = _ := by
      norm_num [singlePairValue158, nodeValue158, Sparse.eval, mixedVector]
      ring

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1218 node1218Labels = Sparse.eval nodeValue1218 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1218) = mixedMoment B node1218 node1218Labels := rfl
  simpa [nodeValue1218, Sparse.eval] using hc.symm

theorem sound1243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1243 node1243Labels = Sparse.eval nodeValue1243 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1243) = mixedMoment B node1243 node1243Labels := rfl
  simpa [nodeValue1243, Sparse.eval] using hc.symm

theorem sound1244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1244 node1244Labels = Sparse.eval nodeValue1244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1244) = mixedMoment B node1244 node1244Labels := rfl
  simpa [nodeValue1244, Sparse.eval] using hc.symm

theorem sound1271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1271 node1271Labels = Sparse.eval nodeValue1271 (mixedVector B) := by
  have h := singleton1271 B _hB
  rw [sound143 B _hB _hF] at h
  norm_num [nodeValue1271, nodeValue143, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1272 node1272Labels = Sparse.eval nodeValue1272 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1272) = mixedMoment B node1272 node1272Labels := rfl
  simpa [nodeValue1272, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1307 node1307Labels = Sparse.eval nodeValue1307 (mixedVector B) := by
  have h := singleton1307 B _hB
  rw [sound158 B _hB _hF] at h
  norm_num [nodeValue1307, nodeValue158, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1309 node1309Labels = Sparse.eval nodeValue1309 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1309) = mixedMoment B node1309 node1309Labels := rfl
  simpa [nodeValue1309, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1452 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1452 node1452Labels = 0 := by
  exact mixedMoment_order_one B hB node1452 node1452Labels 2
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1417 node1417Labels = Sparse.eval nodeValue1417 (mixedVector B) := by
  have h := singleton1417 B _hB
  rw [sound90 B _hB _hF] at h
  norm_num [nodeValue1417, nodeValue90, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1452 node1452Labels = Sparse.eval nodeValue1452 (mixedVector B) := by
  simpa only [nodeValue1452, Sparse.eval_nil] using zero1452 B _hB _hF

theorem sound1453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1453 node1453Labels = Sparse.eval nodeValue1453 (mixedVector B) := by
  have h := singleton1453 B _hB
  rw [sound107 B _hB _hF] at h
  norm_num [nodeValue1453, nodeValue107, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources40
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1282 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1282 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1282 + difference 0 1) (sourceB1282 + difference 1 0) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1047) := by
    have ha : (tripleCharges (sourceA1282 + difference 0 1) (sourceB1282 + difference 1 0) sourceC1282) = raw20620 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20620; decide +kernel
    rw [ha]
    exact (canonical20620 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1282 + difference 0 2) (sourceB1282 + difference 2 0) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1047) := by
    have ha : (tripleCharges (sourceA1282 + difference 0 2) (sourceB1282 + difference 2 0) sourceC1282) = raw20621 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20621; decide +kernel
    rw [ha]
    exact (canonical20621 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1282 + difference 0 3) (sourceB1282 + difference 3 0) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1047) := by
    have ha : (tripleCharges (sourceA1282 + difference 0 3) (sourceB1282 + difference 3 0) sourceC1282) = raw20622 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20622; decide +kernel
    rw [ha]
    exact (canonical20622 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1282 + difference 0 4) (sourceB1282 + difference 4 0) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1092) := by
    have ha : (tripleCharges (sourceA1282 + difference 0 4) (sourceB1282 + difference 4 0) sourceC1282) = raw20623 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20623; decide +kernel
    rw [ha]
    exact (canonical20623 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1282 + difference 0 5) (sourceB1282 + difference 5 0) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1091) := by
    have ha : (tripleCharges (sourceA1282 + difference 0 5) (sourceB1282 + difference 5 0) sourceC1282) = raw20447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20447; decide +kernel
    rw [ha]
    exact (canonical20447 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1282 + difference 1 0) (sourceB1282 + difference 0 1) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1417) := by
    have ha : (tripleCharges (sourceA1282 + difference 1 0) (sourceB1282 + difference 0 1) sourceC1282) = raw20624 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20624; decide +kernel
    rw [ha]
    exact (canonical20624 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1282 + difference 1 2) (sourceB1282 + difference 2 1) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1218) := by
    have ha : (tripleCharges (sourceA1282 + difference 1 2) (sourceB1282 + difference 2 1) sourceC1282) = raw20625 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20625; decide +kernel
    rw [ha]
    exact (canonical20625 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1282 + difference 1 3) (sourceB1282 + difference 3 1) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1218) := by
    have ha : (tripleCharges (sourceA1282 + difference 1 3) (sourceB1282 + difference 3 1) sourceC1282) = raw20626 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20626; decide +kernel
    rw [ha]
    exact (canonical20626 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1282 + difference 1 4) (sourceB1282 + difference 4 1) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1244) := by
    have ha : (tripleCharges (sourceA1282 + difference 1 4) (sourceB1282 + difference 4 1) sourceC1282) = raw20627 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20627; decide +kernel
    rw [ha]
    exact (canonical20627 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1282 + difference 1 5) (sourceB1282 + difference 5 1) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA1282 + difference 1 5) (sourceB1282 + difference 5 1) sourceC1282) = raw20452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20452; decide +kernel
    rw [ha]
    exact (canonical20452 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1282 + difference 2 0) (sourceB1282 + difference 0 2) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1417) := by
    have ha : (tripleCharges (sourceA1282 + difference 2 0) (sourceB1282 + difference 0 2) sourceC1282) = raw20628 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20628; decide +kernel
    rw [ha]
    exact (canonical20628 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1282 + difference 2 1) (sourceB1282 + difference 1 2) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1218) := by
    have ha : (tripleCharges (sourceA1282 + difference 2 1) (sourceB1282 + difference 1 2) sourceC1282) = raw20629 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20629; decide +kernel
    rw [ha]
    exact (canonical20629 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1282 + difference 2 3) (sourceB1282 + difference 3 2) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1218) := by
    have ha : (tripleCharges (sourceA1282 + difference 2 3) (sourceB1282 + difference 3 2) sourceC1282) = raw20630 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20630; decide +kernel
    rw [ha]
    exact (canonical20630 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1282 + difference 2 4) (sourceB1282 + difference 4 2) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1244) := by
    have ha : (tripleCharges (sourceA1282 + difference 2 4) (sourceB1282 + difference 4 2) sourceC1282) = raw20631 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20631; decide +kernel
    rw [ha]
    exact (canonical20631 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1282 + difference 2 5) (sourceB1282 + difference 5 2) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA1282 + difference 2 5) (sourceB1282 + difference 5 2) sourceC1282) = raw20457 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20457; decide +kernel
    rw [ha]
    exact (canonical20457 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1282 + difference 3 0) (sourceB1282 + difference 0 3) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1417) := by
    have ha : (tripleCharges (sourceA1282 + difference 3 0) (sourceB1282 + difference 0 3) sourceC1282) = raw20632 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20632; decide +kernel
    rw [ha]
    exact (canonical20632 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1282 + difference 3 1) (sourceB1282 + difference 1 3) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1218) := by
    have ha : (tripleCharges (sourceA1282 + difference 3 1) (sourceB1282 + difference 1 3) sourceC1282) = raw20633 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20633; decide +kernel
    rw [ha]
    exact (canonical20633 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1282 + difference 3 2) (sourceB1282 + difference 2 3) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1218) := by
    have ha : (tripleCharges (sourceA1282 + difference 3 2) (sourceB1282 + difference 2 3) sourceC1282) = raw20634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20634; decide +kernel
    rw [ha]
    exact (canonical20634 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1282 + difference 3 4) (sourceB1282 + difference 4 3) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1244) := by
    have ha : (tripleCharges (sourceA1282 + difference 3 4) (sourceB1282 + difference 4 3) sourceC1282) = raw20635 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20635; decide +kernel
    rw [ha]
    exact (canonical20635 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1282 + difference 3 5) (sourceB1282 + difference 5 3) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA1282 + difference 3 5) (sourceB1282 + difference 5 3) sourceC1282) = raw20462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20462; decide +kernel
    rw [ha]
    exact (canonical20462 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1282 + difference 4 0) (sourceB1282 + difference 0 4) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1452) := by
    have ha : (tripleCharges (sourceA1282 + difference 4 0) (sourceB1282 + difference 0 4) sourceC1282) = raw20469 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20469; decide +kernel
    rw [ha]
    exact (canonical20469 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1282 + difference 4 1) (sourceB1282 + difference 1 4) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA1282 + difference 4 1) (sourceB1282 + difference 1 4) sourceC1282) = raw20470 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20470; decide +kernel
    rw [ha]
    exact (canonical20470 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1282 + difference 4 2) (sourceB1282 + difference 2 4) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA1282 + difference 4 2) (sourceB1282 + difference 2 4) sourceC1282) = raw20471 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20471; decide +kernel
    rw [ha]
    exact (canonical20471 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1282 + difference 4 3) (sourceB1282 + difference 3 4) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA1282 + difference 4 3) (sourceB1282 + difference 3 4) sourceC1282) = raw20472 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20472; decide +kernel
    rw [ha]
    exact (canonical20472 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1282 + difference 4 5) (sourceB1282 + difference 5 4) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1307) := by
    have ha : (tripleCharges (sourceA1282 + difference 4 5) (sourceB1282 + difference 5 4) sourceC1282) = raw20636 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20636; decide +kernel
    rw [ha]
    exact (canonical20636 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1282 + difference 5 0) (sourceB1282 + difference 0 5) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1453) := by
    have ha : (tripleCharges (sourceA1282 + difference 5 0) (sourceB1282 + difference 0 5) sourceC1282) = raw20637 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20637; decide +kernel
    rw [ha]
    exact (canonical20637 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1282 + difference 5 1) (sourceB1282 + difference 1 5) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1272) := by
    have ha : (tripleCharges (sourceA1282 + difference 5 1) (sourceB1282 + difference 1 5) sourceC1282) = raw20638 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20638; decide +kernel
    rw [ha]
    exact (canonical20638 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1282 + difference 5 2) (sourceB1282 + difference 2 5) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1272) := by
    have ha : (tripleCharges (sourceA1282 + difference 5 2) (sourceB1282 + difference 2 5) sourceC1282) = raw20639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20639; decide +kernel
    rw [ha]
    exact (canonical20639 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1282 + difference 5 3) (sourceB1282 + difference 3 5) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1272) := by
    have ha : (tripleCharges (sourceA1282 + difference 5 3) (sourceB1282 + difference 3 5) sourceC1282) = raw20640 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20640; decide +kernel
    rw [ha]
    exact (canonical20640 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1282 + difference 5 4) (sourceB1282 + difference 4 5) sourceC1282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1309) := by
    have ha : (tripleCharges (sourceA1282 + difference 5 4) (sourceB1282 + difference 4 5) sourceC1282) = raw20641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1282 sourceB1282 sourceC1282 difference raw20641; decide +kernel
    rw [ha]
    exact (canonical20641 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1282 sourceB1282 sourceC1282
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1282, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1111 : Integer.Sparse.reindex keyMap MixedData.row1111 = numericRow1111 := by decide +kernel

theorem numericCheck1111 (x : Master → ℝ) : Integer.Sparse.eval numericRow1111 x =
    (720 : ℝ) * reducedSource1111 x := by
  norm_num [numericRow1111, reducedSource1111, Integer.Sparse.eval, Sparse.eval, nodeValue1047, nodeValue1091, nodeValue1092, nodeValue1218, nodeValue1243, nodeValue1244, nodeValue1271, nodeValue1272, nodeValue1307, nodeValue1309, nodeValue1417, nodeValue1452, nodeValue1453]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1111 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1111 (mixedVector B) = 0 := by
  have h1047 : mixedVector B (Sum.inr 1047) = Sparse.eval nodeValue1047 (mixedVector B) := by
    change mixedMoment B node1047 node1047Labels = _
    exact sound1047 B hB hF
  have h1091 : mixedVector B (Sum.inr 1091) = Sparse.eval nodeValue1091 (mixedVector B) := by
    change mixedMoment B node1091 node1091Labels = _
    exact sound1091 B hB hF
  have h1092 : mixedVector B (Sum.inr 1092) = Sparse.eval nodeValue1092 (mixedVector B) := by
    change mixedMoment B node1092 node1092Labels = _
    exact sound1092 B hB hF
  have h1218 : mixedVector B (Sum.inr 1218) = Sparse.eval nodeValue1218 (mixedVector B) := by
    change mixedMoment B node1218 node1218Labels = _
    exact sound1218 B hB hF
  have h1243 : mixedVector B (Sum.inr 1243) = Sparse.eval nodeValue1243 (mixedVector B) := by
    change mixedMoment B node1243 node1243Labels = _
    exact sound1243 B hB hF
  have h1244 : mixedVector B (Sum.inr 1244) = Sparse.eval nodeValue1244 (mixedVector B) := by
    change mixedMoment B node1244 node1244Labels = _
    exact sound1244 B hB hF
  have h1271 : mixedVector B (Sum.inr 1271) = Sparse.eval nodeValue1271 (mixedVector B) := by
    change mixedMoment B node1271 node1271Labels = _
    exact sound1271 B hB hF
  have h1272 : mixedVector B (Sum.inr 1272) = Sparse.eval nodeValue1272 (mixedVector B) := by
    change mixedMoment B node1272 node1272Labels = _
    exact sound1272 B hB hF
  have h1307 : mixedVector B (Sum.inr 1307) = Sparse.eval nodeValue1307 (mixedVector B) := by
    change mixedMoment B node1307 node1307Labels = _
    exact sound1307 B hB hF
  have h1309 : mixedVector B (Sum.inr 1309) = Sparse.eval nodeValue1309 (mixedVector B) := by
    change mixedMoment B node1309 node1309Labels = _
    exact sound1309 B hB hF
  have h1417 : mixedVector B (Sum.inr 1417) = Sparse.eval nodeValue1417 (mixedVector B) := by
    change mixedMoment B node1417 node1417Labels = _
    exact sound1417 B hB hF
  have h1452 : mixedVector B (Sum.inr 1452) = Sparse.eval nodeValue1452 (mixedVector B) := by
    change mixedMoment B node1452 node1452Labels = _
    exact sound1452 B hB hF
  have h1453 : mixedVector B (Sum.inr 1453) = Sparse.eval nodeValue1453 (mixedVector B) := by
    change mixedMoment B node1453 node1453Labels = _
    exact sound1453 B hB hF
  simpa only [sourceForm1282, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1047, h1091, h1092, h1218, h1243, h1244, h1271, h1272, h1307, h1309, h1417, h1452, h1453, reducedSource1111] using sourceEq1282 B hB

theorem rowSound1111_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1111 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1111, numericCheck1111, reducedZero1111 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111_e_oai
