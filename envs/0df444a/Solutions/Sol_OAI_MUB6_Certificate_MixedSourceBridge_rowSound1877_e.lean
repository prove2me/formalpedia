-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:06:48.135386+00:00
-- url     : https://prove2.me/submissions/14d0b7d3-8d8c-4794-946d-3ae6e777c28d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E099
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1566 raw1566Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw1566 raw1566Labels = mixedMoment B raw1566step0 raw1566step0Labels := by
      have ha : raw1566step0 = (fun i j => raw1566 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1566step0 raw1566; decide +kernel
      have hl : raw1566step0Labels = raw1566Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1566 raw1566Labels permutation32 permutation4
    mixedMoment B raw1566step0 raw1566step0Labels = mixedMoment B raw1566step1 raw1566step1Labels := by
      have ha : raw1566step1 = raw1566step0 := by apply Matrix.ext; unfold raw1566step1 raw1566step0; decide +kernel
      have hl : raw1566step0Labels = labelEmbedding7 ∘ raw1566step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1566step0 raw1566step0Labels raw1566step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4684 node4684Labels := by rfl

theorem canonical1567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1567 raw1567Labels = mixedMoment B node1810 node1810Labels := by
  calc
    mixedMoment B raw1567 raw1567Labels = mixedMoment B raw1567step0 raw1567step0Labels := by
      have ha : raw1567step0 = (fun i j => raw1567 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1567step0 raw1567; decide +kernel
      have hl : raw1567step0Labels = raw1567Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1567 raw1567Labels permutation32 permutation4
    _ = mixedMoment B node1810 node1810Labels := by rfl

theorem canonical1568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1568 raw1568Labels = mixedMoment B node2152 node2152Labels := by
  calc
    mixedMoment B raw1568 raw1568Labels = mixedMoment B raw1568step0 raw1568step0Labels := by
      have ha : raw1568step0 = (fun i j => raw1568 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1568step0 raw1568; decide +kernel
      have hl : raw1568step0Labels = raw1568Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1568 raw1568Labels permutation32 permutation6
    mixedMoment B raw1568step0 raw1568step0Labels = mixedMoment B raw1568step1 raw1568step1Labels := by
      have ha : raw1568step1 = -raw1568step0 := by apply Matrix.ext; change ∀ i j, raw1568step1 i j = -(raw1568step0 i j); unfold raw1568step1 raw1568step0; decide +kernel
      have hl : raw1568step1Labels = raw1568step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1568step1 raw1568step1Labels = mixedMoment B raw1568step2 raw1568step2Labels := by
      have ha : raw1568step2 = raw1568step1 := by apply Matrix.ext; unfold raw1568step2 raw1568step1; decide +kernel
      have hl : raw1568step1Labels = labelEmbedding1 ∘ raw1568step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1568step1 raw1568step1Labels raw1568step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2152 node2152Labels := by rfl

theorem canonical1584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1584 raw1584Labels = mixedMoment B node4692 node4692Labels := by
  calc
    mixedMoment B raw1584 raw1584Labels = mixedMoment B raw1584step0 raw1584step0Labels := by
      have ha : raw1584step0 = (fun i j => raw1584 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1584step0 raw1584; decide +kernel
      have hl : raw1584step0Labels = raw1584Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1584 raw1584Labels permutation8 permutation4
    mixedMoment B raw1584step0 raw1584step0Labels = mixedMoment B raw1584step1 raw1584step1Labels := by
      have ha : raw1584step1 = raw1584step0 := by apply Matrix.ext; unfold raw1584step1 raw1584step0; decide +kernel
      have hl : raw1584step0Labels = labelEmbedding7 ∘ raw1584step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1584step0 raw1584step0Labels raw1584step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4692 node4692Labels := by rfl

theorem canonical1585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1585 raw1585Labels = mixedMoment B node1818 node1818Labels := by
  calc
    mixedMoment B raw1585 raw1585Labels = mixedMoment B raw1585step0 raw1585step0Labels := by
      have ha : raw1585step0 = (fun i j => raw1585 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1585step0 raw1585; decide +kernel
      have hl : raw1585step0Labels = raw1585Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1585 raw1585Labels permutation8 permutation4
    _ = mixedMoment B node1818 node1818Labels := by rfl

theorem canonical1586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1586 raw1586Labels = mixedMoment B node2168 node2168Labels := by
  calc
    mixedMoment B raw1586 raw1586Labels = mixedMoment B raw1586step0 raw1586step0Labels := by
      have ha : raw1586step0 = (fun i j => raw1586 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1586step0 raw1586; decide +kernel
      have hl : raw1586step0Labels = raw1586Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1586 raw1586Labels permutation8 permutation6
    mixedMoment B raw1586step0 raw1586step0Labels = mixedMoment B raw1586step1 raw1586step1Labels := by
      have ha : raw1586step1 = -raw1586step0 := by apply Matrix.ext; change ∀ i j, raw1586step1 i j = -(raw1586step0 i j); unfold raw1586step1 raw1586step0; decide +kernel
      have hl : raw1586step1Labels = raw1586step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1586step1 raw1586step1Labels = mixedMoment B raw1586step2 raw1586step2Labels := by
      have ha : raw1586step2 = raw1586step1 := by apply Matrix.ext; unfold raw1586step2 raw1586step1; decide +kernel
      have hl : raw1586step1Labels = labelEmbedding1 ∘ raw1586step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1586step1 raw1586step1Labels raw1586step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2168 node2168Labels := by rfl

theorem canonical1587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1587 raw1587Labels = mixedMoment B node4693 node4693Labels := by
  calc
    mixedMoment B raw1587 raw1587Labels = mixedMoment B raw1587step0 raw1587step0Labels := by
      have ha : raw1587step0 = (fun i j => raw1587 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1587step0 raw1587; decide +kernel
      have hl : raw1587step0Labels = raw1587Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1587 raw1587Labels permutation8 permutation4
    mixedMoment B raw1587step0 raw1587step0Labels = mixedMoment B raw1587step1 raw1587step1Labels := by
      have ha : raw1587step1 = raw1587step0 := by apply Matrix.ext; unfold raw1587step1 raw1587step0; decide +kernel
      have hl : raw1587step0Labels = labelEmbedding7 ∘ raw1587step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1587step0 raw1587step0Labels raw1587step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4693 node4693Labels := by rfl

theorem canonical1588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1588 raw1588Labels = mixedMoment B node1819 node1819Labels := by
  calc
    mixedMoment B raw1588 raw1588Labels = mixedMoment B raw1588step0 raw1588step0Labels := by
      have ha : raw1588step0 = (fun i j => raw1588 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1588step0 raw1588; decide +kernel
      have hl : raw1588step0Labels = raw1588Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1588 raw1588Labels permutation8 permutation4
    _ = mixedMoment B node1819 node1819Labels := by rfl

theorem canonical1589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1589 raw1589Labels = mixedMoment B node2169 node2169Labels := by
  calc
    mixedMoment B raw1589 raw1589Labels = mixedMoment B raw1589step0 raw1589step0Labels := by
      have ha : raw1589step0 = (fun i j => raw1589 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1589step0 raw1589; decide +kernel
      have hl : raw1589step0Labels = raw1589Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1589 raw1589Labels permutation9 permutation6
    mixedMoment B raw1589step0 raw1589step0Labels = mixedMoment B raw1589step1 raw1589step1Labels := by
      have ha : raw1589step1 = -raw1589step0 := by apply Matrix.ext; change ∀ i j, raw1589step1 i j = -(raw1589step0 i j); unfold raw1589step1 raw1589step0; decide +kernel
      have hl : raw1589step1Labels = raw1589step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1589step1 raw1589step1Labels = mixedMoment B raw1589step2 raw1589step2Labels := by
      have ha : raw1589step2 = raw1589step1 := by apply Matrix.ext; unfold raw1589step2 raw1589step1; decide +kernel
      have hl : raw1589step1Labels = labelEmbedding1 ∘ raw1589step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1589step1 raw1589step1Labels raw1589step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2169 node2169Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1692 raw1692Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw1692 raw1692Labels = mixedMoment B raw1692step0 raw1692step0Labels := by
      have ha : raw1692step0 = (fun i j => raw1692 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1692step0 raw1692; decide +kernel
      have hl : raw1692step0Labels = raw1692Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1692 raw1692Labels permutation152 permutation4
    mixedMoment B raw1692step0 raw1692step0Labels = mixedMoment B raw1692step1 raw1692step1Labels := by
      have ha : raw1692step1 = raw1692step0 := by apply Matrix.ext; unfold raw1692step1 raw1692step0; decide +kernel
      have hl : raw1692step0Labels = labelEmbedding7 ∘ raw1692step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1692step0 raw1692step0Labels raw1692step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4763 node4763Labels := by rfl

theorem canonical1693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1693 raw1693Labels = mixedMoment B node1963 node1963Labels := by
  calc
    mixedMoment B raw1693 raw1693Labels = mixedMoment B raw1693step0 raw1693step0Labels := by
      have ha : raw1693step0 = (fun i j => raw1693 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1693step0 raw1693; decide +kernel
      have hl : raw1693step0Labels = raw1693Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1693 raw1693Labels permutation152 permutation4
    _ = mixedMoment B node1963 node1963Labels := by rfl

theorem canonical1694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1694 raw1694Labels = mixedMoment B node2174 node2174Labels := by
  calc
    mixedMoment B raw1694 raw1694Labels = mixedMoment B raw1694step0 raw1694step0Labels := by
      have ha : raw1694step0 = (fun i j => raw1694 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1694step0 raw1694; decide +kernel
      have hl : raw1694step0Labels = raw1694Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1694 raw1694Labels permutation152 permutation6
    mixedMoment B raw1694step0 raw1694step0Labels = mixedMoment B raw1694step1 raw1694step1Labels := by
      have ha : raw1694step1 = -raw1694step0 := by apply Matrix.ext; change ∀ i j, raw1694step1 i j = -(raw1694step0 i j); unfold raw1694step1 raw1694step0; decide +kernel
      have hl : raw1694step1Labels = raw1694step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1694step1 raw1694step1Labels = mixedMoment B raw1694step2 raw1694step2Labels := by
      have ha : raw1694step2 = raw1694step1 := by apply Matrix.ext; unfold raw1694step2 raw1694step1; decide +kernel
      have hl : raw1694step1Labels = labelEmbedding1 ∘ raw1694step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1694step1 raw1694step1Labels raw1694step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2174 node2174Labels := by rfl

theorem canonical1704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1704 raw1704Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw1704 raw1704Labels = mixedMoment B raw1704step0 raw1704step0Labels := by
      have ha : raw1704step0 = (fun i j => raw1704 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1704step0 raw1704; decide +kernel
      have hl : raw1704step0Labels = raw1704Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1704 raw1704Labels permutation32 permutation4
    mixedMoment B raw1704step0 raw1704step0Labels = mixedMoment B raw1704step1 raw1704step1Labels := by
      have ha : raw1704step1 = raw1704step0 := by apply Matrix.ext; unfold raw1704step1 raw1704step0; decide +kernel
      have hl : raw1704step0Labels = labelEmbedding7 ∘ raw1704step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1704step0 raw1704step0Labels raw1704step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4769 node4769Labels := by rfl

theorem canonical1705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1705 raw1705Labels = mixedMoment B node1969 node1969Labels := by
  calc
    mixedMoment B raw1705 raw1705Labels = mixedMoment B raw1705step0 raw1705step0Labels := by
      have ha : raw1705step0 = (fun i j => raw1705 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1705step0 raw1705; decide +kernel
      have hl : raw1705step0Labels = raw1705Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1705 raw1705Labels permutation32 permutation4
    _ = mixedMoment B node1969 node1969Labels := by rfl

theorem canonical1706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1706 raw1706Labels = mixedMoment B node2185 node2185Labels := by
  calc
    mixedMoment B raw1706 raw1706Labels = mixedMoment B raw1706step0 raw1706step0Labels := by
      have ha : raw1706step0 = (fun i j => raw1706 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1706step0 raw1706; decide +kernel
      have hl : raw1706step0Labels = raw1706Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1706 raw1706Labels permutation32 permutation6
    mixedMoment B raw1706step0 raw1706step0Labels = mixedMoment B raw1706step1 raw1706step1Labels := by
      have ha : raw1706step1 = -raw1706step0 := by apply Matrix.ext; change ∀ i j, raw1706step1 i j = -(raw1706step0 i j); unfold raw1706step1 raw1706step0; decide +kernel
      have hl : raw1706step1Labels = raw1706step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1706step1 raw1706step1Labels = mixedMoment B raw1706step2 raw1706step2Labels := by
      have ha : raw1706step2 = raw1706step1 := by apply Matrix.ext; unfold raw1706step2 raw1706step1; decide +kernel
      have hl : raw1706step1Labels = labelEmbedding1 ∘ raw1706step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1706step1 raw1706step1Labels raw1706step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2185 node2185Labels := by rfl

theorem canonical1707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1707 raw1707Labels = mixedMoment B node4770 node4770Labels := by
  calc
    mixedMoment B raw1707 raw1707Labels = mixedMoment B raw1707step0 raw1707step0Labels := by
      have ha : raw1707step0 = (fun i j => raw1707 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1707step0 raw1707; decide +kernel
      have hl : raw1707step0Labels = raw1707Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1707 raw1707Labels permutation32 permutation4
    mixedMoment B raw1707step0 raw1707step0Labels = mixedMoment B raw1707step1 raw1707step1Labels := by
      have ha : raw1707step1 = raw1707step0 := by apply Matrix.ext; unfold raw1707step1 raw1707step0; decide +kernel
      have hl : raw1707step0Labels = labelEmbedding7 ∘ raw1707step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1707step0 raw1707step0Labels raw1707step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4770 node4770Labels := by rfl

theorem canonical1708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1708 raw1708Labels = mixedMoment B node1970 node1970Labels := by
  calc
    mixedMoment B raw1708 raw1708Labels = mixedMoment B raw1708step0 raw1708step0Labels := by
      have ha : raw1708step0 = (fun i j => raw1708 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1708step0 raw1708; decide +kernel
      have hl : raw1708step0Labels = raw1708Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1708 raw1708Labels permutation32 permutation4
    _ = mixedMoment B node1970 node1970Labels := by rfl

theorem canonical1709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1709 raw1709Labels = mixedMoment B node2186 node2186Labels := by
  calc
    mixedMoment B raw1709 raw1709Labels = mixedMoment B raw1709step0 raw1709step0Labels := by
      have ha : raw1709step0 = (fun i j => raw1709 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1709step0 raw1709; decide +kernel
      have hl : raw1709step0Labels = raw1709Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1709 raw1709Labels permutation33 permutation6
    mixedMoment B raw1709step0 raw1709step0Labels = mixedMoment B raw1709step1 raw1709step1Labels := by
      have ha : raw1709step1 = -raw1709step0 := by apply Matrix.ext; change ∀ i j, raw1709step1 i j = -(raw1709step0 i j); unfold raw1709step1 raw1709step0; decide +kernel
      have hl : raw1709step1Labels = raw1709step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1709step1 raw1709step1Labels = mixedMoment B raw1709step2 raw1709step2Labels := by
      have ha : raw1709step2 = raw1709step1 := by apply Matrix.ext; unfold raw1709step2 raw1709step1; decide +kernel
      have hl : raw1709step1Labels = labelEmbedding1 ∘ raw1709step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1709step1 raw1709step1Labels raw1709step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2186 node2186Labels := by rfl

theorem canonical1767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1767 raw1767Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw1767 raw1767Labels = mixedMoment B raw1767step0 raw1767step0Labels := by
      have ha : raw1767step0 = (fun i j => raw1767 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1767step0 raw1767; decide +kernel
      have hl : raw1767step0Labels = raw1767Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1767 raw1767Labels permutation32 permutation4
    mixedMoment B raw1767step0 raw1767step0Labels = mixedMoment B raw1767step1 raw1767step1Labels := by
      have ha : raw1767step1 = raw1767step0 := by apply Matrix.ext; unfold raw1767step1 raw1767step0; decide +kernel
      have hl : raw1767step0Labels = labelEmbedding7 ∘ raw1767step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1767step0 raw1767step0Labels raw1767step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

theorem canonical1768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1768 raw1768Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw1768 raw1768Labels = mixedMoment B raw1768step0 raw1768step0Labels := by
      have ha : raw1768step0 = (fun i j => raw1768 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1768step0 raw1768; decide +kernel
      have hl : raw1768step0Labels = raw1768Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1768 raw1768Labels permutation32 permutation4
    _ = mixedMoment B node2054 node2054Labels := by rfl

theorem canonical1769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1769 raw1769Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw1769 raw1769Labels = mixedMoment B raw1769step0 raw1769step0Labels := by
      have ha : raw1769step0 = (fun i j => raw1769 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1769step0 raw1769; decide +kernel
      have hl : raw1769step0Labels = raw1769Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1769 raw1769Labels permutation33 permutation6
    mixedMoment B raw1769step0 raw1769step0Labels = mixedMoment B raw1769step1 raw1769step1Labels := by
      have ha : raw1769step1 = -raw1769step0 := by apply Matrix.ext; change ∀ i j, raw1769step1 i j = -(raw1769step0 i j); unfold raw1769step1 raw1769step0; decide +kernel
      have hl : raw1769step1Labels = raw1769step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1769step1 raw1769step1Labels = mixedMoment B raw1769step2 raw1769step2Labels := by
      have ha : raw1769step2 = raw1769step1 := by apply Matrix.ext; unfold raw1769step2 raw1769step1; decide +kernel
      have hl : raw1769step1Labels = labelEmbedding1 ∘ raw1769step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1769step1 raw1769step1Labels raw1769step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

theorem canonical1773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1773 raw1773Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw1773 raw1773Labels = mixedMoment B raw1773step0 raw1773step0Labels := by
      have ha : raw1773step0 = (fun i j => raw1773 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1773step0 raw1773; decide +kernel
      have hl : raw1773step0Labels = raw1773Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1773 raw1773Labels permutation8 permutation4
    mixedMoment B raw1773step0 raw1773step0Labels = mixedMoment B raw1773step1 raw1773step1Labels := by
      have ha : raw1773step1 = raw1773step0 := by apply Matrix.ext; unfold raw1773step1 raw1773step0; decide +kernel
      have hl : raw1773step0Labels = labelEmbedding7 ∘ raw1773step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1773step0 raw1773step0Labels raw1773step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4843 node4843Labels := by rfl

theorem canonical1774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1774 raw1774Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw1774 raw1774Labels = mixedMoment B raw1774step0 raw1774step0Labels := by
      have ha : raw1774step0 = (fun i j => raw1774 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1774step0 raw1774; decide +kernel
      have hl : raw1774step0Labels = raw1774Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1774 raw1774Labels permutation8 permutation4
    _ = mixedMoment B node2062 node2062Labels := by rfl

theorem canonical1775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1775 raw1775Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw1775 raw1775Labels = mixedMoment B raw1775step0 raw1775step0Labels := by
      have ha : raw1775step0 = (fun i j => raw1775 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1775step0 raw1775; decide +kernel
      have hl : raw1775step0Labels = raw1775Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1775 raw1775Labels permutation9 permutation6
    mixedMoment B raw1775step0 raw1775step0Labels = mixedMoment B raw1775step1 raw1775step1Labels := by
      have ha : raw1775step1 = -raw1775step0 := by apply Matrix.ext; change ∀ i j, raw1775step1 i j = -(raw1775step0 i j); unfold raw1775step1 raw1775step0; decide +kernel
      have hl : raw1775step1Labels = raw1775step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1775step1 raw1775step1Labels = mixedMoment B raw1775step2 raw1775step2Labels := by
      have ha : raw1775step2 = raw1775step1 := by apply Matrix.ext; unfold raw1775step2 raw1775step1; decide +kernel
      have hl : raw1775step1Labels = labelEmbedding1 ∘ raw1775step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1775step1 raw1775step1Labels raw1775step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical169
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21634 raw21634Labels = mixedMoment B node4901 node4901Labels := by
  calc
    mixedMoment B raw21634 raw21634Labels = mixedMoment B raw21634step0 raw21634step0Labels := by
      have hz : ∀ j, raw21634 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21634step0 = (fun i j => raw21634 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21634step0 raw21634; decide +kernel
      have hl : raw21634step0Labels = raw21634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21634 raw21634Labels permutation434 hz
    mixedMoment B raw21634step0 raw21634step0Labels = mixedMoment B raw21634step1 raw21634step1Labels := by
      have hz : ∀ j, raw21634step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21634step1 = (fun i j => raw21634step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21634step1 raw21634step0; decide +kernel
      have hl : raw21634step1Labels = raw21634step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21634step0 raw21634step0Labels permutation80 hz
    mixedMoment B raw21634step1 raw21634step1Labels = mixedMoment B raw21634step2 raw21634step2Labels := by
      have hz : ∀ j, raw21634step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21634step2 = (fun i j => raw21634step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21634step2 raw21634step1; decide +kernel
      have hl : raw21634step2Labels = raw21634step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21634step1 raw21634step1Labels permutation14 hz
    _ = mixedMoment B node4901 node4901Labels := by rfl

theorem canonical21648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21648 raw21648Labels = mixedMoment B node4361 node4361Labels := by
  calc
    mixedMoment B raw21648 raw21648Labels = mixedMoment B raw21648step0 raw21648step0Labels := by
      have hz : ∀ j, raw21648 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21648step0 = (fun i j => raw21648 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21648step0 raw21648; decide +kernel
      have hl : raw21648step0Labels = raw21648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21648 raw21648Labels permutation434 hz
    mixedMoment B raw21648step0 raw21648step0Labels = mixedMoment B raw21648step1 raw21648step1Labels := by
      have hz : ∀ j, raw21648step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21648step1 = (fun i j => raw21648step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21648step1 raw21648step0; decide +kernel
      have hl : raw21648step1Labels = raw21648step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21648step0 raw21648step0Labels permutation80 hz
    _ = mixedMoment B node4361 node4361Labels := by rfl

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

theorem canonical2256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2256 raw2256Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw2256 raw2256Labels = mixedMoment B raw2256step0 raw2256step0Labels := by
      have ha : raw2256step0 = (fun i j => raw2256 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2256step0 raw2256; decide +kernel
      have hl : raw2256step0Labels = raw2256Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2256 raw2256Labels permutation8 permutation4
    mixedMoment B raw2256step0 raw2256step0Labels = mixedMoment B raw2256step1 raw2256step1Labels := by
      have ha : raw2256step1 = raw2256step0 := by apply Matrix.ext; unfold raw2256step1 raw2256step0; decide +kernel
      have hl : raw2256step0Labels = labelEmbedding7 ∘ raw2256step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2256step0 raw2256step0Labels raw2256step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

theorem canonical2257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2257 raw2257Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw2257 raw2257Labels = mixedMoment B raw2257step0 raw2257step0Labels := by
      have ha : raw2257step0 = (fun i j => raw2257 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2257step0 raw2257; decide +kernel
      have hl : raw2257step0Labels = raw2257Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2257 raw2257Labels permutation8 permutation4
    _ = mixedMoment B node2686 node2686Labels := by rfl

theorem canonical2258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2258 raw2258Labels = mixedMoment B node3397 node3397Labels := by
  calc
    mixedMoment B raw2258 raw2258Labels = mixedMoment B raw2258step0 raw2258step0Labels := by
      have ha : raw2258step0 = (fun i j => raw2258 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2258step0 raw2258; decide +kernel
      have hl : raw2258step0Labels = raw2258Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2258 raw2258Labels permutation8 permutation6
    mixedMoment B raw2258step0 raw2258step0Labels = mixedMoment B raw2258step1 raw2258step1Labels := by
      have ha : raw2258step1 = -raw2258step0 := by apply Matrix.ext; change ∀ i j, raw2258step1 i j = -(raw2258step0 i j); unfold raw2258step1 raw2258step0; decide +kernel
      have hl : raw2258step1Labels = raw2258step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2258step1 raw2258step1Labels = mixedMoment B raw2258step2 raw2258step2Labels := by
      have ha : raw2258step2 = raw2258step1 := by apply Matrix.ext; unfold raw2258step2 raw2258step1; decide +kernel
      have hl : raw2258step1Labels = labelEmbedding1 ∘ raw2258step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2258step1 raw2258step1Labels raw2258step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3397 node3397Labels := by rfl

theorem canonical2265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2265 raw2265Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw2265 raw2265Labels = mixedMoment B raw2265step0 raw2265step0Labels := by
      have ha : raw2265step0 = (fun i j => raw2265 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2265step0 raw2265; decide +kernel
      have hl : raw2265step0Labels = raw2265Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2265 raw2265Labels permutation32 permutation4
    mixedMoment B raw2265step0 raw2265step0Labels = mixedMoment B raw2265step1 raw2265step1Labels := by
      have ha : raw2265step1 = raw2265step0 := by apply Matrix.ext; unfold raw2265step1 raw2265step0; decide +kernel
      have hl : raw2265step0Labels = labelEmbedding7 ∘ raw2265step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2265step0 raw2265step0Labels raw2265step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

theorem canonical2266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2266 raw2266Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw2266 raw2266Labels = mixedMoment B raw2266step0 raw2266step0Labels := by
      have ha : raw2266step0 = (fun i j => raw2266 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2266step0 raw2266; decide +kernel
      have hl : raw2266step0Labels = raw2266Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2266 raw2266Labels permutation32 permutation4
    _ = mixedMoment B node2705 node2705Labels := by rfl

theorem canonical2267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2267 raw2267Labels = mixedMoment B node3498 node3498Labels := by
  calc
    mixedMoment B raw2267 raw2267Labels = mixedMoment B raw2267step0 raw2267step0Labels := by
      have ha : raw2267step0 = (fun i j => raw2267 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2267step0 raw2267; decide +kernel
      have hl : raw2267step0Labels = raw2267Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2267 raw2267Labels permutation32 permutation6
    mixedMoment B raw2267step0 raw2267step0Labels = mixedMoment B raw2267step1 raw2267step1Labels := by
      have ha : raw2267step1 = -raw2267step0 := by apply Matrix.ext; change ∀ i j, raw2267step1 i j = -(raw2267step0 i j); unfold raw2267step1 raw2267step0; decide +kernel
      have hl : raw2267step1Labels = raw2267step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2267step1 raw2267step1Labels = mixedMoment B raw2267step2 raw2267step2Labels := by
      have ha : raw2267step2 = raw2267step1 := by apply Matrix.ext; unfold raw2267step2 raw2267step1; decide +kernel
      have hl : raw2267step1Labels = labelEmbedding1 ∘ raw2267step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2267step1 raw2267step1Labels raw2267step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3498 node3498Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical183
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23523 raw23523Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw23523 raw23523Labels = mixedMoment B raw23523step0 raw23523step0Labels := by
      have hz : ∀ j, raw23523 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23523step0 = (fun i j => raw23523 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23523step0 raw23523; decide +kernel
      have hl : raw23523step0Labels = raw23523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23523 raw23523Labels permutation434 hz
    mixedMoment B raw23523step0 raw23523step0Labels = mixedMoment B raw23523step1 raw23523step1Labels := by
      have ha : raw23523step1 = (fun i j => raw23523step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23523step1 raw23523step0; decide +kernel
      have hl : raw23523step1Labels = raw23523step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23523step0 raw23523step0Labels permutation33 permutation2
    _ = mixedMoment B node4349 node4349Labels := by rfl

theorem canonical23527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23527 raw23527Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw23527 raw23527Labels = mixedMoment B raw23527step0 raw23527step0Labels := by
      have hz : ∀ j, raw23527 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23527step0 = (fun i j => raw23527 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23527step0 raw23527; decide +kernel
      have hl : raw23527step0Labels = raw23527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23527 raw23527Labels permutation346 hz
    mixedMoment B raw23527step0 raw23527step0Labels = mixedMoment B raw23527step1 raw23527step1Labels := by
      have ha : raw23527step1 = (fun i j => raw23527step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23527step1 raw23527step0; decide +kernel
      have hl : raw23527step1Labels = raw23527step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23527step0 raw23527step0Labels permutation33 permutation2
    _ = mixedMoment B node4349 node4349Labels := by rfl

theorem canonical23531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23531 raw23531Labels = mixedMoment B node4360 node4360Labels := by
  calc
    mixedMoment B raw23531 raw23531Labels = mixedMoment B raw23531step0 raw23531step0Labels := by
      have hz : ∀ j, raw23531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23531step0 = (fun i j => raw23531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23531step0 raw23531; decide +kernel
      have hl : raw23531step0Labels = raw23531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23531 raw23531Labels permutation434 hz
    mixedMoment B raw23531step0 raw23531step0Labels = mixedMoment B raw23531step1 raw23531step1Labels := by
      have hz : ∀ j, raw23531step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23531step1 = (fun i j => raw23531step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23531step1 raw23531step0; decide +kernel
      have hl : raw23531step1Labels = raw23531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23531step0 raw23531step0Labels permutation80 hz
    mixedMoment B raw23531step1 raw23531step1Labels = mixedMoment B raw23531step2 raw23531step2Labels := by
      have ha : raw23531step2 = (fun i j => raw23531step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23531step2 raw23531step1; decide +kernel
      have hl : raw23531step2Labels = raw23531step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23531step1 raw23531step1Labels permutation9 permutation2
    _ = mixedMoment B node4360 node4360Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical247
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical31728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31728 raw31728Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw31728 raw31728Labels = mixedMoment B raw31728step0 raw31728step0Labels := by
      have hz : ∀ j, raw31728 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31728step0 = (fun i j => raw31728 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31728step0 raw31728; decide +kernel
      have hl : raw31728step0Labels = raw31728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31728 raw31728Labels permutation434 hz
    mixedMoment B raw31728step0 raw31728step0Labels = mixedMoment B raw31728step1 raw31728step1Labels := by
      have hz : ∀ j, raw31728step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31728step1 = (fun i j => raw31728step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31728step1 raw31728step0; decide +kernel
      have hl : raw31728step1Labels = raw31728step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31728step0 raw31728step0Labels permutation80 hz
    mixedMoment B raw31728step1 raw31728step1Labels = mixedMoment B raw31728step2 raw31728step2Labels := by
      have ha : raw31728step2 = (fun i j => raw31728step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31728step2 raw31728step1; decide +kernel
      have hl : raw31728step2Labels = raw31728step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31728step1 raw31728step1Labels permutation9 permutation7
    mixedMoment B raw31728step2 raw31728step2Labels = mixedMoment B raw31728step3 raw31728step3Labels := by
      have ha : raw31728step3 = -raw31728step2 := by apply Matrix.ext; change ∀ i j, raw31728step3 i j = -(raw31728step2 i j); unfold raw31728step3 raw31728step2; decide +kernel
      have hl : raw31728step3Labels = raw31728step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31728step3 raw31728step3Labels = mixedMoment B raw31728step4 raw31728step4Labels := by
      have ha : raw31728step4 = raw31728step3 := by apply Matrix.ext; unfold raw31728step4 raw31728step3; decide +kernel
      have hl : raw31728step3Labels = labelEmbedding10 ∘ raw31728step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31728step3 raw31728step3Labels raw31728step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

theorem canonical31729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31729 raw31729Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw31729 raw31729Labels = mixedMoment B raw31729step0 raw31729step0Labels := by
      have hz : ∀ j, raw31729 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31729step0 = (fun i j => raw31729 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31729step0 raw31729; decide +kernel
      have hl : raw31729step0Labels = raw31729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31729 raw31729Labels permutation434 hz
    mixedMoment B raw31729step0 raw31729step0Labels = mixedMoment B raw31729step1 raw31729step1Labels := by
      have ha : raw31729step1 = (fun i j => raw31729step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31729step1 raw31729step0; decide +kernel
      have hl : raw31729step1Labels = raw31729step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31729step0 raw31729step0Labels permutation33 permutation7
    mixedMoment B raw31729step1 raw31729step1Labels = mixedMoment B raw31729step2 raw31729step2Labels := by
      have ha : raw31729step2 = -raw31729step1 := by apply Matrix.ext; change ∀ i j, raw31729step2 i j = -(raw31729step1 i j); unfold raw31729step2 raw31729step1; decide +kernel
      have hl : raw31729step2Labels = raw31729step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31729step2 raw31729step2Labels = mixedMoment B raw31729step3 raw31729step3Labels := by
      have ha : raw31729step3 = raw31729step2 := by apply Matrix.ext; unfold raw31729step3 raw31729step2; decide +kernel
      have hl : raw31729step2Labels = labelEmbedding10 ∘ raw31729step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31729step2 raw31729step2Labels raw31729step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

theorem canonical31730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31730 raw31730Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw31730 raw31730Labels = mixedMoment B raw31730step0 raw31730step0Labels := by
      have hz : ∀ j, raw31730 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31730step0 = (fun i j => raw31730 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31730step0 raw31730; decide +kernel
      have hl : raw31730step0Labels = raw31730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31730 raw31730Labels permutation346 hz
    mixedMoment B raw31730step0 raw31730step0Labels = mixedMoment B raw31730step1 raw31730step1Labels := by
      have ha : raw31730step1 = (fun i j => raw31730step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31730step1 raw31730step0; decide +kernel
      have hl : raw31730step1Labels = raw31730step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31730step0 raw31730step0Labels permutation33 permutation7
    mixedMoment B raw31730step1 raw31730step1Labels = mixedMoment B raw31730step2 raw31730step2Labels := by
      have ha : raw31730step2 = -raw31730step1 := by apply Matrix.ext; change ∀ i j, raw31730step2 i j = -(raw31730step1 i j); unfold raw31730step2 raw31730step1; decide +kernel
      have hl : raw31730step2Labels = raw31730step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31730step2 raw31730step2Labels = mixedMoment B raw31730step3 raw31730step3Labels := by
      have ha : raw31730step3 = raw31730step2 := by apply Matrix.ext; unfold raw31730step3 raw31730step2; decide +kernel
      have hl : raw31730step2Labels = labelEmbedding10 ∘ raw31730step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31730step2 raw31730step2Labels raw31730step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

theorem canonical31731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31731 raw31731Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw31731 raw31731Labels = mixedMoment B raw31731step0 raw31731step0Labels := by
      have hz : ∀ j, raw31731 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31731step0 = (fun i j => raw31731 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31731step0 raw31731; decide +kernel
      have hl : raw31731step0Labels = raw31731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31731 raw31731Labels permutation434 hz
    mixedMoment B raw31731step0 raw31731step0Labels = mixedMoment B raw31731step1 raw31731step1Labels := by
      have hz : ∀ j, raw31731step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31731step1 = (fun i j => raw31731step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31731step1 raw31731step0; decide +kernel
      have hl : raw31731step1Labels = raw31731step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31731step0 raw31731step0Labels permutation80 hz
    mixedMoment B raw31731step1 raw31731step1Labels = mixedMoment B raw31731step2 raw31731step2Labels := by
      have ha : raw31731step2 = (fun i j => raw31731step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31731step2 raw31731step1; decide +kernel
      have hl : raw31731step2Labels = raw31731step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31731step1 raw31731step1Labels permutation9 permutation7
    mixedMoment B raw31731step2 raw31731step2Labels = mixedMoment B raw31731step3 raw31731step3Labels := by
      have ha : raw31731step3 = -raw31731step2 := by apply Matrix.ext; change ∀ i j, raw31731step3 i j = -(raw31731step2 i j); unfold raw31731step3 raw31731step2; decide +kernel
      have hl : raw31731step3Labels = raw31731step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31731step3 raw31731step3Labels = mixedMoment B raw31731step4 raw31731step4Labels := by
      have ha : raw31731step4 = raw31731step3 := by apply Matrix.ext; unfold raw31731step4 raw31731step3; decide +kernel
      have hl : raw31731step3Labels = labelEmbedding10 ∘ raw31731step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31731step3 raw31731step3Labels raw31731step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

theorem canonical31732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31732 raw31732Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw31732 raw31732Labels = mixedMoment B raw31732step0 raw31732step0Labels := by
      have hz : ∀ j, raw31732 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31732step0 = (fun i j => raw31732 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31732step0 raw31732; decide +kernel
      have hl : raw31732step0Labels = raw31732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31732 raw31732Labels permutation434 hz
    mixedMoment B raw31732step0 raw31732step0Labels = mixedMoment B raw31732step1 raw31732step1Labels := by
      have ha : raw31732step1 = (fun i j => raw31732step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31732step1 raw31732step0; decide +kernel
      have hl : raw31732step1Labels = raw31732step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31732step0 raw31732step0Labels permutation33 permutation2
    _ = mixedMoment B node4684 node4684Labels := by rfl

theorem canonical31733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31733 raw31733Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw31733 raw31733Labels = mixedMoment B raw31733step0 raw31733step0Labels := by
      have ha : raw31733step0 = (fun i j => raw31733 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31733step0 raw31733; decide +kernel
      have hl : raw31733step0Labels = raw31733Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31733 raw31733Labels permutation159 permutation2
    _ = mixedMoment B node4763 node4763Labels := by rfl

theorem canonical31734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31734 raw31734Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw31734 raw31734Labels = mixedMoment B raw31734step0 raw31734step0Labels := by
      have hz : ∀ j, raw31734 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31734step0 = (fun i j => raw31734 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31734step0 raw31734; decide +kernel
      have hl : raw31734step0Labels = raw31734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31734 raw31734Labels permutation434 hz
    mixedMoment B raw31734step0 raw31734step0Labels = mixedMoment B raw31734step1 raw31734step1Labels := by
      have ha : raw31734step1 = (fun i j => raw31734step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31734step1 raw31734step0; decide +kernel
      have hl : raw31734step1Labels = raw31734step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31734step0 raw31734step0Labels permutation33 permutation2
    _ = mixedMoment B node4834 node4834Labels := by rfl

theorem canonical31735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31735 raw31735Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw31735 raw31735Labels = mixedMoment B raw31735step0 raw31735step0Labels := by
      have hz : ∀ j, raw31735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31735step0 = (fun i j => raw31735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31735step0 raw31735; decide +kernel
      have hl : raw31735step0Labels = raw31735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31735 raw31735Labels permutation346 hz
    mixedMoment B raw31735step0 raw31735step0Labels = mixedMoment B raw31735step1 raw31735step1Labels := by
      have ha : raw31735step1 = (fun i j => raw31735step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31735step1 raw31735step0; decide +kernel
      have hl : raw31735step1Labels = raw31735step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31735step0 raw31735step0Labels permutation33 permutation2
    _ = mixedMoment B node4684 node4684Labels := by rfl

theorem canonical31736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31736 raw31736Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw31736 raw31736Labels = mixedMoment B raw31736step0 raw31736step0Labels := by
      have ha : raw31736step0 = (fun i j => raw31736 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31736step0 raw31736; decide +kernel
      have hl : raw31736step0Labels = raw31736Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31736 raw31736Labels permutation153 permutation2
    _ = mixedMoment B node4763 node4763Labels := by rfl

theorem canonical31737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31737 raw31737Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw31737 raw31737Labels = mixedMoment B raw31737step0 raw31737step0Labels := by
      have hz : ∀ j, raw31737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31737step0 = (fun i j => raw31737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31737step0 raw31737; decide +kernel
      have hl : raw31737step0Labels = raw31737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31737 raw31737Labels permutation346 hz
    mixedMoment B raw31737step0 raw31737step0Labels = mixedMoment B raw31737step1 raw31737step1Labels := by
      have ha : raw31737step1 = (fun i j => raw31737step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31737step1 raw31737step0; decide +kernel
      have hl : raw31737step1Labels = raw31737step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31737step0 raw31737step0Labels permutation33 permutation2
    _ = mixedMoment B node4834 node4834Labels := by rfl

theorem canonical31738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31738 raw31738Labels = mixedMoment B node4692 node4692Labels := by
  calc
    mixedMoment B raw31738 raw31738Labels = mixedMoment B raw31738step0 raw31738step0Labels := by
      have hz : ∀ j, raw31738 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31738step0 = (fun i j => raw31738 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31738step0 raw31738; decide +kernel
      have hl : raw31738step0Labels = raw31738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31738 raw31738Labels permutation434 hz
    mixedMoment B raw31738step0 raw31738step0Labels = mixedMoment B raw31738step1 raw31738step1Labels := by
      have hz : ∀ j, raw31738step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31738step1 = (fun i j => raw31738step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31738step1 raw31738step0; decide +kernel
      have hl : raw31738step1Labels = raw31738step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31738step0 raw31738step0Labels permutation80 hz
    mixedMoment B raw31738step1 raw31738step1Labels = mixedMoment B raw31738step2 raw31738step2Labels := by
      have ha : raw31738step2 = (fun i j => raw31738step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31738step2 raw31738step1; decide +kernel
      have hl : raw31738step2Labels = raw31738step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31738step1 raw31738step1Labels permutation9 permutation2
    _ = mixedMoment B node4692 node4692Labels := by rfl

theorem canonical31739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31739 raw31739Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw31739 raw31739Labels = mixedMoment B raw31739step0 raw31739step0Labels := by
      have hz : ∀ j, raw31739 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31739step0 = (fun i j => raw31739 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31739step0 raw31739; decide +kernel
      have hl : raw31739step0Labels = raw31739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31739 raw31739Labels permutation434 hz
    mixedMoment B raw31739step0 raw31739step0Labels = mixedMoment B raw31739step1 raw31739step1Labels := by
      have ha : raw31739step1 = (fun i j => raw31739step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31739step1 raw31739step0; decide +kernel
      have hl : raw31739step1Labels = raw31739step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31739step0 raw31739step0Labels permutation33 permutation2
    _ = mixedMoment B node4769 node4769Labels := by rfl

theorem canonical31740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31740 raw31740Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw31740 raw31740Labels = mixedMoment B raw31740step0 raw31740step0Labels := by
      have hz : ∀ j, raw31740 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31740step0 = (fun i j => raw31740 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31740step0 raw31740; decide +kernel
      have hl : raw31740step0Labels = raw31740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31740 raw31740Labels permutation346 hz
    mixedMoment B raw31740step0 raw31740step0Labels = mixedMoment B raw31740step1 raw31740step1Labels := by
      have ha : raw31740step1 = (fun i j => raw31740step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31740step1 raw31740step0; decide +kernel
      have hl : raw31740step1Labels = raw31740step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31740step0 raw31740step0Labels permutation33 permutation2
    _ = mixedMoment B node4769 node4769Labels := by rfl

theorem canonical31741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31741 raw31741Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw31741 raw31741Labels = mixedMoment B raw31741step0 raw31741step0Labels := by
      have hz : ∀ j, raw31741 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31741step0 = (fun i j => raw31741 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31741step0 raw31741; decide +kernel
      have hl : raw31741step0Labels = raw31741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31741 raw31741Labels permutation434 hz
    mixedMoment B raw31741step0 raw31741step0Labels = mixedMoment B raw31741step1 raw31741step1Labels := by
      have hz : ∀ j, raw31741step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31741step1 = (fun i j => raw31741step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31741step1 raw31741step0; decide +kernel
      have hl : raw31741step1Labels = raw31741step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31741step0 raw31741step0Labels permutation80 hz
    mixedMoment B raw31741step1 raw31741step1Labels = mixedMoment B raw31741step2 raw31741step2Labels := by
      have ha : raw31741step2 = (fun i j => raw31741step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31741step2 raw31741step1; decide +kernel
      have hl : raw31741step2Labels = raw31741step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31741step1 raw31741step1Labels permutation9 permutation2
    _ = mixedMoment B node4841 node4841Labels := by rfl

theorem canonical31742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31742 raw31742Labels = mixedMoment B node4693 node4693Labels := by
  calc
    mixedMoment B raw31742 raw31742Labels = mixedMoment B raw31742step0 raw31742step0Labels := by
      have hz : ∀ j, raw31742 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31742step0 = (fun i j => raw31742 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31742step0 raw31742; decide +kernel
      have hl : raw31742step0Labels = raw31742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31742 raw31742Labels permutation434 hz
    mixedMoment B raw31742step0 raw31742step0Labels = mixedMoment B raw31742step1 raw31742step1Labels := by
      have hz : ∀ j, raw31742step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31742step1 = (fun i j => raw31742step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31742step1 raw31742step0; decide +kernel
      have hl : raw31742step1Labels = raw31742step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31742step0 raw31742step0Labels permutation80 hz
    _ = mixedMoment B node4693 node4693Labels := by rfl

theorem canonical31743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31743 raw31743Labels = mixedMoment B node4770 node4770Labels := by
  calc
    mixedMoment B raw31743 raw31743Labels = mixedMoment B raw31743step0 raw31743step0Labels := by
      have hz : ∀ j, raw31743 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31743step0 = (fun i j => raw31743 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31743step0 raw31743; decide +kernel
      have hl : raw31743step0Labels = raw31743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31743 raw31743Labels permutation434 hz
    _ = mixedMoment B node4770 node4770Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical248
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical31744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31744 raw31744Labels = mixedMoment B node4770 node4770Labels := by
  calc
    mixedMoment B raw31744 raw31744Labels = mixedMoment B raw31744step0 raw31744step0Labels := by
      have hz : ∀ j, raw31744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31744step0 = (fun i j => raw31744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31744step0 raw31744; decide +kernel
      have hl : raw31744step0Labels = raw31744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31744 raw31744Labels permutation346 hz
    _ = mixedMoment B node4770 node4770Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1134 raw1134Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw1134 raw1134Labels = mixedMoment B raw1134step0 raw1134step0Labels := by
      have ha : raw1134step0 = (fun i j => raw1134 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1134step0 raw1134; decide +kernel
      have hl : raw1134step0Labels = raw1134Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1134 raw1134Labels permutation32 permutation4
    mixedMoment B raw1134step0 raw1134step0Labels = mixedMoment B raw1134step1 raw1134step1Labels := by
      have ha : raw1134step1 = raw1134step0 := by apply Matrix.ext; unfold raw1134step1 raw1134step0; decide +kernel
      have hl : raw1134step0Labels = labelEmbedding7 ∘ raw1134step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1134step0 raw1134step0Labels raw1134step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4349 node4349Labels := by rfl

theorem canonical1135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1135 raw1135Labels = mixedMoment B node927 node927Labels := by
  calc
    mixedMoment B raw1135 raw1135Labels = mixedMoment B raw1135step0 raw1135step0Labels := by
      have ha : raw1135step0 = (fun i j => raw1135 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1135step0 raw1135; decide +kernel
      have hl : raw1135step0Labels = raw1135Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1135 raw1135Labels permutation32 permutation4
    _ = mixedMoment B node927 node927Labels := by rfl

theorem canonical1136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1136 raw1136Labels = mixedMoment B node1675 node1675Labels := by
  calc
    mixedMoment B raw1136 raw1136Labels = mixedMoment B raw1136step0 raw1136step0Labels := by
      have ha : raw1136step0 = (fun i j => raw1136 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1136step0 raw1136; decide +kernel
      have hl : raw1136step0Labels = raw1136Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1136 raw1136Labels permutation32 permutation6
    mixedMoment B raw1136step0 raw1136step0Labels = mixedMoment B raw1136step1 raw1136step1Labels := by
      have ha : raw1136step1 = -raw1136step0 := by apply Matrix.ext; change ∀ i j, raw1136step1 i j = -(raw1136step0 i j); unfold raw1136step1 raw1136step0; decide +kernel
      have hl : raw1136step1Labels = raw1136step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1136step1 raw1136step1Labels = mixedMoment B raw1136step2 raw1136step2Labels := by
      have ha : raw1136step2 = raw1136step1 := by apply Matrix.ext; unfold raw1136step2 raw1136step1; decide +kernel
      have hl : raw1136step1Labels = labelEmbedding1 ∘ raw1136step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1136step1 raw1136step1Labels raw1136step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1675 node1675Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11501 raw11501Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw11501 raw11501Labels = mixedMoment B raw11501step0 raw11501step0Labels := by
      have hz : ∀ j, raw11501 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11501step0 = (fun i j => raw11501 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11501step0 raw11501; decide +kernel
      have hl : raw11501step0Labels = raw11501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11501 raw11501Labels permutation434 hz
    mixedMoment B raw11501step0 raw11501step0Labels = mixedMoment B raw11501step1 raw11501step1Labels := by
      have hz : ∀ j, raw11501step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11501step1 = (fun i j => raw11501step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11501step1 raw11501step0; decide +kernel
      have hl : raw11501step1Labels = raw11501step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11501step0 raw11501step0Labels permutation80 hz
    mixedMoment B raw11501step1 raw11501step1Labels = mixedMoment B raw11501step2 raw11501step2Labels := by
      have ha : raw11501step2 = (fun i j => raw11501step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11501step2 raw11501step1; decide +kernel
      have hl : raw11501step2Labels = raw11501step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11501step1 raw11501step1Labels permutation9 permutation7
    mixedMoment B raw11501step2 raw11501step2Labels = mixedMoment B raw11501step3 raw11501step3Labels := by
      have ha : raw11501step3 = -raw11501step2 := by apply Matrix.ext; change ∀ i j, raw11501step3 i j = -(raw11501step2 i j); unfold raw11501step3 raw11501step2; decide +kernel
      have hl : raw11501step3Labels = raw11501step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11501step3 raw11501step3Labels = mixedMoment B raw11501step4 raw11501step4Labels := by
      have ha : raw11501step4 = raw11501step3 := by apply Matrix.ext; unfold raw11501step4 raw11501step3; decide +kernel
      have hl : raw11501step3Labels = labelEmbedding10 ∘ raw11501step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11501step3 raw11501step3Labels raw11501step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

theorem canonical11512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11512 raw11512Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw11512 raw11512Labels = mixedMoment B raw11512step0 raw11512step0Labels := by
      have hz : ∀ j, raw11512 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11512step0 = (fun i j => raw11512 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11512step0 raw11512; decide +kernel
      have hl : raw11512step0Labels = raw11512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11512 raw11512Labels permutation434 hz
    _ = mixedMoment B node4835 node4835Labels := by rfl

theorem canonical11517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11517 raw11517Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw11517 raw11517Labels = mixedMoment B raw11517step0 raw11517step0Labels := by
      have hz : ∀ j, raw11517 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11517step0 = (fun i j => raw11517 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11517step0 raw11517; decide +kernel
      have hl : raw11517step0Labels = raw11517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11517 raw11517Labels permutation346 hz
    _ = mixedMoment B node4835 node4835Labels := by rfl

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

theorem canonical1158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1158 raw1158Labels = mixedMoment B node4360 node4360Labels := by
  calc
    mixedMoment B raw1158 raw1158Labels = mixedMoment B raw1158step0 raw1158step0Labels := by
      have ha : raw1158step0 = (fun i j => raw1158 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1158step0 raw1158; decide +kernel
      have hl : raw1158step0Labels = raw1158Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1158 raw1158Labels permutation8 permutation4
    mixedMoment B raw1158step0 raw1158step0Labels = mixedMoment B raw1158step1 raw1158step1Labels := by
      have ha : raw1158step1 = raw1158step0 := by apply Matrix.ext; unfold raw1158step1 raw1158step0; decide +kernel
      have hl : raw1158step0Labels = labelEmbedding7 ∘ raw1158step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1158step0 raw1158step0Labels raw1158step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4360 node4360Labels := by rfl

theorem canonical1159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1159 raw1159Labels = mixedMoment B node938 node938Labels := by
  calc
    mixedMoment B raw1159 raw1159Labels = mixedMoment B raw1159step0 raw1159step0Labels := by
      have ha : raw1159step0 = (fun i j => raw1159 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1159step0 raw1159; decide +kernel
      have hl : raw1159step0Labels = raw1159Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1159 raw1159Labels permutation8 permutation4
    _ = mixedMoment B node938 node938Labels := by rfl

theorem canonical1160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1160 raw1160Labels = mixedMoment B node1693 node1693Labels := by
  calc
    mixedMoment B raw1160 raw1160Labels = mixedMoment B raw1160step0 raw1160step0Labels := by
      have ha : raw1160step0 = (fun i j => raw1160 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1160step0 raw1160; decide +kernel
      have hl : raw1160step0Labels = raw1160Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1160 raw1160Labels permutation8 permutation6
    mixedMoment B raw1160step0 raw1160step0Labels = mixedMoment B raw1160step1 raw1160step1Labels := by
      have ha : raw1160step1 = -raw1160step0 := by apply Matrix.ext; change ∀ i j, raw1160step1 i j = -(raw1160step0 i j); unfold raw1160step1 raw1160step0; decide +kernel
      have hl : raw1160step1Labels = raw1160step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1160step1 raw1160step1Labels = mixedMoment B raw1160step2 raw1160step2Labels := by
      have ha : raw1160step2 = raw1160step1 := by apply Matrix.ext; unfold raw1160step2 raw1160step1; decide +kernel
      have hl : raw1160step1Labels = labelEmbedding1 ∘ raw1160step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1160step1 raw1160step1Labels raw1160step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1693 node1693Labels := by rfl

theorem canonical1161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1161 raw1161Labels = mixedMoment B node4361 node4361Labels := by
  calc
    mixedMoment B raw1161 raw1161Labels = mixedMoment B raw1161step0 raw1161step0Labels := by
      have ha : raw1161step0 = (fun i j => raw1161 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1161step0 raw1161; decide +kernel
      have hl : raw1161step0Labels = raw1161Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1161 raw1161Labels permutation8 permutation4
    mixedMoment B raw1161step0 raw1161step0Labels = mixedMoment B raw1161step1 raw1161step1Labels := by
      have ha : raw1161step1 = raw1161step0 := by apply Matrix.ext; unfold raw1161step1 raw1161step0; decide +kernel
      have hl : raw1161step0Labels = labelEmbedding7 ∘ raw1161step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1161step0 raw1161step0Labels raw1161step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4361 node4361Labels := by rfl

theorem canonical1162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1162 raw1162Labels = mixedMoment B node939 node939Labels := by
  calc
    mixedMoment B raw1162 raw1162Labels = mixedMoment B raw1162step0 raw1162step0Labels := by
      have ha : raw1162step0 = (fun i j => raw1162 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1162step0 raw1162; decide +kernel
      have hl : raw1162step0Labels = raw1162Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1162 raw1162Labels permutation8 permutation4
    _ = mixedMoment B node939 node939Labels := by rfl

theorem canonical1163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1163 raw1163Labels = mixedMoment B node1694 node1694Labels := by
  calc
    mixedMoment B raw1163 raw1163Labels = mixedMoment B raw1163step0 raw1163step0Labels := by
      have ha : raw1163step0 = (fun i j => raw1163 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1163step0 raw1163; decide +kernel
      have hl : raw1163step0Labels = raw1163Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1163 raw1163Labels permutation9 permutation6
    mixedMoment B raw1163step0 raw1163step0Labels = mixedMoment B raw1163step1 raw1163step1Labels := by
      have ha : raw1163step1 = -raw1163step0 := by apply Matrix.ext; change ∀ i j, raw1163step1 i j = -(raw1163step0 i j); unfold raw1163step1 raw1163step0; decide +kernel
      have hl : raw1163step1Labels = raw1163step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1163step1 raw1163step1Labels = mixedMoment B raw1163step2 raw1163step2Labels := by
      have ha : raw1163step2 = raw1163step1 := by apply Matrix.ext; unfold raw1163step2 raw1163step1; decide +kernel
      have hl : raw1163step1Labels = labelEmbedding1 ∘ raw1163step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1163step1 raw1163step1Labels raw1163step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1694 node1694Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11521 raw11521Labels = mixedMoment B node4511 node4511Labels := by
  calc
    mixedMoment B raw11521 raw11521Labels = mixedMoment B raw11521step0 raw11521step0Labels := by
      have hz : ∀ j, raw11521 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11521step0 = (fun i j => raw11521 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11521step0 raw11521; decide +kernel
      have hl : raw11521step0Labels = raw11521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11521 raw11521Labels permutation434 hz
    mixedMoment B raw11521step0 raw11521step0Labels = mixedMoment B raw11521step1 raw11521step1Labels := by
      have hz : ∀ j, raw11521step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11521step1 = (fun i j => raw11521step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11521step1 raw11521step0; decide +kernel
      have hl : raw11521step1Labels = raw11521step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11521step0 raw11521step0Labels permutation80 hz
    mixedMoment B raw11521step1 raw11521step1Labels = mixedMoment B raw11521step2 raw11521step2Labels := by
      have hz : ∀ j, raw11521step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw11521step2 = (fun i j => raw11521step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw11521step2 raw11521step1; decide +kernel
      have hl : raw11521step2Labels = raw11521step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11521step1 raw11521step1Labels permutation14 hz
    mixedMoment B raw11521step2 raw11521step2Labels = mixedMoment B raw11521step3 raw11521step3Labels := by
      have ha : raw11521step3 = (fun i j => raw11521step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11521step3 raw11521step2; decide +kernel
      have hl : raw11521step3Labels = raw11521step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11521step2 raw11521step2Labels permutation3 permutation2
    _ = mixedMoment B node4511 node4511Labels := by rfl

theorem canonical11523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11523 raw11523Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw11523 raw11523Labels = mixedMoment B raw11523step0 raw11523step0Labels := by
      have hz : ∀ j, raw11523 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11523step0 = (fun i j => raw11523 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11523step0 raw11523; decide +kernel
      have hl : raw11523step0Labels = raw11523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11523 raw11523Labels permutation434 hz
    mixedMoment B raw11523step0 raw11523step0Labels = mixedMoment B raw11523step1 raw11523step1Labels := by
      have hz : ∀ j, raw11523step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11523step1 = (fun i j => raw11523step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11523step1 raw11523step0; decide +kernel
      have hl : raw11523step1Labels = raw11523step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11523step0 raw11523step0Labels permutation56 hz
    mixedMoment B raw11523step1 raw11523step1Labels = mixedMoment B raw11523step2 raw11523step2Labels := by
      have ha : raw11523step2 = (fun i j => raw11523step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11523step2 raw11523step1; decide +kernel
      have hl : raw11523step2Labels = raw11523step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11523step1 raw11523step1Labels permutation9 permutation2
    _ = mixedMoment B node4846 node4846Labels := by rfl

theorem canonical11524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11524 raw11524Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw11524 raw11524Labels = mixedMoment B raw11524step0 raw11524step0Labels := by
      have hz : ∀ j, raw11524 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11524step0 = (fun i j => raw11524 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11524step0 raw11524; decide +kernel
      have hl : raw11524step0Labels = raw11524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11524 raw11524Labels permutation346 hz
    mixedMoment B raw11524step0 raw11524step0Labels = mixedMoment B raw11524step1 raw11524step1Labels := by
      have hz : ∀ j, raw11524step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11524step1 = (fun i j => raw11524step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11524step1 raw11524step0; decide +kernel
      have hl : raw11524step1Labels = raw11524step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11524step0 raw11524step0Labels permutation56 hz
    mixedMoment B raw11524step1 raw11524step1Labels = mixedMoment B raw11524step2 raw11524step2Labels := by
      have ha : raw11524step2 = (fun i j => raw11524step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11524step2 raw11524step1; decide +kernel
      have hl : raw11524step2Labels = raw11524step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11524step1 raw11524step1Labels permutation9 permutation2
    _ = mixedMoment B node4846 node4846Labels := by rfl

theorem canonical11525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11525 raw11525Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw11525 raw11525Labels = mixedMoment B raw11525step0 raw11525step0Labels := by
      have hz : ∀ j, raw11525 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11525step0 = (fun i j => raw11525 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11525step0 raw11525; decide +kernel
      have hl : raw11525step0Labels = raw11525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11525 raw11525Labels permutation434 hz
    mixedMoment B raw11525step0 raw11525step0Labels = mixedMoment B raw11525step1 raw11525step1Labels := by
      have hz : ∀ j, raw11525step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11525step1 = (fun i j => raw11525step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11525step1 raw11525step0; decide +kernel
      have hl : raw11525step1Labels = raw11525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11525step0 raw11525step0Labels permutation80 hz
    mixedMoment B raw11525step1 raw11525step1Labels = mixedMoment B raw11525step2 raw11525step2Labels := by
      have hz : ∀ j, raw11525step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw11525step2 = (fun i j => raw11525step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw11525step2 raw11525step1; decide +kernel
      have hl : raw11525step2Labels = raw11525step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11525step1 raw11525step1Labels permutation14 hz
    mixedMoment B raw11525step2 raw11525step2Labels = mixedMoment B raw11525step3 raw11525step3Labels := by
      have hz : ∀ i, raw11525step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw11525step3 = (fun i j => raw11525step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw11525step3 raw11525step2; decide +kernel
      have hl : raw11525step3Labels = (fun j => raw11525step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11525step2 raw11525step2Labels permutation4 hz
    mixedMoment B raw11525step3 raw11525step3Labels = mixedMoment B raw11525step4 raw11525step4Labels := by
      have ha : raw11525step4 = (fun i j => raw11525step3 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw11525step4 raw11525step3; decide +kernel
      have hl : raw11525step4Labels = raw11525step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11525step3 raw11525step3Labels permutation3 permutation0
    mixedMoment B raw11525step4 raw11525step4Labels = mixedMoment B raw11525step5 raw11525step5Labels := by
      have ha : raw11525step5 = raw11525step4 := by apply Matrix.ext; unfold raw11525step5 raw11525step4; decide +kernel
      have hl : raw11525step4Labels = labelEmbedding2 ∘ raw11525step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11525step4 raw11525step4Labels raw11525step5Labels labelEmbedding2 hl
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical11527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11527 raw11527Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw11527 raw11527Labels = mixedMoment B raw11527step0 raw11527step0Labels := by
      have hz : ∀ j, raw11527 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11527step0 = (fun i j => raw11527 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11527step0 raw11527; decide +kernel
      have hl : raw11527step0Labels = raw11527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11527 raw11527Labels permutation434 hz
    mixedMoment B raw11527step0 raw11527step0Labels = mixedMoment B raw11527step1 raw11527step1Labels := by
      have hz : ∀ j, raw11527step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11527step1 = (fun i j => raw11527step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11527step1 raw11527step0; decide +kernel
      have hl : raw11527step1Labels = raw11527step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11527step0 raw11527step0Labels permutation80 hz
    _ = mixedMoment B node4843 node4843Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4349 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4349 node4349Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node927 node927Labels + mixedMoment B node1675 node1675Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1134 singletonSmall4349
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4349) = raw1134Labels := by decide +kernel
  rw [hl, canonical1134 B hB] at h
  have hc0 : mixedMoment B raw1134 (Fin.cases (0 : Fin 2) singletonSmall4349) =
      mixedMoment B node927 node927Labels := by
    have ha : raw1134 = raw1135 := by apply Matrix.ext; unfold raw1134 raw1135; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4349 = raw1135Labels := by decide +kernel
    rw [ha, hj, canonical1135 B hB]
  have hc1 : mixedMoment B raw1134 (Fin.cases (1 : Fin 2) singletonSmall4349) =
      mixedMoment B node1675 node1675Labels := by
    have ha : raw1134 = raw1136 := by apply Matrix.ext; unfold raw1134 raw1136; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4349 = raw1136Labels := by decide +kernel
    rw [ha, hj, canonical1136 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4360 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4360 node4360Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node938 node938Labels + mixedMoment B node1693 node1693Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1158 singletonSmall4360
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4360) = raw1158Labels := by decide +kernel
  rw [hl, canonical1158 B hB] at h
  have hc0 : mixedMoment B raw1158 (Fin.cases (0 : Fin 2) singletonSmall4360) =
      mixedMoment B node938 node938Labels := by
    have ha : raw1158 = raw1159 := by apply Matrix.ext; unfold raw1158 raw1159; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4360 = raw1159Labels := by decide +kernel
    rw [ha, hj, canonical1159 B hB]
  have hc1 : mixedMoment B raw1158 (Fin.cases (1 : Fin 2) singletonSmall4360) =
      mixedMoment B node1693 node1693Labels := by
    have ha : raw1158 = raw1160 := by apply Matrix.ext; unfold raw1158 raw1160; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4360 = raw1160Labels := by decide +kernel
    rw [ha, hj, canonical1160 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4361 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4361 node4361Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node939 node939Labels + mixedMoment B node1694 node1694Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1161 singletonSmall4361
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4361) = raw1161Labels := by decide +kernel
  rw [hl, canonical1161 B hB] at h
  have hc0 : mixedMoment B raw1161 (Fin.cases (0 : Fin 2) singletonSmall4361) =
      mixedMoment B node939 node939Labels := by
    have ha : raw1161 = raw1162 := by apply Matrix.ext; unfold raw1161 raw1162; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4361 = raw1162Labels := by decide +kernel
    rw [ha, hj, canonical1162 B hB]
  have hc1 : mixedMoment B raw1161 (Fin.cases (1 : Fin 2) singletonSmall4361) =
      mixedMoment B node1694 node1694Labels := by
    have ha : raw1161 = raw1163 := by apply Matrix.ext; unfold raw1161 raw1163; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4361 = raw1163Labels := by decide +kernel
    rw [ha, hj, canonical1163 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4684 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4684 node4684Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1810 node1810Labels + mixedMoment B node2152 node2152Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1566 singletonSmall4684
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4684) = raw1566Labels := by decide +kernel
  rw [hl, canonical1566 B hB] at h
  have hc0 : mixedMoment B raw1566 (Fin.cases (0 : Fin 2) singletonSmall4684) =
      mixedMoment B node1810 node1810Labels := by
    have ha : raw1566 = raw1567 := by apply Matrix.ext; unfold raw1566 raw1567; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4684 = raw1567Labels := by decide +kernel
    rw [ha, hj, canonical1567 B hB]
  have hc1 : mixedMoment B raw1566 (Fin.cases (1 : Fin 2) singletonSmall4684) =
      mixedMoment B node2152 node2152Labels := by
    have ha : raw1566 = raw1568 := by apply Matrix.ext; unfold raw1566 raw1568; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4684 = raw1568Labels := by decide +kernel
    rw [ha, hj, canonical1568 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4692 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4692 node4692Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1818 node1818Labels + mixedMoment B node2168 node2168Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1584 singletonSmall4692
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4692) = raw1584Labels := by decide +kernel
  rw [hl, canonical1584 B hB] at h
  have hc0 : mixedMoment B raw1584 (Fin.cases (0 : Fin 2) singletonSmall4692) =
      mixedMoment B node1818 node1818Labels := by
    have ha : raw1584 = raw1585 := by apply Matrix.ext; unfold raw1584 raw1585; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4692 = raw1585Labels := by decide +kernel
    rw [ha, hj, canonical1585 B hB]
  have hc1 : mixedMoment B raw1584 (Fin.cases (1 : Fin 2) singletonSmall4692) =
      mixedMoment B node2168 node2168Labels := by
    have ha : raw1584 = raw1586 := by apply Matrix.ext; unfold raw1584 raw1586; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4692 = raw1586Labels := by decide +kernel
    rw [ha, hj, canonical1586 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4693 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4693 node4693Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1819 node1819Labels + mixedMoment B node2169 node2169Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1587 singletonSmall4693
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4693) = raw1587Labels := by decide +kernel
  rw [hl, canonical1587 B hB] at h
  have hc0 : mixedMoment B raw1587 (Fin.cases (0 : Fin 2) singletonSmall4693) =
      mixedMoment B node1819 node1819Labels := by
    have ha : raw1587 = raw1588 := by apply Matrix.ext; unfold raw1587 raw1588; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4693 = raw1588Labels := by decide +kernel
    rw [ha, hj, canonical1588 B hB]
  have hc1 : mixedMoment B raw1587 (Fin.cases (1 : Fin 2) singletonSmall4693) =
      mixedMoment B node2169 node2169Labels := by
    have ha : raw1587 = raw1589 := by apply Matrix.ext; unfold raw1587 raw1589; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4693 = raw1589Labels := by decide +kernel
    rw [ha, hj, canonical1589 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4763 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4763 node4763Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1963 node1963Labels + mixedMoment B node2174 node2174Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1692 singletonSmall4763
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4763) = raw1692Labels := by decide +kernel
  rw [hl, canonical1692 B hB] at h
  have hc0 : mixedMoment B raw1692 (Fin.cases (0 : Fin 2) singletonSmall4763) =
      mixedMoment B node1963 node1963Labels := by
    have ha : raw1692 = raw1693 := by apply Matrix.ext; unfold raw1692 raw1693; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4763 = raw1693Labels := by decide +kernel
    rw [ha, hj, canonical1693 B hB]
  have hc1 : mixedMoment B raw1692 (Fin.cases (1 : Fin 2) singletonSmall4763) =
      mixedMoment B node2174 node2174Labels := by
    have ha : raw1692 = raw1694 := by apply Matrix.ext; unfold raw1692 raw1694; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4763 = raw1694Labels := by decide +kernel
    rw [ha, hj, canonical1694 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4769 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4769 node4769Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1969 node1969Labels + mixedMoment B node2185 node2185Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1704 singletonSmall4769
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4769) = raw1704Labels := by decide +kernel
  rw [hl, canonical1704 B hB] at h
  have hc0 : mixedMoment B raw1704 (Fin.cases (0 : Fin 2) singletonSmall4769) =
      mixedMoment B node1969 node1969Labels := by
    have ha : raw1704 = raw1705 := by apply Matrix.ext; unfold raw1704 raw1705; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4769 = raw1705Labels := by decide +kernel
    rw [ha, hj, canonical1705 B hB]
  have hc1 : mixedMoment B raw1704 (Fin.cases (1 : Fin 2) singletonSmall4769) =
      mixedMoment B node2185 node2185Labels := by
    have ha : raw1704 = raw1706 := by apply Matrix.ext; unfold raw1704 raw1706; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4769 = raw1706Labels := by decide +kernel
    rw [ha, hj, canonical1706 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4770 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4770 node4770Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1970 node1970Labels + mixedMoment B node2186 node2186Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1707 singletonSmall4770
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4770) = raw1707Labels := by decide +kernel
  rw [hl, canonical1707 B hB] at h
  have hc0 : mixedMoment B raw1707 (Fin.cases (0 : Fin 2) singletonSmall4770) =
      mixedMoment B node1970 node1970Labels := by
    have ha : raw1707 = raw1708 := by apply Matrix.ext; unfold raw1707 raw1708; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4770 = raw1708Labels := by decide +kernel
    rw [ha, hj, canonical1708 B hB]
  have hc1 : mixedMoment B raw1707 (Fin.cases (1 : Fin 2) singletonSmall4770) =
      mixedMoment B node2186 node2186Labels := by
    have ha : raw1707 = raw1709 := by apply Matrix.ext; unfold raw1707 raw1709; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4770 = raw1709Labels := by decide +kernel
    rw [ha, hj, canonical1709 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4835 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4835 node4835Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2054 node2054Labels + mixedMoment B node2206 node2206Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1767 singletonSmall4835
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4835) = raw1767Labels := by decide +kernel
  rw [hl, canonical1767 B hB] at h
  have hc0 : mixedMoment B raw1767 (Fin.cases (0 : Fin 2) singletonSmall4835) =
      mixedMoment B node2054 node2054Labels := by
    have ha : raw1767 = raw1768 := by apply Matrix.ext; unfold raw1767 raw1768; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4835 = raw1768Labels := by decide +kernel
    rw [ha, hj, canonical1768 B hB]
  have hc1 : mixedMoment B raw1767 (Fin.cases (1 : Fin 2) singletonSmall4835) =
      mixedMoment B node2206 node2206Labels := by
    have ha : raw1767 = raw1769 := by apply Matrix.ext; unfold raw1767 raw1769; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4835 = raw1769Labels := by decide +kernel
    rw [ha, hj, canonical1769 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4843 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4843 node4843Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2062 node2062Labels + mixedMoment B node2230 node2230Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1773 singletonSmall4843
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4843) = raw1773Labels := by decide +kernel
  rw [hl, canonical1773 B hB] at h
  have hc0 : mixedMoment B raw1773 (Fin.cases (0 : Fin 2) singletonSmall4843) =
      mixedMoment B node2062 node2062Labels := by
    have ha : raw1773 = raw1774 := by apply Matrix.ext; unfold raw1773 raw1774; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4843 = raw1774Labels := by decide +kernel
    rw [ha, hj, canonical1774 B hB]
  have hc1 : mixedMoment B raw1773 (Fin.cases (1 : Fin 2) singletonSmall4843) =
      mixedMoment B node2230 node2230Labels := by
    have ha : raw1773 = raw1775 := by apply Matrix.ext; unfold raw1773 raw1775; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4843 = raw1775Labels := by decide +kernel
    rw [ha, hj, canonical1775 B hB]
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

theorem singleton5238 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5238 node5238Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2686 node2686Labels + mixedMoment B node3397 node3397Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2256 singletonSmall5238
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5238) = raw2256Labels := by decide +kernel
  rw [hl, canonical2256 B hB] at h
  have hc0 : mixedMoment B raw2256 (Fin.cases (0 : Fin 2) singletonSmall5238) =
      mixedMoment B node2686 node2686Labels := by
    have ha : raw2256 = raw2257 := by apply Matrix.ext; unfold raw2256 raw2257; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5238 = raw2257Labels := by decide +kernel
    rw [ha, hj, canonical2257 B hB]
  have hc1 : mixedMoment B raw2256 (Fin.cases (1 : Fin 2) singletonSmall5238) =
      mixedMoment B node3397 node3397Labels := by
    have ha : raw2256 = raw2258 := by apply Matrix.ext; unfold raw2256 raw2258; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5238 = raw2258Labels := by decide +kernel
    rw [ha, hj, canonical2258 B hB]
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

theorem singleton5248 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5248 node5248Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2705 node2705Labels + mixedMoment B node3498 node3498Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2265 singletonSmall5248
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5248) = raw2265Labels := by decide +kernel
  rw [hl, canonical2265 B hB] at h
  have hc0 : mixedMoment B raw2265 (Fin.cases (0 : Fin 2) singletonSmall5248) =
      mixedMoment B node2705 node2705Labels := by
    have ha : raw2265 = raw2266 := by apply Matrix.ext; unfold raw2265 raw2266; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5248 = raw2266Labels := by decide +kernel
    rw [ha, hj, canonical2266 B hB]
  have hc1 : mixedMoment B raw2265 (Fin.cases (1 : Fin 2) singletonSmall5248) =
      mixedMoment B node3498 node3498Labels := by
    have ha : raw2265 = raw2267 := by apply Matrix.ext; unfold raw2265 raw2267; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5248 = raw2267Labels := by decide +kernel
    rw [ha, hj, canonical2267 B hB]
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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node927 node927Labels = Sparse.eval nodeValue927 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 927) = mixedMoment B node927 node927Labels := rfl
  simpa [nodeValue927, Sparse.eval] using hc.symm

theorem sound938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node938 node938Labels = Sparse.eval nodeValue938 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 938) = mixedMoment B node938 node938Labels := rfl
  simpa [nodeValue938, Sparse.eval] using hc.symm

theorem sound939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node939 node939Labels = Sparse.eval nodeValue939 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 939) = mixedMoment B node939 node939Labels := rfl
  simpa [nodeValue939, Sparse.eval] using hc.symm

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

theorem sound1675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1675 node1675Labels = Sparse.eval nodeValue1675 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1675) = mixedMoment B node1675 node1675Labels := rfl
  simpa [nodeValue1675, Sparse.eval] using hc.symm

theorem sound1693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1693 node1693Labels = Sparse.eval nodeValue1693 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1693) = mixedMoment B node1693 node1693Labels := rfl
  simpa [nodeValue1693, Sparse.eval] using hc.symm

theorem sound1694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1694 node1694Labels = Sparse.eval nodeValue1694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1694) = mixedMoment B node1694 node1694Labels := rfl
  simpa [nodeValue1694, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1810 node1810Labels = Sparse.eval nodeValue1810 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1810) = mixedMoment B node1810 node1810Labels := rfl
  simpa [nodeValue1810, Sparse.eval] using hc.symm

theorem sound1818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1818 node1818Labels = Sparse.eval nodeValue1818 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1818) = mixedMoment B node1818 node1818Labels := rfl
  simpa [nodeValue1818, Sparse.eval] using hc.symm

theorem sound1819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1819 node1819Labels = Sparse.eval nodeValue1819 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1819) = mixedMoment B node1819 node1819Labels := rfl
  simpa [nodeValue1819, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1963 node1963Labels = Sparse.eval nodeValue1963 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1963) = mixedMoment B node1963 node1963Labels := rfl
  simpa [nodeValue1963, Sparse.eval] using hc.symm

theorem sound1969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1969 node1969Labels = Sparse.eval nodeValue1969 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1969) = mixedMoment B node1969 node1969Labels := rfl
  simpa [nodeValue1969, Sparse.eval] using hc.symm

theorem sound1970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1970 node1970Labels = Sparse.eval nodeValue1970 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1970) = mixedMoment B node1970 node1970Labels := rfl
  simpa [nodeValue1970, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2054 node2054Labels = Sparse.eval nodeValue2054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2054) = mixedMoment B node2054 node2054Labels := rfl
  simpa [nodeValue2054, Sparse.eval] using hc.symm

theorem sound2062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2062 node2062Labels = Sparse.eval nodeValue2062 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2062) = mixedMoment B node2062 node2062Labels := rfl
  simpa [nodeValue2062, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2152 node2152Labels = Sparse.eval nodeValue2152 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2152) = mixedMoment B node2152 node2152Labels := rfl
  simpa [nodeValue2152, Sparse.eval] using hc.symm

theorem sound2168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2168 node2168Labels = Sparse.eval nodeValue2168 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2168) = mixedMoment B node2168 node2168Labels := rfl
  simpa [nodeValue2168, Sparse.eval] using hc.symm

theorem sound2169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2169 node2169Labels = Sparse.eval nodeValue2169 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2169) = mixedMoment B node2169 node2169Labels := rfl
  simpa [nodeValue2169, Sparse.eval] using hc.symm

theorem sound2174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2174 node2174Labels = Sparse.eval nodeValue2174 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2174) = mixedMoment B node2174 node2174Labels := rfl
  simpa [nodeValue2174, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2185 node2185Labels = Sparse.eval nodeValue2185 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2185) = mixedMoment B node2185 node2185Labels := rfl
  simpa [nodeValue2185, Sparse.eval] using hc.symm

theorem sound2186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2186 node2186Labels = Sparse.eval nodeValue2186 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2186) = mixedMoment B node2186 node2186Labels := rfl
  simpa [nodeValue2186, Sparse.eval] using hc.symm

theorem sound2206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2206 node2206Labels = Sparse.eval nodeValue2206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2206) = mixedMoment B node2206 node2206Labels := rfl
  simpa [nodeValue2206, Sparse.eval] using hc.symm

theorem sound2230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2230 node2230Labels = Sparse.eval nodeValue2230 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2230) = mixedMoment B node2230 node2230Labels := rfl
  simpa [nodeValue2230, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2686 node2686Labels = Sparse.eval nodeValue2686 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2686) = mixedMoment B node2686 node2686Labels := rfl
  simpa [nodeValue2686, Sparse.eval] using hc.symm

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

theorem sound2705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2705 node2705Labels = Sparse.eval nodeValue2705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2705) = mixedMoment B node2705 node2705Labels := rfl
  simpa [nodeValue2705, Sparse.eval] using hc.symm

theorem sound2743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2743 node2743Labels = Sparse.eval nodeValue2743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2743) = mixedMoment B node2743 node2743Labels := rfl
  simpa [nodeValue2743, Sparse.eval] using hc.symm

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

theorem sound3397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3397 node3397Labels = Sparse.eval nodeValue3397 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3397) = mixedMoment B node3397 node3397Labels := rfl
  simpa [nodeValue3397, Sparse.eval] using hc.symm

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

theorem sound3498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3498 node3498Labels = Sparse.eval nodeValue3498 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3498) = mixedMoment B node3498 node3498Labels := rfl
  simpa [nodeValue3498, Sparse.eval] using hc.symm

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

theorem sound3548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3548 node3548Labels = Sparse.eval nodeValue3548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3548) = mixedMoment B node3548 node3548Labels := rfl
  simpa [nodeValue3548, Sparse.eval] using hc.symm

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

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

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

theorem sound4349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4349 node4349Labels = Sparse.eval nodeValue4349 (mixedVector B) := by
  have h := singleton4349 B _hB
  rw [sound927 B _hB _hF, sound1675 B _hB _hF] at h
  norm_num [nodeValue4349, nodeValue927, nodeValue1675, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4360 node4360Labels = Sparse.eval nodeValue4360 (mixedVector B) := by
  have h := singleton4360 B _hB
  rw [sound938 B _hB _hF, sound1693 B _hB _hF] at h
  norm_num [nodeValue4360, nodeValue938, nodeValue1693, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4361 node4361Labels = Sparse.eval nodeValue4361 (mixedVector B) := by
  have h := singleton4361 B _hB
  rw [sound939 B _hB _hF, sound1694 B _hB _hF] at h
  norm_num [nodeValue4361, nodeValue939, nodeValue1694, Sparse.eval] at h ⊢
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

theorem zero4511 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4511 node4511Labels = 0 := by
  exact mixedMoment_order_one B hB node4511 node4511Labels 1
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

theorem sound4511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4511 node4511Labels = Sparse.eval nodeValue4511 (mixedVector B) := by
  simpa only [nodeValue4511, Sparse.eval_nil] using zero4511 B _hB _hF

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

theorem sound4684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4684 node4684Labels = Sparse.eval nodeValue4684 (mixedVector B) := by
  have h := singleton4684 B _hB
  rw [sound1810 B _hB _hF, sound2152 B _hB _hF] at h
  norm_num [nodeValue4684, nodeValue1810, nodeValue2152, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4692 node4692Labels = Sparse.eval nodeValue4692 (mixedVector B) := by
  have h := singleton4692 B _hB
  rw [sound1818 B _hB _hF, sound2168 B _hB _hF] at h
  norm_num [nodeValue4692, nodeValue1818, nodeValue2168, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4693 node4693Labels = Sparse.eval nodeValue4693 (mixedVector B) := by
  have h := singleton4693 B _hB
  rw [sound1819 B _hB _hF, sound2169 B _hB _hF] at h
  norm_num [nodeValue4693, nodeValue1819, nodeValue2169, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4763 node4763Labels = Sparse.eval nodeValue4763 (mixedVector B) := by
  have h := singleton4763 B _hB
  rw [sound1963 B _hB _hF, sound2174 B _hB _hF] at h
  norm_num [nodeValue4763, nodeValue1963, nodeValue2174, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4769 node4769Labels = Sparse.eval nodeValue4769 (mixedVector B) := by
  have h := singleton4769 B _hB
  rw [sound1969 B _hB _hF, sound2185 B _hB _hF] at h
  norm_num [nodeValue4769, nodeValue1969, nodeValue2185, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4770 node4770Labels = Sparse.eval nodeValue4770 (mixedVector B) := by
  have h := singleton4770 B _hB
  rw [sound1970 B _hB _hF, sound2186 B _hB _hF] at h
  norm_num [nodeValue4770, nodeValue1970, nodeValue2186, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4834 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4834 node4834Labels = 0 := by
  exact mixedMoment_order_one B hB node4834 node4834Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4841 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4841 node4841Labels = 0 := by
  exact mixedMoment_order_one B hB node4841 node4841Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4846 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4846 node4846Labels = 0 := by
  exact mixedMoment_order_one B hB node4846 node4846Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4834 node4834Labels = Sparse.eval nodeValue4834 (mixedVector B) := by
  simpa only [nodeValue4834, Sparse.eval_nil] using zero4834 B _hB _hF

theorem sound4835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4835 node4835Labels = Sparse.eval nodeValue4835 (mixedVector B) := by
  have h := singleton4835 B _hB
  rw [sound2054 B _hB _hF, sound2206 B _hB _hF] at h
  norm_num [nodeValue4835, nodeValue2054, nodeValue2206, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4841 node4841Labels = Sparse.eval nodeValue4841 (mixedVector B) := by
  simpa only [nodeValue4841, Sparse.eval_nil] using zero4841 B _hB _hF

theorem sound4843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4843 node4843Labels = Sparse.eval nodeValue4843 (mixedVector B) := by
  have h := singleton4843 B _hB
  rw [sound2062 B _hB _hF, sound2230 B _hB _hF] at h
  norm_num [nodeValue4843, nodeValue2062, nodeValue2230, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4846 node4846Labels = Sparse.eval nodeValue4846 (mixedVector B) := by
  simpa only [nodeValue4846, Sparse.eval_nil] using zero4846 B _hB _hF

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

theorem sound4901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4901 node4901Labels = Sparse.eval nodeValue4901 (mixedVector B) := by
  simpa only [nodeValue4901, Sparse.eval_nil] using zero4901 B _hB _hF

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

theorem sound5238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5238 node5238Labels = Sparse.eval nodeValue5238 (mixedVector B) := by
  have h := singleton5238 B _hB
  rw [sound2686 B _hB _hF, sound3397 B _hB _hF] at h
  norm_num [nodeValue5238, nodeValue2686, nodeValue3397, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5248 node5248Labels = Sparse.eval nodeValue5248 (mixedVector B) := by
  have h := singleton5248 B _hB
  rw [sound2705 B _hB _hF, sound3498 B _hB _hF] at h
  norm_num [nodeValue5248, nodeValue2705, nodeValue3498, Sparse.eval] at h ⊢
  linarith only [h]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources71
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2302 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2302 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2302 + difference 0 1) (sourceB2302 + difference 1 0) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2302 + difference 0 1) (sourceB2302 + difference 1 0) sourceC2302) = raw31728 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31728; decide +kernel
    rw [ha]
    exact (canonical31728 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2302 + difference 0 2) (sourceB2302 + difference 2 0) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA2302 + difference 0 2) (sourceB2302 + difference 2 0) sourceC2302) = raw31729 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31729; decide +kernel
    rw [ha]
    exact (canonical31729 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2302 + difference 0 3) (sourceB2302 + difference 3 0) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA2302 + difference 0 3) (sourceB2302 + difference 3 0) sourceC2302) = raw31730 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31730; decide +kernel
    rw [ha]
    exact (canonical31730 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2302 + difference 0 4) (sourceB2302 + difference 4 0) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA2302 + difference 0 4) (sourceB2302 + difference 4 0) sourceC2302) = raw11501 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw11501; decide +kernel
    rw [ha]
    exact (canonical11501 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2302 + difference 0 5) (sourceB2302 + difference 5 0) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA2302 + difference 0 5) (sourceB2302 + difference 5 0) sourceC2302) = raw31731 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31731; decide +kernel
    rw [ha]
    exact (canonical31731 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2302 + difference 1 0) (sourceB2302 + difference 0 1) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA2302 + difference 1 0) (sourceB2302 + difference 0 1) sourceC2302) = raw11521 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw11521; decide +kernel
    rw [ha]
    exact (canonical11521 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2302 + difference 1 2) (sourceB2302 + difference 2 1) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2302 + difference 1 2) (sourceB2302 + difference 2 1) sourceC2302) = raw11523 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw11523; decide +kernel
    rw [ha]
    exact (canonical11523 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2302 + difference 1 3) (sourceB2302 + difference 3 1) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2302 + difference 1 3) (sourceB2302 + difference 3 1) sourceC2302) = raw11524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw11524; decide +kernel
    rw [ha]
    exact (canonical11524 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2302 + difference 1 4) (sourceB2302 + difference 4 1) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4901) := by
    have ha : (tripleCharges (sourceA2302 + difference 1 4) (sourceB2302 + difference 4 1) sourceC2302) = raw21634 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw21634; decide +kernel
    rw [ha]
    exact (canonical21634 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2302 + difference 1 5) (sourceB2302 + difference 5 1) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA2302 + difference 1 5) (sourceB2302 + difference 5 1) sourceC2302) = raw11525 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw11525; decide +kernel
    rw [ha]
    exact (canonical11525 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2302 + difference 2 0) (sourceB2302 + difference 0 2) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA2302 + difference 2 0) (sourceB2302 + difference 0 2) sourceC2302) = raw23523 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw23523; decide +kernel
    rw [ha]
    exact (canonical23523 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2302 + difference 2 1) (sourceB2302 + difference 1 2) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4684) := by
    have ha : (tripleCharges (sourceA2302 + difference 2 1) (sourceB2302 + difference 1 2) sourceC2302) = raw31732 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31732; decide +kernel
    rw [ha]
    exact (canonical31732 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2302 + difference 2 3) (sourceB2302 + difference 3 2) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4763) := by
    have ha : (tripleCharges (sourceA2302 + difference 2 3) (sourceB2302 + difference 3 2) sourceC2302) = raw31733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31733; decide +kernel
    rw [ha]
    exact (canonical31733 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2302 + difference 2 4) (sourceB2302 + difference 4 2) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2302 + difference 2 4) (sourceB2302 + difference 4 2) sourceC2302) = raw11512 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw11512; decide +kernel
    rw [ha]
    exact (canonical11512 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2302 + difference 2 5) (sourceB2302 + difference 5 2) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2302 + difference 2 5) (sourceB2302 + difference 5 2) sourceC2302) = raw31734 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31734; decide +kernel
    rw [ha]
    exact (canonical31734 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2302 + difference 3 0) (sourceB2302 + difference 0 3) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA2302 + difference 3 0) (sourceB2302 + difference 0 3) sourceC2302) = raw23527 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw23527; decide +kernel
    rw [ha]
    exact (canonical23527 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2302 + difference 3 1) (sourceB2302 + difference 1 3) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4684) := by
    have ha : (tripleCharges (sourceA2302 + difference 3 1) (sourceB2302 + difference 1 3) sourceC2302) = raw31735 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31735; decide +kernel
    rw [ha]
    exact (canonical31735 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2302 + difference 3 2) (sourceB2302 + difference 2 3) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4763) := by
    have ha : (tripleCharges (sourceA2302 + difference 3 2) (sourceB2302 + difference 2 3) sourceC2302) = raw31736 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31736; decide +kernel
    rw [ha]
    exact (canonical31736 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2302 + difference 3 4) (sourceB2302 + difference 4 3) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2302 + difference 3 4) (sourceB2302 + difference 4 3) sourceC2302) = raw11517 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw11517; decide +kernel
    rw [ha]
    exact (canonical11517 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2302 + difference 3 5) (sourceB2302 + difference 5 3) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2302 + difference 3 5) (sourceB2302 + difference 5 3) sourceC2302) = raw31737 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31737; decide +kernel
    rw [ha]
    exact (canonical31737 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2302 + difference 4 0) (sourceB2302 + difference 0 4) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4360) := by
    have ha : (tripleCharges (sourceA2302 + difference 4 0) (sourceB2302 + difference 0 4) sourceC2302) = raw23531 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw23531; decide +kernel
    rw [ha]
    exact (canonical23531 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2302 + difference 4 1) (sourceB2302 + difference 1 4) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4692) := by
    have ha : (tripleCharges (sourceA2302 + difference 4 1) (sourceB2302 + difference 1 4) sourceC2302) = raw31738 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31738; decide +kernel
    rw [ha]
    exact (canonical31738 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2302 + difference 4 2) (sourceB2302 + difference 2 4) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4769) := by
    have ha : (tripleCharges (sourceA2302 + difference 4 2) (sourceB2302 + difference 2 4) sourceC2302) = raw31739 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31739; decide +kernel
    rw [ha]
    exact (canonical31739 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2302 + difference 4 3) (sourceB2302 + difference 3 4) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4769) := by
    have ha : (tripleCharges (sourceA2302 + difference 4 3) (sourceB2302 + difference 3 4) sourceC2302) = raw31740 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31740; decide +kernel
    rw [ha]
    exact (canonical31740 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2302 + difference 4 5) (sourceB2302 + difference 5 4) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA2302 + difference 4 5) (sourceB2302 + difference 5 4) sourceC2302) = raw31741 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31741; decide +kernel
    rw [ha]
    exact (canonical31741 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2302 + difference 5 0) (sourceB2302 + difference 0 5) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4361) := by
    have ha : (tripleCharges (sourceA2302 + difference 5 0) (sourceB2302 + difference 0 5) sourceC2302) = raw21648 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw21648; decide +kernel
    rw [ha]
    exact (canonical21648 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2302 + difference 5 1) (sourceB2302 + difference 1 5) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4693) := by
    have ha : (tripleCharges (sourceA2302 + difference 5 1) (sourceB2302 + difference 1 5) sourceC2302) = raw31742 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31742; decide +kernel
    rw [ha]
    exact (canonical31742 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2302 + difference 5 2) (sourceB2302 + difference 2 5) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4770) := by
    have ha : (tripleCharges (sourceA2302 + difference 5 2) (sourceB2302 + difference 2 5) sourceC2302) = raw31743 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31743; decide +kernel
    rw [ha]
    exact (canonical31743 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2302 + difference 5 3) (sourceB2302 + difference 3 5) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4770) := by
    have ha : (tripleCharges (sourceA2302 + difference 5 3) (sourceB2302 + difference 3 5) sourceC2302) = raw31744 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31744; decide +kernel
    rw [ha]
    exact (canonical31744 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2302 + difference 5 4) (sourceB2302 + difference 4 5) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA2302 + difference 5 4) (sourceB2302 + difference 4 5) sourceC2302) = raw11527 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw11527; decide +kernel
    rw [ha]
    exact (canonical11527 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2302 sourceB2302 sourceC2302
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2302, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic117
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1877 : Integer.Sparse.reindex keyMap MixedData.row1877 = numericRow1877 := by decide +kernel

theorem numericCheck1877 (x : Master → ℝ) : Integer.Sparse.eval numericRow1877 x =
    (4 : ℝ) * reducedSource1877 x := by
  norm_num [numericRow1877, reducedSource1877, Integer.Sparse.eval, Sparse.eval, nodeValue4084, nodeValue4349, nodeValue4360, nodeValue4361, nodeValue4511, nodeValue4684, nodeValue4692, nodeValue4693, nodeValue4763, nodeValue4769, nodeValue4770, nodeValue4834, nodeValue4835, nodeValue4841, nodeValue4843, nodeValue4846, nodeValue4901, nodeValue5238, nodeValue5248, nodeValue5274, nodeValue5275] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows117
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1877 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1877 (mixedVector B) = 0 := by
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4349 : mixedVector B (Sum.inr 4349) = Sparse.eval nodeValue4349 (mixedVector B) := by
    change mixedMoment B node4349 node4349Labels = _
    exact sound4349 B hB hF
  have h4360 : mixedVector B (Sum.inr 4360) = Sparse.eval nodeValue4360 (mixedVector B) := by
    change mixedMoment B node4360 node4360Labels = _
    exact sound4360 B hB hF
  have h4361 : mixedVector B (Sum.inr 4361) = Sparse.eval nodeValue4361 (mixedVector B) := by
    change mixedMoment B node4361 node4361Labels = _
    exact sound4361 B hB hF
  have h4511 : mixedVector B (Sum.inr 4511) = Sparse.eval nodeValue4511 (mixedVector B) := by
    change mixedMoment B node4511 node4511Labels = _
    exact sound4511 B hB hF
  have h4684 : mixedVector B (Sum.inr 4684) = Sparse.eval nodeValue4684 (mixedVector B) := by
    change mixedMoment B node4684 node4684Labels = _
    exact sound4684 B hB hF
  have h4692 : mixedVector B (Sum.inr 4692) = Sparse.eval nodeValue4692 (mixedVector B) := by
    change mixedMoment B node4692 node4692Labels = _
    exact sound4692 B hB hF
  have h4693 : mixedVector B (Sum.inr 4693) = Sparse.eval nodeValue4693 (mixedVector B) := by
    change mixedMoment B node4693 node4693Labels = _
    exact sound4693 B hB hF
  have h4763 : mixedVector B (Sum.inr 4763) = Sparse.eval nodeValue4763 (mixedVector B) := by
    change mixedMoment B node4763 node4763Labels = _
    exact sound4763 B hB hF
  have h4769 : mixedVector B (Sum.inr 4769) = Sparse.eval nodeValue4769 (mixedVector B) := by
    change mixedMoment B node4769 node4769Labels = _
    exact sound4769 B hB hF
  have h4770 : mixedVector B (Sum.inr 4770) = Sparse.eval nodeValue4770 (mixedVector B) := by
    change mixedMoment B node4770 node4770Labels = _
    exact sound4770 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4841 : mixedVector B (Sum.inr 4841) = Sparse.eval nodeValue4841 (mixedVector B) := by
    change mixedMoment B node4841 node4841Labels = _
    exact sound4841 B hB hF
  have h4843 : mixedVector B (Sum.inr 4843) = Sparse.eval nodeValue4843 (mixedVector B) := by
    change mixedMoment B node4843 node4843Labels = _
    exact sound4843 B hB hF
  have h4846 : mixedVector B (Sum.inr 4846) = Sparse.eval nodeValue4846 (mixedVector B) := by
    change mixedMoment B node4846 node4846Labels = _
    exact sound4846 B hB hF
  have h4901 : mixedVector B (Sum.inr 4901) = Sparse.eval nodeValue4901 (mixedVector B) := by
    change mixedMoment B node4901 node4901Labels = _
    exact sound4901 B hB hF
  have h5238 : mixedVector B (Sum.inr 5238) = Sparse.eval nodeValue5238 (mixedVector B) := by
    change mixedMoment B node5238 node5238Labels = _
    exact sound5238 B hB hF
  have h5248 : mixedVector B (Sum.inr 5248) = Sparse.eval nodeValue5248 (mixedVector B) := by
    change mixedMoment B node5248 node5248Labels = _
    exact sound5248 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  have h5275 : mixedVector B (Sum.inr 5275) = Sparse.eval nodeValue5275 (mixedVector B) := by
    change mixedMoment B node5275 node5275Labels = _
    exact sound5275 B hB hF
  simpa only [sourceForm2302, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4084, h4349, h4360, h4361, h4511, h4684, h4692, h4693, h4763, h4769, h4770, h4834, h4835, h4841, h4843, h4846, h4901, h5238, h5248, h5274, h5275, reducedSource1877] using sourceEq2302 B hB

theorem rowSound1877_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1877 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1877, numericCheck1877, reducedZero1877 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877_e_oai
