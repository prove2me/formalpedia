-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1233_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T20:17:11.555129+00:00
-- url     : https://prove2.me/submissions/dd7dff5a-fe78-42bc-964d-92b13762fd81

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E117
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

theorem canonical1305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1305 raw1305Labels = mixedMoment B node4507 node4507Labels := by
  calc
    mixedMoment B raw1305 raw1305Labels = mixedMoment B raw1305step0 raw1305step0Labels := by
      have ha : raw1305step0 = (fun i j => raw1305 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1305step0 raw1305; decide +kernel
      have hl : raw1305step0Labels = raw1305Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1305 raw1305Labels permutation2 permutation4
    mixedMoment B raw1305step0 raw1305step0Labels = mixedMoment B raw1305step1 raw1305step1Labels := by
      have ha : raw1305step1 = raw1305step0 := by apply Matrix.ext; unfold raw1305step1 raw1305step0; decide +kernel
      have hl : raw1305step0Labels = labelEmbedding7 ∘ raw1305step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1305step0 raw1305step0Labels raw1305step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4507 node4507Labels := by rfl

theorem canonical1306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1306 raw1306Labels = mixedMoment B node1091 node1091Labels := by
  calc
    mixedMoment B raw1306 raw1306Labels = mixedMoment B raw1306step0 raw1306step0Labels := by
      have ha : raw1306step0 = (fun i j => raw1306 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1306step0 raw1306; decide +kernel
      have hl : raw1306step0Labels = raw1306Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1306 raw1306Labels permutation2 permutation4
    _ = mixedMoment B node1091 node1091Labels := by rfl

theorem canonical1307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1307 raw1307Labels = mixedMoment B node1756 node1756Labels := by
  calc
    mixedMoment B raw1307 raw1307Labels = mixedMoment B raw1307step0 raw1307step0Labels := by
      have ha : raw1307step0 = (fun i j => raw1307 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1307step0 raw1307; decide +kernel
      have hl : raw1307step0Labels = raw1307Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1307 raw1307Labels permutation3 permutation6
    mixedMoment B raw1307step0 raw1307step0Labels = mixedMoment B raw1307step1 raw1307step1Labels := by
      have ha : raw1307step1 = -raw1307step0 := by apply Matrix.ext; change ∀ i j, raw1307step1 i j = -(raw1307step0 i j); unfold raw1307step1 raw1307step0; decide +kernel
      have hl : raw1307step1Labels = raw1307step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1307step1 raw1307step1Labels = mixedMoment B raw1307step2 raw1307step2Labels := by
      have ha : raw1307step2 = raw1307step1 := by apply Matrix.ext; unfold raw1307step2 raw1307step1; decide +kernel
      have hl : raw1307step1Labels = labelEmbedding1 ∘ raw1307step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1307step1 raw1307step1Labels raw1307step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1756 node1756Labels := by rfl

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

theorem canonical20434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20434 raw20434Labels = mixedMoment B node4505 node4505Labels := by
  calc
    mixedMoment B raw20434 raw20434Labels = mixedMoment B raw20434step0 raw20434step0Labels := by
      have hz : ∀ j, raw20434 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20434step0 = (fun i j => raw20434 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20434step0 raw20434; decide +kernel
      have hl : raw20434step0Labels = raw20434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20434 raw20434Labels permutation434 hz
    mixedMoment B raw20434step0 raw20434step0Labels = mixedMoment B raw20434step1 raw20434step1Labels := by
      have hz : ∀ j, raw20434step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20434step1 = (fun i j => raw20434step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20434step1 raw20434step0; decide +kernel
      have hl : raw20434step1Labels = raw20434step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20434step0 raw20434step0Labels permutation80 hz
    mixedMoment B raw20434step1 raw20434step1Labels = mixedMoment B raw20434step2 raw20434step2Labels := by
      have hz : ∀ j, raw20434step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20434step2 = (fun i j => raw20434step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20434step2 raw20434step1; decide +kernel
      have hl : raw20434step2Labels = raw20434step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20434step1 raw20434step1Labels permutation14 hz
    mixedMoment B raw20434step2 raw20434step2Labels = mixedMoment B raw20434step3 raw20434step3Labels := by
      have ha : raw20434step3 = (fun i j => raw20434step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20434step3 raw20434step2; decide +kernel
      have hl : raw20434step3Labels = raw20434step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20434step2 raw20434step2Labels permutation2 permutation6
    mixedMoment B raw20434step3 raw20434step3Labels = mixedMoment B raw20434step4 raw20434step4Labels := by
      have ha : raw20434step4 = raw20434step3 := by apply Matrix.ext; unfold raw20434step4 raw20434step3; decide +kernel
      have hl : raw20434step3Labels = labelEmbedding9 ∘ raw20434step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20434step3 raw20434step3Labels raw20434step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4505 node4505Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20803 raw20803Labels = mixedMoment B node4428 node4428Labels := by
  calc
    mixedMoment B raw20803 raw20803Labels = mixedMoment B raw20803step0 raw20803step0Labels := by
      have hz : ∀ j, raw20803 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20803step0 = (fun i j => raw20803 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20803step0 raw20803; decide +kernel
      have hl : raw20803step0Labels = raw20803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20803 raw20803Labels permutation346 hz
    mixedMoment B raw20803step0 raw20803step0Labels = mixedMoment B raw20803step1 raw20803step1Labels := by
      have hz : ∀ j, raw20803step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20803step1 = (fun i j => raw20803step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20803step1 raw20803step0; decide +kernel
      have hl : raw20803step1Labels = raw20803step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20803step0 raw20803step0Labels permutation56 hz
    mixedMoment B raw20803step1 raw20803step1Labels = mixedMoment B raw20803step2 raw20803step2Labels := by
      have ha : raw20803step2 = (fun i j => raw20803step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20803step2 raw20803step1; decide +kernel
      have hl : raw20803step2Labels = raw20803step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20803step1 raw20803step1Labels permutation8 permutation6
    mixedMoment B raw20803step2 raw20803step2Labels = mixedMoment B raw20803step3 raw20803step3Labels := by
      have ha : raw20803step3 = raw20803step2 := by apply Matrix.ext; unfold raw20803step3 raw20803step2; decide +kernel
      have hl : raw20803step2Labels = labelEmbedding9 ∘ raw20803step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20803step2 raw20803step2Labels raw20803step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4428 node4428Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical166
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21308 raw21308Labels = mixedMoment B node4270 node4270Labels := by
  calc
    mixedMoment B raw21308 raw21308Labels = mixedMoment B raw21308step0 raw21308step0Labels := by
      have hz : ∀ j, raw21308 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21308step0 = (fun i j => raw21308 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21308step0 raw21308; decide +kernel
      have hl : raw21308step0Labels = raw21308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21308 raw21308Labels permutation434 hz
    mixedMoment B raw21308step0 raw21308step0Labels = mixedMoment B raw21308step1 raw21308step1Labels := by
      have hz : ∀ j, raw21308step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21308step1 = (fun i j => raw21308step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21308step1 raw21308step0; decide +kernel
      have hl : raw21308step1Labels = raw21308step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21308step0 raw21308step0Labels permutation80 hz
    mixedMoment B raw21308step1 raw21308step1Labels = mixedMoment B raw21308step2 raw21308step2Labels := by
      have ha : raw21308step2 = (fun i j => raw21308step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21308step2 raw21308step1; decide +kernel
      have hl : raw21308step2Labels = raw21308step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21308step1 raw21308step1Labels permutation8 permutation6
    mixedMoment B raw21308step2 raw21308step2Labels = mixedMoment B raw21308step3 raw21308step3Labels := by
      have ha : raw21308step3 = raw21308step2 := by apply Matrix.ext; unfold raw21308step3 raw21308step2; decide +kernel
      have hl : raw21308step2Labels = labelEmbedding9 ∘ raw21308step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21308step2 raw21308step2Labels raw21308step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4270 node4270Labels := by rfl

theorem canonical21309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21309 raw21309Labels = mixedMoment B node4507 node4507Labels := by
  calc
    mixedMoment B raw21309 raw21309Labels = mixedMoment B raw21309step0 raw21309step0Labels := by
      have hz : ∀ j, raw21309 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21309step0 = (fun i j => raw21309 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21309step0 raw21309; decide +kernel
      have hl : raw21309step0Labels = raw21309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21309 raw21309Labels permutation434 hz
    mixedMoment B raw21309step0 raw21309step0Labels = mixedMoment B raw21309step1 raw21309step1Labels := by
      have hz : ∀ j, raw21309step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21309step1 = (fun i j => raw21309step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21309step1 raw21309step0; decide +kernel
      have hl : raw21309step1Labels = raw21309step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21309step0 raw21309step0Labels permutation80 hz
    mixedMoment B raw21309step1 raw21309step1Labels = mixedMoment B raw21309step2 raw21309step2Labels := by
      have hz : ∀ j, raw21309step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21309step2 = (fun i j => raw21309step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21309step2 raw21309step1; decide +kernel
      have hl : raw21309step2Labels = raw21309step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21309step1 raw21309step1Labels permutation14 hz
    mixedMoment B raw21309step2 raw21309step2Labels = mixedMoment B raw21309step3 raw21309step3Labels := by
      have ha : raw21309step3 = (fun i j => raw21309step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21309step3 raw21309step2; decide +kernel
      have hl : raw21309step3Labels = raw21309step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21309step2 raw21309step2Labels permutation2 permutation6
    mixedMoment B raw21309step3 raw21309step3Labels = mixedMoment B raw21309step4 raw21309step4Labels := by
      have ha : raw21309step4 = raw21309step3 := by apply Matrix.ext; unfold raw21309step4 raw21309step3; decide +kernel
      have hl : raw21309step3Labels = labelEmbedding9 ∘ raw21309step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21309step3 raw21309step3Labels raw21309step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4507 node4507Labels := by rfl

theorem canonical21313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21313 raw21313Labels = mixedMoment B node4269 node4269Labels := by
  calc
    mixedMoment B raw21313 raw21313Labels = mixedMoment B raw21313step0 raw21313step0Labels := by
      have hz : ∀ j, raw21313 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21313step0 = (fun i j => raw21313 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21313step0 raw21313; decide +kernel
      have hl : raw21313step0Labels = raw21313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21313 raw21313Labels permutation434 hz
    mixedMoment B raw21313step0 raw21313step0Labels = mixedMoment B raw21313step1 raw21313step1Labels := by
      have hz : ∀ j, raw21313step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21313step1 = (fun i j => raw21313step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21313step1 raw21313step0; decide +kernel
      have hl : raw21313step1Labels = raw21313step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21313step0 raw21313step0Labels permutation80 hz
    mixedMoment B raw21313step1 raw21313step1Labels = mixedMoment B raw21313step2 raw21313step2Labels := by
      have ha : raw21313step2 = (fun i j => raw21313step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21313step2 raw21313step1; decide +kernel
      have hl : raw21313step2Labels = raw21313step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21313step1 raw21313step1Labels permutation8 permutation6
    mixedMoment B raw21313step2 raw21313step2Labels = mixedMoment B raw21313step3 raw21313step3Labels := by
      have ha : raw21313step3 = raw21313step2 := by apply Matrix.ext; unfold raw21313step3 raw21313step2; decide +kernel
      have hl : raw21313step2Labels = labelEmbedding9 ∘ raw21313step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21313step2 raw21313step2Labels raw21313step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4269 node4269Labels := by rfl

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

theorem canonical21736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21736 raw21736Labels = mixedMoment B node4270 node4270Labels := by
  calc
    mixedMoment B raw21736 raw21736Labels = mixedMoment B raw21736step0 raw21736step0Labels := by
      have hz : ∀ j, raw21736 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21736step0 = (fun i j => raw21736 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21736step0 raw21736; decide +kernel
      have hl : raw21736step0Labels = raw21736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21736 raw21736Labels permutation434 hz
    mixedMoment B raw21736step0 raw21736step0Labels = mixedMoment B raw21736step1 raw21736step1Labels := by
      have hz : ∀ j, raw21736step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21736step1 = (fun i j => raw21736step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21736step1 raw21736step0; decide +kernel
      have hl : raw21736step1Labels = raw21736step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21736step0 raw21736step0Labels permutation56 hz
    mixedMoment B raw21736step1 raw21736step1Labels = mixedMoment B raw21736step2 raw21736step2Labels := by
      have ha : raw21736step2 = (fun i j => raw21736step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21736step2 raw21736step1; decide +kernel
      have hl : raw21736step2Labels = raw21736step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21736step1 raw21736step1Labels permutation8 permutation6
    mixedMoment B raw21736step2 raw21736step2Labels = mixedMoment B raw21736step3 raw21736step3Labels := by
      have ha : raw21736step3 = raw21736step2 := by apply Matrix.ext; unfold raw21736step3 raw21736step2; decide +kernel
      have hl : raw21736step2Labels = labelEmbedding9 ∘ raw21736step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21736step2 raw21736step2Labels raw21736step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4270 node4270Labels := by rfl

theorem canonical21740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21740 raw21740Labels = mixedMoment B node4270 node4270Labels := by
  calc
    mixedMoment B raw21740 raw21740Labels = mixedMoment B raw21740step0 raw21740step0Labels := by
      have hz : ∀ j, raw21740 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21740step0 = (fun i j => raw21740 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21740step0 raw21740; decide +kernel
      have hl : raw21740step0Labels = raw21740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21740 raw21740Labels permutation346 hz
    mixedMoment B raw21740step0 raw21740step0Labels = mixedMoment B raw21740step1 raw21740step1Labels := by
      have hz : ∀ j, raw21740step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21740step1 = (fun i j => raw21740step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21740step1 raw21740step0; decide +kernel
      have hl : raw21740step1Labels = raw21740step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21740step0 raw21740step0Labels permutation56 hz
    mixedMoment B raw21740step1 raw21740step1Labels = mixedMoment B raw21740step2 raw21740step2Labels := by
      have ha : raw21740step2 = (fun i j => raw21740step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21740step2 raw21740step1; decide +kernel
      have hl : raw21740step2Labels = raw21740step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21740step1 raw21740step1Labels permutation8 permutation6
    mixedMoment B raw21740step2 raw21740step2Labels = mixedMoment B raw21740step3 raw21740step3Labels := by
      have ha : raw21740step3 = raw21740step2 := by apply Matrix.ext; unfold raw21740step3 raw21740step2; decide +kernel
      have hl : raw21740step2Labels = labelEmbedding9 ∘ raw21740step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21740step2 raw21740step2Labels raw21740step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4270 node4270Labels := by rfl

theorem canonical21744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21744 raw21744Labels = mixedMoment B node4285 node4285Labels := by
  calc
    mixedMoment B raw21744 raw21744Labels = mixedMoment B raw21744step0 raw21744step0Labels := by
      have hz : ∀ j, raw21744 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21744step0 = (fun i j => raw21744 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21744step0 raw21744; decide +kernel
      have hl : raw21744step0Labels = raw21744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21744 raw21744Labels permutation434 hz
    mixedMoment B raw21744step0 raw21744step0Labels = mixedMoment B raw21744step1 raw21744step1Labels := by
      have hz : ∀ j, raw21744step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21744step1 = (fun i j => raw21744step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21744step1 raw21744step0; decide +kernel
      have hl : raw21744step1Labels = raw21744step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21744step0 raw21744step0Labels permutation80 hz
    mixedMoment B raw21744step1 raw21744step1Labels = mixedMoment B raw21744step2 raw21744step2Labels := by
      have hz : ∀ j, raw21744step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21744step2 = (fun i j => raw21744step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21744step2 raw21744step1; decide +kernel
      have hl : raw21744step2Labels = raw21744step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21744step1 raw21744step1Labels permutation14 hz
    mixedMoment B raw21744step2 raw21744step2Labels = mixedMoment B raw21744step3 raw21744step3Labels := by
      have ha : raw21744step3 = (fun i j => raw21744step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21744step3 raw21744step2; decide +kernel
      have hl : raw21744step3Labels = raw21744step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21744step2 raw21744step2Labels permutation3 permutation4
    mixedMoment B raw21744step3 raw21744step3Labels = mixedMoment B raw21744step4 raw21744step4Labels := by
      have ha : raw21744step4 = -raw21744step3 := by apply Matrix.ext; change ∀ i j, raw21744step4 i j = -(raw21744step3 i j); unfold raw21744step4 raw21744step3; decide +kernel
      have hl : raw21744step4Labels = raw21744step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21744step4 raw21744step4Labels = mixedMoment B raw21744step5 raw21744step5Labels := by
      have ha : raw21744step5 = raw21744step4 := by apply Matrix.ext; unfold raw21744step5 raw21744step4; decide +kernel
      have hl : raw21744step4Labels = labelEmbedding7 ∘ raw21744step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21744step4 raw21744step4Labels raw21744step5Labels labelEmbedding7 hl
    _ = mixedMoment B node4285 node4285Labels := by rfl

theorem canonical21750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21750 raw21750Labels = mixedMoment B node4428 node4428Labels := by
  calc
    mixedMoment B raw21750 raw21750Labels = mixedMoment B raw21750step0 raw21750step0Labels := by
      have hz : ∀ j, raw21750 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21750step0 = (fun i j => raw21750 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21750step0 raw21750; decide +kernel
      have hl : raw21750step0Labels = raw21750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21750 raw21750Labels permutation434 hz
    mixedMoment B raw21750step0 raw21750step0Labels = mixedMoment B raw21750step1 raw21750step1Labels := by
      have hz : ∀ j, raw21750step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21750step1 = (fun i j => raw21750step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21750step1 raw21750step0; decide +kernel
      have hl : raw21750step1Labels = raw21750step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21750step0 raw21750step0Labels permutation80 hz
    mixedMoment B raw21750step1 raw21750step1Labels = mixedMoment B raw21750step2 raw21750step2Labels := by
      have ha : raw21750step2 = (fun i j => raw21750step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21750step2 raw21750step1; decide +kernel
      have hl : raw21750step2Labels = raw21750step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21750step1 raw21750step1Labels permutation8 permutation6
    mixedMoment B raw21750step2 raw21750step2Labels = mixedMoment B raw21750step3 raw21750step3Labels := by
      have ha : raw21750step3 = raw21750step2 := by apply Matrix.ext; unfold raw21750step3 raw21750step2; decide +kernel
      have hl : raw21750step2Labels = labelEmbedding9 ∘ raw21750step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21750step2 raw21750step2Labels raw21750step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4428 node4428Labels := by rfl

theorem canonical21751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21751 raw21751Labels = mixedMoment B node4428 node4428Labels := by
  calc
    mixedMoment B raw21751 raw21751Labels = mixedMoment B raw21751step0 raw21751step0Labels := by
      have hz : ∀ j, raw21751 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21751step0 = (fun i j => raw21751 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21751step0 raw21751; decide +kernel
      have hl : raw21751step0Labels = raw21751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21751 raw21751Labels permutation434 hz
    mixedMoment B raw21751step0 raw21751step0Labels = mixedMoment B raw21751step1 raw21751step1Labels := by
      have hz : ∀ j, raw21751step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21751step1 = (fun i j => raw21751step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21751step1 raw21751step0; decide +kernel
      have hl : raw21751step1Labels = raw21751step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21751step0 raw21751step0Labels permutation56 hz
    mixedMoment B raw21751step1 raw21751step1Labels = mixedMoment B raw21751step2 raw21751step2Labels := by
      have ha : raw21751step2 = (fun i j => raw21751step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21751step2 raw21751step1; decide +kernel
      have hl : raw21751step2Labels = raw21751step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21751step1 raw21751step1Labels permutation8 permutation6
    mixedMoment B raw21751step2 raw21751step2Labels = mixedMoment B raw21751step3 raw21751step3Labels := by
      have ha : raw21751step3 = raw21751step2 := by apply Matrix.ext; unfold raw21751step3 raw21751step2; decide +kernel
      have hl : raw21751step2Labels = labelEmbedding9 ∘ raw21751step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21751step2 raw21751step2Labels raw21751step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4428 node4428Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical171
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21991 raw21991Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw21991 raw21991Labels = mixedMoment B raw21991step0 raw21991step0Labels := by
      have hz : ∀ j, raw21991 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21991step0 = (fun i j => raw21991 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21991step0 raw21991; decide +kernel
      have hl : raw21991step0Labels = raw21991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21991 raw21991Labels permutation434 hz
    mixedMoment B raw21991step0 raw21991step0Labels = mixedMoment B raw21991step1 raw21991step1Labels := by
      have hz : ∀ j, raw21991step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21991step1 = (fun i j => raw21991step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21991step1 raw21991step0; decide +kernel
      have hl : raw21991step1Labels = raw21991step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21991step0 raw21991step0Labels permutation80 hz
    mixedMoment B raw21991step1 raw21991step1Labels = mixedMoment B raw21991step2 raw21991step2Labels := by
      have hz : ∀ j, raw21991step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21991step2 = (fun i j => raw21991step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21991step2 raw21991step1; decide +kernel
      have hl : raw21991step2Labels = raw21991step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21991step1 raw21991step1Labels permutation14 hz
    mixedMoment B raw21991step2 raw21991step2Labels = mixedMoment B raw21991step3 raw21991step3Labels := by
      have hz : ∀ i, raw21991step2 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw21991step3 = (fun i j => raw21991step2 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw21991step3 raw21991step2; decide +kernel
      have hl : raw21991step3Labels = (fun j => raw21991step2Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw21991step2 raw21991step2Labels permutation2 hz
    mixedMoment B raw21991step3 raw21991step3Labels = mixedMoment B raw21991step4 raw21991step4Labels := by
      have ha : raw21991step4 = -raw21991step3 := by apply Matrix.ext; change ∀ i j, raw21991step4 i j = -(raw21991step3 i j); unfold raw21991step4 raw21991step3; decide +kernel
      have hl : raw21991step4Labels = raw21991step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21991step4 raw21991step4Labels = mixedMoment B raw21991step5 raw21991step5Labels := by
      have ha : raw21991step5 = raw21991step4 := by apply Matrix.ext; unfold raw21991step5 raw21991step4; decide +kernel
      have hl : raw21991step4Labels = labelEmbedding3 ∘ raw21991step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21991step4 raw21991step4Labels raw21991step5Labels labelEmbedding3 hl
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical21994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21994 raw21994Labels = mixedMoment B node4227 node4227Labels := by
  calc
    mixedMoment B raw21994 raw21994Labels = mixedMoment B raw21994step0 raw21994step0Labels := by
      have hz : ∀ j, raw21994 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21994step0 = (fun i j => raw21994 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21994step0 raw21994; decide +kernel
      have hl : raw21994step0Labels = raw21994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21994 raw21994Labels permutation346 hz
    mixedMoment B raw21994step0 raw21994step0Labels = mixedMoment B raw21994step1 raw21994step1Labels := by
      have hz : ∀ j, raw21994step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21994step1 = (fun i j => raw21994step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21994step1 raw21994step0; decide +kernel
      have hl : raw21994step1Labels = raw21994step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21994step0 raw21994step0Labels permutation56 hz
    mixedMoment B raw21994step1 raw21994step1Labels = mixedMoment B raw21994step2 raw21994step2Labels := by
      have ha : raw21994step2 = (fun i j => raw21994step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21994step2 raw21994step1; decide +kernel
      have hl : raw21994step2Labels = raw21994step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21994step1 raw21994step1Labels permutation8 permutation4
    mixedMoment B raw21994step2 raw21994step2Labels = mixedMoment B raw21994step3 raw21994step3Labels := by
      have ha : raw21994step3 = -raw21994step2 := by apply Matrix.ext; change ∀ i j, raw21994step3 i j = -(raw21994step2 i j); unfold raw21994step3 raw21994step2; decide +kernel
      have hl : raw21994step3Labels = raw21994step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21994step3 raw21994step3Labels = mixedMoment B raw21994step4 raw21994step4Labels := by
      have ha : raw21994step4 = raw21994step3 := by apply Matrix.ext; unfold raw21994step4 raw21994step3; decide +kernel
      have hl : raw21994step3Labels = labelEmbedding7 ∘ raw21994step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21994step3 raw21994step3Labels raw21994step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4227 node4227Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical173
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22211 raw22211Labels = mixedMoment B node4269 node4269Labels := by
  calc
    mixedMoment B raw22211 raw22211Labels = mixedMoment B raw22211step0 raw22211step0Labels := by
      have hz : ∀ j, raw22211 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22211step0 = (fun i j => raw22211 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22211step0 raw22211; decide +kernel
      have hl : raw22211step0Labels = raw22211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22211 raw22211Labels permutation434 hz
    mixedMoment B raw22211step0 raw22211step0Labels = mixedMoment B raw22211step1 raw22211step1Labels := by
      have hz : ∀ j, raw22211step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22211step1 = (fun i j => raw22211step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22211step1 raw22211step0; decide +kernel
      have hl : raw22211step1Labels = raw22211step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22211step0 raw22211step0Labels permutation56 hz
    mixedMoment B raw22211step1 raw22211step1Labels = mixedMoment B raw22211step2 raw22211step2Labels := by
      have ha : raw22211step2 = (fun i j => raw22211step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22211step2 raw22211step1; decide +kernel
      have hl : raw22211step2Labels = raw22211step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22211step1 raw22211step1Labels permutation8 permutation6
    mixedMoment B raw22211step2 raw22211step2Labels = mixedMoment B raw22211step3 raw22211step3Labels := by
      have ha : raw22211step3 = raw22211step2 := by apply Matrix.ext; unfold raw22211step3 raw22211step2; decide +kernel
      have hl : raw22211step2Labels = labelEmbedding9 ∘ raw22211step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22211step2 raw22211step2Labels raw22211step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4269 node4269Labels := by rfl

theorem canonical22214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22214 raw22214Labels = mixedMoment B node4269 node4269Labels := by
  calc
    mixedMoment B raw22214 raw22214Labels = mixedMoment B raw22214step0 raw22214step0Labels := by
      have hz : ∀ j, raw22214 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22214step0 = (fun i j => raw22214 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22214step0 raw22214; decide +kernel
      have hl : raw22214step0Labels = raw22214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22214 raw22214Labels permutation346 hz
    mixedMoment B raw22214step0 raw22214step0Labels = mixedMoment B raw22214step1 raw22214step1Labels := by
      have hz : ∀ j, raw22214step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22214step1 = (fun i j => raw22214step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22214step1 raw22214step0; decide +kernel
      have hl : raw22214step1Labels = raw22214step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22214step0 raw22214step0Labels permutation56 hz
    mixedMoment B raw22214step1 raw22214step1Labels = mixedMoment B raw22214step2 raw22214step2Labels := by
      have ha : raw22214step2 = (fun i j => raw22214step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22214step2 raw22214step1; decide +kernel
      have hl : raw22214step2Labels = raw22214step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22214step1 raw22214step1Labels permutation8 permutation6
    mixedMoment B raw22214step2 raw22214step2Labels = mixedMoment B raw22214step3 raw22214step3Labels := by
      have ha : raw22214step3 = raw22214step2 := by apply Matrix.ext; unfold raw22214step3 raw22214step2; decide +kernel
      have hl : raw22214step2Labels = labelEmbedding9 ∘ raw22214step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22214step2 raw22214step2Labels raw22214step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4269 node4269Labels := by rfl

theorem canonical22216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22216 raw22216Labels = mixedMoment B node4122 node4122Labels := by
  calc
    mixedMoment B raw22216 raw22216Labels = mixedMoment B raw22216step0 raw22216step0Labels := by
      have hz : ∀ j, raw22216 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22216step0 = (fun i j => raw22216 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22216step0 raw22216; decide +kernel
      have hl : raw22216step0Labels = raw22216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22216 raw22216Labels permutation434 hz
    mixedMoment B raw22216step0 raw22216step0Labels = mixedMoment B raw22216step1 raw22216step1Labels := by
      have hz : ∀ j, raw22216step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22216step1 = (fun i j => raw22216step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22216step1 raw22216step0; decide +kernel
      have hl : raw22216step1Labels = raw22216step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22216step0 raw22216step0Labels permutation80 hz
    mixedMoment B raw22216step1 raw22216step1Labels = mixedMoment B raw22216step2 raw22216step2Labels := by
      have ha : raw22216step2 = (fun i j => raw22216step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22216step2 raw22216step1; decide +kernel
      have hl : raw22216step2Labels = raw22216step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22216step1 raw22216step1Labels permutation8 permutation4
    mixedMoment B raw22216step2 raw22216step2Labels = mixedMoment B raw22216step3 raw22216step3Labels := by
      have ha : raw22216step3 = -raw22216step2 := by apply Matrix.ext; change ∀ i j, raw22216step3 i j = -(raw22216step2 i j); unfold raw22216step3 raw22216step2; decide +kernel
      have hl : raw22216step3Labels = raw22216step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22216step3 raw22216step3Labels = mixedMoment B raw22216step4 raw22216step4Labels := by
      have ha : raw22216step4 = raw22216step3 := by apply Matrix.ext; unfold raw22216step4 raw22216step3; decide +kernel
      have hl : raw22216step3Labels = labelEmbedding7 ∘ raw22216step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22216step3 raw22216step3Labels raw22216step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4122 node4122Labels := by rfl

theorem canonical22217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22217 raw22217Labels = mixedMoment B node4213 node4213Labels := by
  calc
    mixedMoment B raw22217 raw22217Labels = mixedMoment B raw22217step0 raw22217step0Labels := by
      have hz : ∀ j, raw22217 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22217step0 = (fun i j => raw22217 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22217step0 raw22217; decide +kernel
      have hl : raw22217step0Labels = raw22217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22217 raw22217Labels permutation434 hz
    mixedMoment B raw22217step0 raw22217step0Labels = mixedMoment B raw22217step1 raw22217step1Labels := by
      have ha : raw22217step1 = (fun i j => raw22217step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22217step1 raw22217step0; decide +kernel
      have hl : raw22217step1Labels = raw22217step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22217step0 raw22217step0Labels permutation38 permutation4
    mixedMoment B raw22217step1 raw22217step1Labels = mixedMoment B raw22217step2 raw22217step2Labels := by
      have ha : raw22217step2 = -raw22217step1 := by apply Matrix.ext; change ∀ i j, raw22217step2 i j = -(raw22217step1 i j); unfold raw22217step2 raw22217step1; decide +kernel
      have hl : raw22217step2Labels = raw22217step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22217step2 raw22217step2Labels = mixedMoment B raw22217step3 raw22217step3Labels := by
      have ha : raw22217step3 = raw22217step2 := by apply Matrix.ext; unfold raw22217step3 raw22217step2; decide +kernel
      have hl : raw22217step2Labels = labelEmbedding7 ∘ raw22217step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22217step2 raw22217step2Labels raw22217step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4213 node4213Labels := by rfl

theorem canonical22218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22218 raw22218Labels = mixedMoment B node4213 node4213Labels := by
  calc
    mixedMoment B raw22218 raw22218Labels = mixedMoment B raw22218step0 raw22218step0Labels := by
      have hz : ∀ j, raw22218 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22218step0 = (fun i j => raw22218 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22218step0 raw22218; decide +kernel
      have hl : raw22218step0Labels = raw22218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22218 raw22218Labels permutation346 hz
    mixedMoment B raw22218step0 raw22218step0Labels = mixedMoment B raw22218step1 raw22218step1Labels := by
      have ha : raw22218step1 = (fun i j => raw22218step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22218step1 raw22218step0; decide +kernel
      have hl : raw22218step1Labels = raw22218step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22218step0 raw22218step0Labels permutation38 permutation4
    mixedMoment B raw22218step1 raw22218step1Labels = mixedMoment B raw22218step2 raw22218step2Labels := by
      have ha : raw22218step2 = -raw22218step1 := by apply Matrix.ext; change ∀ i j, raw22218step2 i j = -(raw22218step1 i j); unfold raw22218step2 raw22218step1; decide +kernel
      have hl : raw22218step2Labels = raw22218step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22218step2 raw22218step2Labels = mixedMoment B raw22218step3 raw22218step3Labels := by
      have ha : raw22218step3 = raw22218step2 := by apply Matrix.ext; unfold raw22218step3 raw22218step2; decide +kernel
      have hl : raw22218step2Labels = labelEmbedding7 ∘ raw22218step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22218step2 raw22218step2Labels raw22218step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4213 node4213Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical174
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22288 raw22288Labels = mixedMoment B node4122 node4122Labels := by
  calc
    mixedMoment B raw22288 raw22288Labels = mixedMoment B raw22288step0 raw22288step0Labels := by
      have hz : ∀ j, raw22288 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22288step0 = (fun i j => raw22288 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22288step0 raw22288; decide +kernel
      have hl : raw22288step0Labels = raw22288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22288 raw22288Labels permutation434 hz
    mixedMoment B raw22288step0 raw22288step0Labels = mixedMoment B raw22288step1 raw22288step1Labels := by
      have hz : ∀ j, raw22288step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22288step1 = (fun i j => raw22288step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22288step1 raw22288step0; decide +kernel
      have hl : raw22288step1Labels = raw22288step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22288step0 raw22288step0Labels permutation56 hz
    mixedMoment B raw22288step1 raw22288step1Labels = mixedMoment B raw22288step2 raw22288step2Labels := by
      have ha : raw22288step2 = (fun i j => raw22288step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22288step2 raw22288step1; decide +kernel
      have hl : raw22288step2Labels = raw22288step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22288step1 raw22288step1Labels permutation8 permutation4
    mixedMoment B raw22288step2 raw22288step2Labels = mixedMoment B raw22288step3 raw22288step3Labels := by
      have ha : raw22288step3 = -raw22288step2 := by apply Matrix.ext; change ∀ i j, raw22288step3 i j = -(raw22288step2 i j); unfold raw22288step3 raw22288step2; decide +kernel
      have hl : raw22288step3Labels = raw22288step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22288step3 raw22288step3Labels = mixedMoment B raw22288step4 raw22288step4Labels := by
      have ha : raw22288step4 = raw22288step3 := by apply Matrix.ext; unfold raw22288step4 raw22288step3; decide +kernel
      have hl : raw22288step3Labels = labelEmbedding7 ∘ raw22288step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22288step3 raw22288step3Labels raw22288step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4122 node4122Labels := by rfl

theorem canonical22289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22289 raw22289Labels = mixedMoment B node4213 node4213Labels := by
  calc
    mixedMoment B raw22289 raw22289Labels = mixedMoment B raw22289step0 raw22289step0Labels := by
      have hz : ∀ j, raw22289 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22289step0 = (fun i j => raw22289 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22289step0 raw22289; decide +kernel
      have hl : raw22289step0Labels = raw22289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22289 raw22289Labels permutation434 hz
    mixedMoment B raw22289step0 raw22289step0Labels = mixedMoment B raw22289step1 raw22289step1Labels := by
      have ha : raw22289step1 = (fun i j => raw22289step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22289step1 raw22289step0; decide +kernel
      have hl : raw22289step1Labels = raw22289step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22289step0 raw22289step0Labels permutation32 permutation4
    mixedMoment B raw22289step1 raw22289step1Labels = mixedMoment B raw22289step2 raw22289step2Labels := by
      have ha : raw22289step2 = -raw22289step1 := by apply Matrix.ext; change ∀ i j, raw22289step2 i j = -(raw22289step1 i j); unfold raw22289step2 raw22289step1; decide +kernel
      have hl : raw22289step2Labels = raw22289step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22289step2 raw22289step2Labels = mixedMoment B raw22289step3 raw22289step3Labels := by
      have ha : raw22289step3 = raw22289step2 := by apply Matrix.ext; unfold raw22289step3 raw22289step2; decide +kernel
      have hl : raw22289step2Labels = labelEmbedding7 ∘ raw22289step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22289step2 raw22289step2Labels raw22289step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4213 node4213Labels := by rfl

theorem canonical22290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22290 raw22290Labels = mixedMoment B node4213 node4213Labels := by
  calc
    mixedMoment B raw22290 raw22290Labels = mixedMoment B raw22290step0 raw22290step0Labels := by
      have hz : ∀ j, raw22290 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22290step0 = (fun i j => raw22290 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22290step0 raw22290; decide +kernel
      have hl : raw22290step0Labels = raw22290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22290 raw22290Labels permutation265 hz
    mixedMoment B raw22290step0 raw22290step0Labels = mixedMoment B raw22290step1 raw22290step1Labels := by
      have ha : raw22290step1 = (fun i j => raw22290step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22290step1 raw22290step0; decide +kernel
      have hl : raw22290step1Labels = raw22290step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22290step0 raw22290step0Labels permutation38 permutation4
    mixedMoment B raw22290step1 raw22290step1Labels = mixedMoment B raw22290step2 raw22290step2Labels := by
      have ha : raw22290step2 = -raw22290step1 := by apply Matrix.ext; change ∀ i j, raw22290step2 i j = -(raw22290step1 i j); unfold raw22290step2 raw22290step1; decide +kernel
      have hl : raw22290step2Labels = raw22290step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22290step2 raw22290step2Labels = mixedMoment B raw22290step3 raw22290step3Labels := by
      have ha : raw22290step3 = raw22290step2 := by apply Matrix.ext; unfold raw22290step3 raw22290step2; decide +kernel
      have hl : raw22290step2Labels = labelEmbedding7 ∘ raw22290step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22290step2 raw22290step2Labels raw22290step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4213 node4213Labels := by rfl

theorem canonical22291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22291 raw22291Labels = mixedMoment B node4122 node4122Labels := by
  calc
    mixedMoment B raw22291 raw22291Labels = mixedMoment B raw22291step0 raw22291step0Labels := by
      have hz : ∀ j, raw22291 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22291step0 = (fun i j => raw22291 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22291step0 raw22291; decide +kernel
      have hl : raw22291step0Labels = raw22291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22291 raw22291Labels permutation346 hz
    mixedMoment B raw22291step0 raw22291step0Labels = mixedMoment B raw22291step1 raw22291step1Labels := by
      have hz : ∀ j, raw22291step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22291step1 = (fun i j => raw22291step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22291step1 raw22291step0; decide +kernel
      have hl : raw22291step1Labels = raw22291step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22291step0 raw22291step0Labels permutation56 hz
    mixedMoment B raw22291step1 raw22291step1Labels = mixedMoment B raw22291step2 raw22291step2Labels := by
      have ha : raw22291step2 = (fun i j => raw22291step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22291step2 raw22291step1; decide +kernel
      have hl : raw22291step2Labels = raw22291step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22291step1 raw22291step1Labels permutation8 permutation4
    mixedMoment B raw22291step2 raw22291step2Labels = mixedMoment B raw22291step3 raw22291step3Labels := by
      have ha : raw22291step3 = -raw22291step2 := by apply Matrix.ext; change ∀ i j, raw22291step3 i j = -(raw22291step2 i j); unfold raw22291step3 raw22291step2; decide +kernel
      have hl : raw22291step3Labels = raw22291step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22291step3 raw22291step3Labels = mixedMoment B raw22291step4 raw22291step4Labels := by
      have ha : raw22291step4 = raw22291step3 := by apply Matrix.ext; unfold raw22291step4 raw22291step3; decide +kernel
      have hl : raw22291step3Labels = labelEmbedding7 ∘ raw22291step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22291step3 raw22291step3Labels raw22291step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4122 node4122Labels := by rfl

theorem canonical22292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22292 raw22292Labels = mixedMoment B node4213 node4213Labels := by
  calc
    mixedMoment B raw22292 raw22292Labels = mixedMoment B raw22292step0 raw22292step0Labels := by
      have hz : ∀ j, raw22292 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22292step0 = (fun i j => raw22292 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22292step0 raw22292; decide +kernel
      have hl : raw22292step0Labels = raw22292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22292 raw22292Labels permutation346 hz
    mixedMoment B raw22292step0 raw22292step0Labels = mixedMoment B raw22292step1 raw22292step1Labels := by
      have ha : raw22292step1 = (fun i j => raw22292step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22292step1 raw22292step0; decide +kernel
      have hl : raw22292step1Labels = raw22292step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22292step0 raw22292step0Labels permutation32 permutation4
    mixedMoment B raw22292step1 raw22292step1Labels = mixedMoment B raw22292step2 raw22292step2Labels := by
      have ha : raw22292step2 = -raw22292step1 := by apply Matrix.ext; change ∀ i j, raw22292step2 i j = -(raw22292step1 i j); unfold raw22292step2 raw22292step1; decide +kernel
      have hl : raw22292step2Labels = raw22292step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22292step2 raw22292step2Labels = mixedMoment B raw22292step3 raw22292step3Labels := by
      have ha : raw22292step3 = raw22292step2 := by apply Matrix.ext; unfold raw22292step3 raw22292step2; decide +kernel
      have hl : raw22292step2Labels = labelEmbedding7 ∘ raw22292step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22292step2 raw22292step2Labels raw22292step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4213 node4213Labels := by rfl

theorem canonical22293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22293 raw22293Labels = mixedMoment B node4213 node4213Labels := by
  calc
    mixedMoment B raw22293 raw22293Labels = mixedMoment B raw22293step0 raw22293step0Labels := by
      have hz : ∀ j, raw22293 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22293step0 = (fun i j => raw22293 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22293step0 raw22293; decide +kernel
      have hl : raw22293step0Labels = raw22293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22293 raw22293Labels permutation265 hz
    mixedMoment B raw22293step0 raw22293step0Labels = mixedMoment B raw22293step1 raw22293step1Labels := by
      have ha : raw22293step1 = (fun i j => raw22293step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22293step1 raw22293step0; decide +kernel
      have hl : raw22293step1Labels = raw22293step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22293step0 raw22293step0Labels permutation32 permutation4
    mixedMoment B raw22293step1 raw22293step1Labels = mixedMoment B raw22293step2 raw22293step2Labels := by
      have ha : raw22293step2 = -raw22293step1 := by apply Matrix.ext; change ∀ i j, raw22293step2 i j = -(raw22293step1 i j); unfold raw22293step2 raw22293step1; decide +kernel
      have hl : raw22293step2Labels = raw22293step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22293step2 raw22293step2Labels = mixedMoment B raw22293step3 raw22293step3Labels := by
      have ha : raw22293step3 = raw22293step2 := by apply Matrix.ext; unfold raw22293step3 raw22293step2; decide +kernel
      have hl : raw22293step2Labels = labelEmbedding7 ∘ raw22293step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22293step2 raw22293step2Labels raw22293step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4213 node4213Labels := by rfl

theorem canonical22294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22294 raw22294Labels = mixedMoment B node4138 node4138Labels := by
  calc
    mixedMoment B raw22294 raw22294Labels = mixedMoment B raw22294step0 raw22294step0Labels := by
      have hz : ∀ j, raw22294 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22294step0 = (fun i j => raw22294 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22294step0 raw22294; decide +kernel
      have hl : raw22294step0Labels = raw22294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22294 raw22294Labels permutation434 hz
    mixedMoment B raw22294step0 raw22294step0Labels = mixedMoment B raw22294step1 raw22294step1Labels := by
      have hz : ∀ j, raw22294step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22294step1 = (fun i j => raw22294step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22294step1 raw22294step0; decide +kernel
      have hl : raw22294step1Labels = raw22294step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22294step0 raw22294step0Labels permutation80 hz
    mixedMoment B raw22294step1 raw22294step1Labels = mixedMoment B raw22294step2 raw22294step2Labels := by
      have hz : ∀ j, raw22294step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22294step2 = (fun i j => raw22294step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22294step2 raw22294step1; decide +kernel
      have hl : raw22294step2Labels = raw22294step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22294step1 raw22294step1Labels permutation14 hz
    mixedMoment B raw22294step2 raw22294step2Labels = mixedMoment B raw22294step3 raw22294step3Labels := by
      have ha : raw22294step3 = (fun i j => raw22294step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22294step3 raw22294step2; decide +kernel
      have hl : raw22294step3Labels = raw22294step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22294step2 raw22294step2Labels permutation3 permutation4
    mixedMoment B raw22294step3 raw22294step3Labels = mixedMoment B raw22294step4 raw22294step4Labels := by
      have ha : raw22294step4 = -raw22294step3 := by apply Matrix.ext; change ∀ i j, raw22294step4 i j = -(raw22294step3 i j); unfold raw22294step4 raw22294step3; decide +kernel
      have hl : raw22294step4Labels = raw22294step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22294step4 raw22294step4Labels = mixedMoment B raw22294step5 raw22294step5Labels := by
      have ha : raw22294step5 = raw22294step4 := by apply Matrix.ext; unfold raw22294step5 raw22294step4; decide +kernel
      have hl : raw22294step4Labels = labelEmbedding7 ∘ raw22294step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22294step4 raw22294step4Labels raw22294step5Labels labelEmbedding7 hl
    _ = mixedMoment B node4138 node4138Labels := by rfl

theorem canonical22295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22295 raw22295Labels = mixedMoment B node4229 node4229Labels := by
  calc
    mixedMoment B raw22295 raw22295Labels = mixedMoment B raw22295step0 raw22295step0Labels := by
      have hz : ∀ j, raw22295 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22295step0 = (fun i j => raw22295 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22295step0 raw22295; decide +kernel
      have hl : raw22295step0Labels = raw22295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22295 raw22295Labels permutation434 hz
    mixedMoment B raw22295step0 raw22295step0Labels = mixedMoment B raw22295step1 raw22295step1Labels := by
      have hz : ∀ j, raw22295step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22295step1 = (fun i j => raw22295step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22295step1 raw22295step0; decide +kernel
      have hl : raw22295step1Labels = raw22295step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22295step0 raw22295step0Labels permutation80 hz
    mixedMoment B raw22295step1 raw22295step1Labels = mixedMoment B raw22295step2 raw22295step2Labels := by
      have ha : raw22295step2 = (fun i j => raw22295step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22295step2 raw22295step1; decide +kernel
      have hl : raw22295step2Labels = raw22295step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22295step1 raw22295step1Labels permutation9 permutation4
    mixedMoment B raw22295step2 raw22295step2Labels = mixedMoment B raw22295step3 raw22295step3Labels := by
      have ha : raw22295step3 = -raw22295step2 := by apply Matrix.ext; change ∀ i j, raw22295step3 i j = -(raw22295step2 i j); unfold raw22295step3 raw22295step2; decide +kernel
      have hl : raw22295step3Labels = raw22295step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22295step3 raw22295step3Labels = mixedMoment B raw22295step4 raw22295step4Labels := by
      have ha : raw22295step4 = raw22295step3 := by apply Matrix.ext; unfold raw22295step4 raw22295step3; decide +kernel
      have hl : raw22295step3Labels = labelEmbedding7 ∘ raw22295step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22295step3 raw22295step3Labels raw22295step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4229 node4229Labels := by rfl

theorem canonical22296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22296 raw22296Labels = mixedMoment B node4229 node4229Labels := by
  calc
    mixedMoment B raw22296 raw22296Labels = mixedMoment B raw22296step0 raw22296step0Labels := by
      have hz : ∀ j, raw22296 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22296step0 = (fun i j => raw22296 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22296step0 raw22296; decide +kernel
      have hl : raw22296step0Labels = raw22296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22296 raw22296Labels permutation434 hz
    mixedMoment B raw22296step0 raw22296step0Labels = mixedMoment B raw22296step1 raw22296step1Labels := by
      have hz : ∀ j, raw22296step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22296step1 = (fun i j => raw22296step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22296step1 raw22296step0; decide +kernel
      have hl : raw22296step1Labels = raw22296step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22296step0 raw22296step0Labels permutation56 hz
    mixedMoment B raw22296step1 raw22296step1Labels = mixedMoment B raw22296step2 raw22296step2Labels := by
      have ha : raw22296step2 = (fun i j => raw22296step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22296step2 raw22296step1; decide +kernel
      have hl : raw22296step2Labels = raw22296step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22296step1 raw22296step1Labels permutation9 permutation4
    mixedMoment B raw22296step2 raw22296step2Labels = mixedMoment B raw22296step3 raw22296step3Labels := by
      have ha : raw22296step3 = -raw22296step2 := by apply Matrix.ext; change ∀ i j, raw22296step3 i j = -(raw22296step2 i j); unfold raw22296step3 raw22296step2; decide +kernel
      have hl : raw22296step3Labels = raw22296step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22296step3 raw22296step3Labels = mixedMoment B raw22296step4 raw22296step4Labels := by
      have ha : raw22296step4 = raw22296step3 := by apply Matrix.ext; unfold raw22296step4 raw22296step3; decide +kernel
      have hl : raw22296step3Labels = labelEmbedding7 ∘ raw22296step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22296step3 raw22296step3Labels raw22296step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4229 node4229Labels := by rfl

theorem canonical22297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22297 raw22297Labels = mixedMoment B node4229 node4229Labels := by
  calc
    mixedMoment B raw22297 raw22297Labels = mixedMoment B raw22297step0 raw22297step0Labels := by
      have hz : ∀ j, raw22297 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22297step0 = (fun i j => raw22297 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22297step0 raw22297; decide +kernel
      have hl : raw22297step0Labels = raw22297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22297 raw22297Labels permutation346 hz
    mixedMoment B raw22297step0 raw22297step0Labels = mixedMoment B raw22297step1 raw22297step1Labels := by
      have hz : ∀ j, raw22297step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22297step1 = (fun i j => raw22297step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22297step1 raw22297step0; decide +kernel
      have hl : raw22297step1Labels = raw22297step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22297step0 raw22297step0Labels permutation56 hz
    mixedMoment B raw22297step1 raw22297step1Labels = mixedMoment B raw22297step2 raw22297step2Labels := by
      have ha : raw22297step2 = (fun i j => raw22297step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22297step2 raw22297step1; decide +kernel
      have hl : raw22297step2Labels = raw22297step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22297step1 raw22297step1Labels permutation9 permutation4
    mixedMoment B raw22297step2 raw22297step2Labels = mixedMoment B raw22297step3 raw22297step3Labels := by
      have ha : raw22297step3 = -raw22297step2 := by apply Matrix.ext; change ∀ i j, raw22297step3 i j = -(raw22297step2 i j); unfold raw22297step3 raw22297step2; decide +kernel
      have hl : raw22297step3Labels = raw22297step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22297step3 raw22297step3Labels = mixedMoment B raw22297step4 raw22297step4Labels := by
      have ha : raw22297step4 = raw22297step3 := by apply Matrix.ext; unfold raw22297step4 raw22297step3; decide +kernel
      have hl : raw22297step3Labels = labelEmbedding7 ∘ raw22297step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22297step3 raw22297step3Labels raw22297step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4229 node4229Labels := by rfl

theorem canonical22298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22298 raw22298Labels = mixedMoment B node4136 node4136Labels := by
  calc
    mixedMoment B raw22298 raw22298Labels = mixedMoment B raw22298step0 raw22298step0Labels := by
      have hz : ∀ j, raw22298 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22298step0 = (fun i j => raw22298 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22298step0 raw22298; decide +kernel
      have hl : raw22298step0Labels = raw22298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22298 raw22298Labels permutation434 hz
    mixedMoment B raw22298step0 raw22298step0Labels = mixedMoment B raw22298step1 raw22298step1Labels := by
      have hz : ∀ j, raw22298step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22298step1 = (fun i j => raw22298step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22298step1 raw22298step0; decide +kernel
      have hl : raw22298step1Labels = raw22298step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22298step0 raw22298step0Labels permutation80 hz
    mixedMoment B raw22298step1 raw22298step1Labels = mixedMoment B raw22298step2 raw22298step2Labels := by
      have hz : ∀ j, raw22298step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22298step2 = (fun i j => raw22298step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22298step2 raw22298step1; decide +kernel
      have hl : raw22298step2Labels = raw22298step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22298step1 raw22298step1Labels permutation14 hz
    mixedMoment B raw22298step2 raw22298step2Labels = mixedMoment B raw22298step3 raw22298step3Labels := by
      have ha : raw22298step3 = (fun i j => raw22298step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22298step3 raw22298step2; decide +kernel
      have hl : raw22298step3Labels = raw22298step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22298step2 raw22298step2Labels permutation2 permutation4
    mixedMoment B raw22298step3 raw22298step3Labels = mixedMoment B raw22298step4 raw22298step4Labels := by
      have ha : raw22298step4 = -raw22298step3 := by apply Matrix.ext; change ∀ i j, raw22298step4 i j = -(raw22298step3 i j); unfold raw22298step4 raw22298step3; decide +kernel
      have hl : raw22298step4Labels = raw22298step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22298step4 raw22298step4Labels = mixedMoment B raw22298step5 raw22298step5Labels := by
      have ha : raw22298step5 = raw22298step4 := by apply Matrix.ext; unfold raw22298step5 raw22298step4; decide +kernel
      have hl : raw22298step4Labels = labelEmbedding7 ∘ raw22298step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22298step4 raw22298step4Labels raw22298step5Labels labelEmbedding7 hl
    _ = mixedMoment B node4136 node4136Labels := by rfl

theorem canonical22299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22299 raw22299Labels = mixedMoment B node4227 node4227Labels := by
  calc
    mixedMoment B raw22299 raw22299Labels = mixedMoment B raw22299step0 raw22299step0Labels := by
      have hz : ∀ j, raw22299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22299step0 = (fun i j => raw22299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22299step0 raw22299; decide +kernel
      have hl : raw22299step0Labels = raw22299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22299 raw22299Labels permutation434 hz
    mixedMoment B raw22299step0 raw22299step0Labels = mixedMoment B raw22299step1 raw22299step1Labels := by
      have hz : ∀ j, raw22299step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22299step1 = (fun i j => raw22299step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22299step1 raw22299step0; decide +kernel
      have hl : raw22299step1Labels = raw22299step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22299step0 raw22299step0Labels permutation80 hz
    mixedMoment B raw22299step1 raw22299step1Labels = mixedMoment B raw22299step2 raw22299step2Labels := by
      have ha : raw22299step2 = (fun i j => raw22299step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22299step2 raw22299step1; decide +kernel
      have hl : raw22299step2Labels = raw22299step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22299step1 raw22299step1Labels permutation8 permutation4
    mixedMoment B raw22299step2 raw22299step2Labels = mixedMoment B raw22299step3 raw22299step3Labels := by
      have ha : raw22299step3 = -raw22299step2 := by apply Matrix.ext; change ∀ i j, raw22299step3 i j = -(raw22299step2 i j); unfold raw22299step3 raw22299step2; decide +kernel
      have hl : raw22299step3Labels = raw22299step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22299step3 raw22299step3Labels = mixedMoment B raw22299step4 raw22299step4Labels := by
      have ha : raw22299step4 = raw22299step3 := by apply Matrix.ext; unfold raw22299step4 raw22299step3; decide +kernel
      have hl : raw22299step3Labels = labelEmbedding7 ∘ raw22299step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22299step3 raw22299step3Labels raw22299step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4227 node4227Labels := by rfl

theorem canonical22300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22300 raw22300Labels = mixedMoment B node4227 node4227Labels := by
  calc
    mixedMoment B raw22300 raw22300Labels = mixedMoment B raw22300step0 raw22300step0Labels := by
      have hz : ∀ j, raw22300 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22300step0 = (fun i j => raw22300 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22300step0 raw22300; decide +kernel
      have hl : raw22300step0Labels = raw22300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22300 raw22300Labels permutation434 hz
    mixedMoment B raw22300step0 raw22300step0Labels = mixedMoment B raw22300step1 raw22300step1Labels := by
      have hz : ∀ j, raw22300step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22300step1 = (fun i j => raw22300step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22300step1 raw22300step0; decide +kernel
      have hl : raw22300step1Labels = raw22300step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22300step0 raw22300step0Labels permutation56 hz
    mixedMoment B raw22300step1 raw22300step1Labels = mixedMoment B raw22300step2 raw22300step2Labels := by
      have ha : raw22300step2 = (fun i j => raw22300step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22300step2 raw22300step1; decide +kernel
      have hl : raw22300step2Labels = raw22300step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22300step1 raw22300step1Labels permutation8 permutation4
    mixedMoment B raw22300step2 raw22300step2Labels = mixedMoment B raw22300step3 raw22300step3Labels := by
      have ha : raw22300step3 = -raw22300step2 := by apply Matrix.ext; change ∀ i j, raw22300step3 i j = -(raw22300step2 i j); unfold raw22300step3 raw22300step2; decide +kernel
      have hl : raw22300step3Labels = raw22300step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22300step3 raw22300step3Labels = mixedMoment B raw22300step4 raw22300step4Labels := by
      have ha : raw22300step4 = raw22300step3 := by apply Matrix.ext; unfold raw22300step4 raw22300step3; decide +kernel
      have hl : raw22300step3Labels = labelEmbedding7 ∘ raw22300step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22300step3 raw22300step3Labels raw22300step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4227 node4227Labels := by rfl

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

theorem canonical729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw729 raw729Labels = mixedMoment B node4122 node4122Labels := by
  calc
    mixedMoment B raw729 raw729Labels = mixedMoment B raw729step0 raw729step0Labels := by
      have ha : raw729step0 = (fun i j => raw729 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw729step0 raw729; decide +kernel
      have hl : raw729step0Labels = raw729Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw729 raw729Labels permutation8 permutation4
    mixedMoment B raw729step0 raw729step0Labels = mixedMoment B raw729step1 raw729step1Labels := by
      have ha : raw729step1 = raw729step0 := by apply Matrix.ext; unfold raw729step1 raw729step0; decide +kernel
      have hl : raw729step0Labels = labelEmbedding7 ∘ raw729step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw729step0 raw729step0Labels raw729step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4122 node4122Labels := by rfl

theorem canonical730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw730 raw730Labels = mixedMoment B node556 node556Labels := by
  calc
    mixedMoment B raw730 raw730Labels = mixedMoment B raw730step0 raw730step0Labels := by
      have ha : raw730step0 = (fun i j => raw730 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw730step0 raw730; decide +kernel
      have hl : raw730step0Labels = raw730Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw730 raw730Labels permutation8 permutation4
    _ = mixedMoment B node556 node556Labels := by rfl

theorem canonical731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw731 raw731Labels = mixedMoment B node670 node670Labels := by
  calc
    mixedMoment B raw731 raw731Labels = mixedMoment B raw731step0 raw731step0Labels := by
      have ha : raw731step0 = (fun i j => raw731 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw731step0 raw731; decide +kernel
      have hl : raw731step0Labels = raw731Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw731 raw731Labels permutation8 permutation6
    mixedMoment B raw731step0 raw731step0Labels = mixedMoment B raw731step1 raw731step1Labels := by
      have ha : raw731step1 = -raw731step0 := by apply Matrix.ext; change ∀ i j, raw731step1 i j = -(raw731step0 i j); unfold raw731step1 raw731step0; decide +kernel
      have hl : raw731step1Labels = raw731step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw731step1 raw731step1Labels = mixedMoment B raw731step2 raw731step2Labels := by
      have ha : raw731step2 = raw731step1 := by apply Matrix.ext; unfold raw731step2 raw731step1; decide +kernel
      have hl : raw731step1Labels = labelEmbedding1 ∘ raw731step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw731step1 raw731step1Labels raw731step2Labels labelEmbedding1 hl
    _ = mixedMoment B node670 node670Labels := by rfl

theorem canonical753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw753 raw753Labels = mixedMoment B node4138 node4138Labels := by
  calc
    mixedMoment B raw753 raw753Labels = mixedMoment B raw753step0 raw753step0Labels := by
      have ha : raw753step0 = (fun i j => raw753 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw753step0 raw753; decide +kernel
      have hl : raw753step0Labels = raw753Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw753 raw753Labels permutation2 permutation4
    mixedMoment B raw753step0 raw753step0Labels = mixedMoment B raw753step1 raw753step1Labels := by
      have ha : raw753step1 = raw753step0 := by apply Matrix.ext; unfold raw753step1 raw753step0; decide +kernel
      have hl : raw753step0Labels = labelEmbedding7 ∘ raw753step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw753step0 raw753step0Labels raw753step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4138 node4138Labels := by rfl

theorem canonical754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw754 raw754Labels = mixedMoment B node566 node566Labels := by
  calc
    mixedMoment B raw754 raw754Labels = mixedMoment B raw754step0 raw754step0Labels := by
      have ha : raw754step0 = (fun i j => raw754 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw754step0 raw754; decide +kernel
      have hl : raw754step0Labels = raw754Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw754 raw754Labels permutation2 permutation4
    _ = mixedMoment B node566 node566Labels := by rfl

theorem canonical755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw755 raw755Labels = mixedMoment B node694 node694Labels := by
  calc
    mixedMoment B raw755 raw755Labels = mixedMoment B raw755step0 raw755step0Labels := by
      have ha : raw755step0 = (fun i j => raw755 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw755step0 raw755; decide +kernel
      have hl : raw755step0Labels = raw755Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw755 raw755Labels permutation3 permutation6
    mixedMoment B raw755step0 raw755step0Labels = mixedMoment B raw755step1 raw755step1Labels := by
      have ha : raw755step1 = -raw755step0 := by apply Matrix.ext; change ∀ i j, raw755step1 i j = -(raw755step0 i j); unfold raw755step1 raw755step0; decide +kernel
      have hl : raw755step1Labels = raw755step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw755step1 raw755step1Labels = mixedMoment B raw755step2 raw755step2Labels := by
      have ha : raw755step2 = raw755step1 := by apply Matrix.ext; unfold raw755step2 raw755step1; decide +kernel
      have hl : raw755step1Labels = labelEmbedding1 ∘ raw755step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw755step1 raw755step1Labels raw755step2Labels labelEmbedding1 hl
    _ = mixedMoment B node694 node694Labels := by rfl

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

theorem canonical897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw897 raw897Labels = mixedMoment B node4213 node4213Labels := by
  calc
    mixedMoment B raw897 raw897Labels = mixedMoment B raw897step0 raw897step0Labels := by
      have ha : raw897step0 = (fun i j => raw897 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw897step0 raw897; decide +kernel
      have hl : raw897step0Labels = raw897Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw897 raw897Labels permutation32 permutation4
    mixedMoment B raw897step0 raw897step0Labels = mixedMoment B raw897step1 raw897step1Labels := by
      have ha : raw897step1 = raw897step0 := by apply Matrix.ext; unfold raw897step1 raw897step0; decide +kernel
      have hl : raw897step0Labels = labelEmbedding7 ∘ raw897step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw897step0 raw897step0Labels raw897step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4213 node4213Labels := by rfl

theorem canonical898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw898 raw898Labels = mixedMoment B node716 node716Labels := by
  calc
    mixedMoment B raw898 raw898Labels = mixedMoment B raw898step0 raw898step0Labels := by
      have ha : raw898step0 = (fun i j => raw898 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw898step0 raw898; decide +kernel
      have hl : raw898step0Labels = raw898Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw898 raw898Labels permutation32 permutation4
    _ = mixedMoment B node716 node716Labels := by rfl

theorem canonical899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw899 raw899Labels = mixedMoment B node752 node752Labels := by
  calc
    mixedMoment B raw899 raw899Labels = mixedMoment B raw899step0 raw899step0Labels := by
      have ha : raw899step0 = (fun i j => raw899 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw899step0 raw899; decide +kernel
      have hl : raw899step0Labels = raw899Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw899 raw899Labels permutation32 permutation6
    mixedMoment B raw899step0 raw899step0Labels = mixedMoment B raw899step1 raw899step1Labels := by
      have ha : raw899step1 = -raw899step0 := by apply Matrix.ext; change ∀ i j, raw899step1 i j = -(raw899step0 i j); unfold raw899step1 raw899step0; decide +kernel
      have hl : raw899step1Labels = raw899step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw899step1 raw899step1Labels = mixedMoment B raw899step2 raw899step2Labels := by
      have ha : raw899step2 = raw899step1 := by apply Matrix.ext; unfold raw899step2 raw899step1; decide +kernel
      have hl : raw899step1Labels = labelEmbedding1 ∘ raw899step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw899step1 raw899step1Labels raw899step2Labels labelEmbedding1 hl
    _ = mixedMoment B node752 node752Labels := by rfl

theorem canonical921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw921 raw921Labels = mixedMoment B node4229 node4229Labels := by
  calc
    mixedMoment B raw921 raw921Labels = mixedMoment B raw921step0 raw921step0Labels := by
      have ha : raw921step0 = (fun i j => raw921 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw921step0 raw921; decide +kernel
      have hl : raw921step0Labels = raw921Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw921 raw921Labels permutation8 permutation4
    mixedMoment B raw921step0 raw921step0Labels = mixedMoment B raw921step1 raw921step1Labels := by
      have ha : raw921step1 = raw921step0 := by apply Matrix.ext; unfold raw921step1 raw921step0; decide +kernel
      have hl : raw921step0Labels = labelEmbedding7 ∘ raw921step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw921step0 raw921step0Labels raw921step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4229 node4229Labels := by rfl

theorem canonical922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw922 raw922Labels = mixedMoment B node729 node729Labels := by
  calc
    mixedMoment B raw922 raw922Labels = mixedMoment B raw922step0 raw922step0Labels := by
      have ha : raw922step0 = (fun i j => raw922 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw922step0 raw922; decide +kernel
      have hl : raw922step0Labels = raw922Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw922 raw922Labels permutation8 permutation4
    _ = mixedMoment B node729 node729Labels := by rfl

theorem canonical923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw923 raw923Labels = mixedMoment B node773 node773Labels := by
  calc
    mixedMoment B raw923 raw923Labels = mixedMoment B raw923step0 raw923step0Labels := by
      have ha : raw923step0 = (fun i j => raw923 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw923step0 raw923; decide +kernel
      have hl : raw923step0Labels = raw923Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw923 raw923Labels permutation9 permutation6
    mixedMoment B raw923step0 raw923step0Labels = mixedMoment B raw923step1 raw923step1Labels := by
      have ha : raw923step1 = -raw923step0 := by apply Matrix.ext; change ∀ i j, raw923step1 i j = -(raw923step0 i j); unfold raw923step1 raw923step0; decide +kernel
      have hl : raw923step1Labels = raw923step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw923step1 raw923step1Labels = mixedMoment B raw923step2 raw923step2Labels := by
      have ha : raw923step2 = raw923step1 := by apply Matrix.ext; unfold raw923step2 raw923step1; decide +kernel
      have hl : raw923step1Labels = labelEmbedding1 ∘ raw923step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw923step1 raw923step1Labels raw923step2Labels labelEmbedding1 hl
    _ = mixedMoment B node773 node773Labels := by rfl

theorem canonical996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw996 raw996Labels = mixedMoment B node4270 node4270Labels := by
  calc
    mixedMoment B raw996 raw996Labels = mixedMoment B raw996step0 raw996step0Labels := by
      have ha : raw996step0 = (fun i j => raw996 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw996step0 raw996; decide +kernel
      have hl : raw996step0Labels = raw996Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw996 raw996Labels permutation8 permutation4
    mixedMoment B raw996step0 raw996step0Labels = mixedMoment B raw996step1 raw996step1Labels := by
      have ha : raw996step1 = raw996step0 := by apply Matrix.ext; unfold raw996step1 raw996step0; decide +kernel
      have hl : raw996step0Labels = labelEmbedding7 ∘ raw996step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw996step0 raw996step0Labels raw996step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4270 node4270Labels := by rfl

theorem canonical997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw997 raw997Labels = mixedMoment B node813 node813Labels := by
  calc
    mixedMoment B raw997 raw997Labels = mixedMoment B raw997step0 raw997step0Labels := by
      have ha : raw997step0 = (fun i j => raw997 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw997step0 raw997; decide +kernel
      have hl : raw997step0Labels = raw997Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw997 raw997Labels permutation8 permutation4
    _ = mixedMoment B node813 node813Labels := by rfl

theorem canonical998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw998 raw998Labels = mixedMoment B node853 node853Labels := by
  calc
    mixedMoment B raw998 raw998Labels = mixedMoment B raw998step0 raw998step0Labels := by
      have ha : raw998step0 = (fun i j => raw998 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw998step0 raw998; decide +kernel
      have hl : raw998step0Labels = raw998Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw998 raw998Labels permutation9 permutation6
    mixedMoment B raw998step0 raw998step0Labels = mixedMoment B raw998step1 raw998step1Labels := by
      have ha : raw998step1 = -raw998step0 := by apply Matrix.ext; change ∀ i j, raw998step1 i j = -(raw998step0 i j); unfold raw998step1 raw998step0; decide +kernel
      have hl : raw998step1Labels = raw998step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw998step1 raw998step1Labels = mixedMoment B raw998step2 raw998step2Labels := by
      have ha : raw998step2 = raw998step1 := by apply Matrix.ext; unfold raw998step2 raw998step1; decide +kernel
      have hl : raw998step1Labels = labelEmbedding1 ∘ raw998step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw998step1 raw998step1Labels raw998step2Labels labelEmbedding1 hl
    _ = mixedMoment B node853 node853Labels := by rfl

theorem canonical1017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1017 raw1017Labels = mixedMoment B node4285 node4285Labels := by
  calc
    mixedMoment B raw1017 raw1017Labels = mixedMoment B raw1017step0 raw1017step0Labels := by
      have ha : raw1017step0 = (fun i j => raw1017 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1017step0 raw1017; decide +kernel
      have hl : raw1017step0Labels = raw1017Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1017 raw1017Labels permutation2 permutation4
    mixedMoment B raw1017step0 raw1017step0Labels = mixedMoment B raw1017step1 raw1017step1Labels := by
      have ha : raw1017step1 = raw1017step0 := by apply Matrix.ext; unfold raw1017step1 raw1017step0; decide +kernel
      have hl : raw1017step0Labels = labelEmbedding7 ∘ raw1017step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1017step0 raw1017step0Labels raw1017step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4285 node4285Labels := by rfl

theorem canonical1018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1018 raw1018Labels = mixedMoment B node860 node860Labels := by
  calc
    mixedMoment B raw1018 raw1018Labels = mixedMoment B raw1018step0 raw1018step0Labels := by
      have ha : raw1018step0 = (fun i j => raw1018 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1018step0 raw1018; decide +kernel
      have hl : raw1018step0Labels = raw1018Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1018 raw1018Labels permutation2 permutation4
    _ = mixedMoment B node860 node860Labels := by rfl

theorem canonical1019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1019 raw1019Labels = mixedMoment B node860 node860Labels := by
  calc
    mixedMoment B raw1019 raw1019Labels = mixedMoment B raw1019step0 raw1019step0Labels := by
      have ha : raw1019step0 = (fun i j => raw1019 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1019step0 raw1019; decide +kernel
      have hl : raw1019step0Labels = raw1019Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1019 raw1019Labels permutation3 permutation6
    mixedMoment B raw1019step0 raw1019step0Labels = mixedMoment B raw1019step1 raw1019step1Labels := by
      have ha : raw1019step1 = -raw1019step0 := by apply Matrix.ext; change ∀ i j, raw1019step1 i j = -(raw1019step0 i j); unfold raw1019step1 raw1019step0; decide +kernel
      have hl : raw1019step1Labels = raw1019step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1019step1 raw1019step1Labels = mixedMoment B raw1019step2 raw1019step2Labels := by
      have ha : raw1019step2 = raw1019step1 := by apply Matrix.ext; unfold raw1019step2 raw1019step1; decide +kernel
      have hl : raw1019step1Labels = labelEmbedding1 ∘ raw1019step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1019step1 raw1019step1Labels raw1019step2Labels labelEmbedding1 hl
    _ = mixedMoment B node860 node860Labels := by rfl

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

theorem canonical1239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1239 raw1239Labels = mixedMoment B node4428 node4428Labels := by
  calc
    mixedMoment B raw1239 raw1239Labels = mixedMoment B raw1239step0 raw1239step0Labels := by
      have ha : raw1239step0 = (fun i j => raw1239 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1239step0 raw1239; decide +kernel
      have hl : raw1239step0Labels = raw1239Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1239 raw1239Labels permutation8 permutation4
    mixedMoment B raw1239step0 raw1239step0Labels = mixedMoment B raw1239step1 raw1239step1Labels := by
      have ha : raw1239step1 = raw1239step0 := by apply Matrix.ext; unfold raw1239step1 raw1239step0; decide +kernel
      have hl : raw1239step0Labels = labelEmbedding7 ∘ raw1239step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1239step0 raw1239step0Labels raw1239step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4428 node4428Labels := by rfl

theorem canonical1240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1240 raw1240Labels = mixedMoment B node1009 node1009Labels := by
  calc
    mixedMoment B raw1240 raw1240Labels = mixedMoment B raw1240step0 raw1240step0Labels := by
      have ha : raw1240step0 = (fun i j => raw1240 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1240step0 raw1240; decide +kernel
      have hl : raw1240step0Labels = raw1240Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1240 raw1240Labels permutation8 permutation4
    _ = mixedMoment B node1009 node1009Labels := by rfl

theorem canonical1241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1241 raw1241Labels = mixedMoment B node1630 node1630Labels := by
  calc
    mixedMoment B raw1241 raw1241Labels = mixedMoment B raw1241step0 raw1241step0Labels := by
      have ha : raw1241step0 = (fun i j => raw1241 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1241step0 raw1241; decide +kernel
      have hl : raw1241step0Labels = raw1241Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1241 raw1241Labels permutation8 permutation6
    mixedMoment B raw1241step0 raw1241step0Labels = mixedMoment B raw1241step1 raw1241step1Labels := by
      have ha : raw1241step1 = -raw1241step0 := by apply Matrix.ext; change ∀ i j, raw1241step1 i j = -(raw1241step0 i j); unfold raw1241step1 raw1241step0; decide +kernel
      have hl : raw1241step1Labels = raw1241step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1241step1 raw1241step1Labels = mixedMoment B raw1241step2 raw1241step2Labels := by
      have ha : raw1241step2 = raw1241step1 := by apply Matrix.ext; unfold raw1241step2 raw1241step1; decide +kernel
      have hl : raw1241step1Labels = labelEmbedding1 ∘ raw1241step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1241step1 raw1241step1Labels raw1241step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1630 node1630Labels := by rfl

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

theorem singleton4122 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4122 node4122Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node556 node556Labels + mixedMoment B node670 node670Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw729 singletonSmall4122
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4122) = raw729Labels := by decide +kernel
  rw [hl, canonical729 B hB] at h
  have hc0 : mixedMoment B raw729 (Fin.cases (0 : Fin 2) singletonSmall4122) =
      mixedMoment B node556 node556Labels := by
    have ha : raw729 = raw730 := by apply Matrix.ext; unfold raw729 raw730; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4122 = raw730Labels := by decide +kernel
    rw [ha, hj, canonical730 B hB]
  have hc1 : mixedMoment B raw729 (Fin.cases (1 : Fin 2) singletonSmall4122) =
      mixedMoment B node670 node670Labels := by
    have ha : raw729 = raw731 := by apply Matrix.ext; unfold raw729 raw731; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4122 = raw731Labels := by decide +kernel
    rw [ha, hj, canonical731 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4138 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4138 node4138Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node566 node566Labels + mixedMoment B node694 node694Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw753 singletonSmall4138
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4138) = raw753Labels := by decide +kernel
  rw [hl, canonical753 B hB] at h
  have hc0 : mixedMoment B raw753 (Fin.cases (0 : Fin 2) singletonSmall4138) =
      mixedMoment B node566 node566Labels := by
    have ha : raw753 = raw754 := by apply Matrix.ext; unfold raw753 raw754; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4138 = raw754Labels := by decide +kernel
    rw [ha, hj, canonical754 B hB]
  have hc1 : mixedMoment B raw753 (Fin.cases (1 : Fin 2) singletonSmall4138) =
      mixedMoment B node694 node694Labels := by
    have ha : raw753 = raw755 := by apply Matrix.ext; unfold raw753 raw755; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4138 = raw755Labels := by decide +kernel
    rw [ha, hj, canonical755 B hB]
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

theorem singleton4213 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4213 node4213Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node716 node716Labels + mixedMoment B node752 node752Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw897 singletonSmall4213
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4213) = raw897Labels := by decide +kernel
  rw [hl, canonical897 B hB] at h
  have hc0 : mixedMoment B raw897 (Fin.cases (0 : Fin 2) singletonSmall4213) =
      mixedMoment B node716 node716Labels := by
    have ha : raw897 = raw898 := by apply Matrix.ext; unfold raw897 raw898; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4213 = raw898Labels := by decide +kernel
    rw [ha, hj, canonical898 B hB]
  have hc1 : mixedMoment B raw897 (Fin.cases (1 : Fin 2) singletonSmall4213) =
      mixedMoment B node752 node752Labels := by
    have ha : raw897 = raw899 := by apply Matrix.ext; unfold raw897 raw899; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4213 = raw899Labels := by decide +kernel
    rw [ha, hj, canonical899 B hB]
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

theorem singleton4229 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4229 node4229Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node729 node729Labels + mixedMoment B node773 node773Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw921 singletonSmall4229
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4229) = raw921Labels := by decide +kernel
  rw [hl, canonical921 B hB] at h
  have hc0 : mixedMoment B raw921 (Fin.cases (0 : Fin 2) singletonSmall4229) =
      mixedMoment B node729 node729Labels := by
    have ha : raw921 = raw922 := by apply Matrix.ext; unfold raw921 raw922; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4229 = raw922Labels := by decide +kernel
    rw [ha, hj, canonical922 B hB]
  have hc1 : mixedMoment B raw921 (Fin.cases (1 : Fin 2) singletonSmall4229) =
      mixedMoment B node773 node773Labels := by
    have ha : raw921 = raw923 := by apply Matrix.ext; unfold raw921 raw923; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4229 = raw923Labels := by decide +kernel
    rw [ha, hj, canonical923 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4270 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4270 node4270Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node813 node813Labels + mixedMoment B node853 node853Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw996 singletonSmall4270
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4270) = raw996Labels := by decide +kernel
  rw [hl, canonical996 B hB] at h
  have hc0 : mixedMoment B raw996 (Fin.cases (0 : Fin 2) singletonSmall4270) =
      mixedMoment B node813 node813Labels := by
    have ha : raw996 = raw997 := by apply Matrix.ext; unfold raw996 raw997; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4270 = raw997Labels := by decide +kernel
    rw [ha, hj, canonical997 B hB]
  have hc1 : mixedMoment B raw996 (Fin.cases (1 : Fin 2) singletonSmall4270) =
      mixedMoment B node853 node853Labels := by
    have ha : raw996 = raw998 := by apply Matrix.ext; unfold raw996 raw998; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4270 = raw998Labels := by decide +kernel
    rw [ha, hj, canonical998 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4285 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4285 node4285Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node860 node860Labels + mixedMoment B node860 node860Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1017 singletonSmall4285
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4285) = raw1017Labels := by decide +kernel
  rw [hl, canonical1017 B hB] at h
  have hc0 : mixedMoment B raw1017 (Fin.cases (0 : Fin 2) singletonSmall4285) =
      mixedMoment B node860 node860Labels := by
    have ha : raw1017 = raw1018 := by apply Matrix.ext; unfold raw1017 raw1018; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4285 = raw1018Labels := by decide +kernel
    rw [ha, hj, canonical1018 B hB]
  have hc1 : mixedMoment B raw1017 (Fin.cases (1 : Fin 2) singletonSmall4285) =
      mixedMoment B node860 node860Labels := by
    have ha : raw1017 = raw1019 := by apply Matrix.ext; unfold raw1017 raw1019; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4285 = raw1019Labels := by decide +kernel
    rw [ha, hj, canonical1019 B hB]
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

theorem singleton4428 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4428 node4428Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1009 node1009Labels + mixedMoment B node1630 node1630Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1239 singletonSmall4428
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4428) = raw1239Labels := by decide +kernel
  rw [hl, canonical1239 B hB] at h
  have hc0 : mixedMoment B raw1239 (Fin.cases (0 : Fin 2) singletonSmall4428) =
      mixedMoment B node1009 node1009Labels := by
    have ha : raw1239 = raw1240 := by apply Matrix.ext; unfold raw1239 raw1240; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4428 = raw1240Labels := by decide +kernel
    rw [ha, hj, canonical1240 B hB]
  have hc1 : mixedMoment B raw1239 (Fin.cases (1 : Fin 2) singletonSmall4428) =
      mixedMoment B node1630 node1630Labels := by
    have ha : raw1239 = raw1241 := by apply Matrix.ext; unfold raw1239 raw1241; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4428 = raw1241Labels := by decide +kernel
    rw [ha, hj, canonical1241 B hB]
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

theorem singleton4507 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4507 node4507Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1091 node1091Labels + mixedMoment B node1756 node1756Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1305 singletonSmall4507
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4507) = raw1305Labels := by decide +kernel
  rw [hl, canonical1305 B hB] at h
  have hc0 : mixedMoment B raw1305 (Fin.cases (0 : Fin 2) singletonSmall4507) =
      mixedMoment B node1091 node1091Labels := by
    have ha : raw1305 = raw1306 := by apply Matrix.ext; unfold raw1305 raw1306; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4507 = raw1306Labels := by decide +kernel
    rw [ha, hj, canonical1306 B hB]
  have hc1 : mixedMoment B raw1305 (Fin.cases (1 : Fin 2) singletonSmall4507) =
      mixedMoment B node1756 node1756Labels := by
    have ha : raw1305 = raw1307 := by apply Matrix.ext; unfold raw1305 raw1307; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4507 = raw1307Labels := by decide +kernel
    rw [ha, hj, canonical1307 B hB]
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

theorem sound670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node670 node670Labels = Sparse.eval nodeValue670 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 670) = mixedMoment B node670 node670Labels := rfl
  simpa [nodeValue670, Sparse.eval] using hc.symm

theorem sound694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node694 node694Labels = Sparse.eval nodeValue694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 694) = mixedMoment B node694 node694Labels := rfl
  simpa [nodeValue694, Sparse.eval] using hc.symm

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

theorem sound716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node716 node716Labels = Sparse.eval nodeValue716 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 716) = mixedMoment B node716 node716Labels := rfl
  simpa [nodeValue716, Sparse.eval] using hc.symm

theorem sound729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node729 node729Labels = Sparse.eval nodeValue729 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 729) = mixedMoment B node729 node729Labels := rfl
  simpa [nodeValue729, Sparse.eval] using hc.symm

theorem sound752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node752 node752Labels = Sparse.eval nodeValue752 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 752) = mixedMoment B node752 node752Labels := rfl
  simpa [nodeValue752, Sparse.eval] using hc.symm

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

theorem sound773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node773 node773Labels = Sparse.eval nodeValue773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 773) = mixedMoment B node773 node773Labels := rfl
  simpa [nodeValue773, Sparse.eval] using hc.symm

theorem sound813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node813 node813Labels = Sparse.eval nodeValue813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 813) = mixedMoment B node813 node813Labels := rfl
  simpa [nodeValue813, Sparse.eval] using hc.symm

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

theorem sound853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node853 node853Labels = Sparse.eval nodeValue853 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 853) = mixedMoment B node853 node853Labels := rfl
  simpa [nodeValue853, Sparse.eval] using hc.symm

theorem sound860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node860 node860Labels = Sparse.eval nodeValue860 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 860) = mixedMoment B node860 node860Labels := rfl
  simpa [nodeValue860, Sparse.eval] using hc.symm

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

theorem sound1009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1009 node1009Labels = Sparse.eval nodeValue1009 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1009) = mixedMoment B node1009 node1009Labels := rfl
  simpa [nodeValue1009, Sparse.eval] using hc.symm

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

theorem sound1630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1630 node1630Labels = Sparse.eval nodeValue1630 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1630) = mixedMoment B node1630 node1630Labels := rfl
  simpa [nodeValue1630, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1756 node1756Labels = Sparse.eval nodeValue1756 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1756) = mixedMoment B node1756 node1756Labels := rfl
  simpa [nodeValue1756, Sparse.eval] using hc.symm

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

theorem sound556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node556 node556Labels = Sparse.eval nodeValue556 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 556) = mixedMoment B node556 node556Labels := rfl
  simpa [nodeValue556, Sparse.eval] using hc.symm

theorem sound566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node566 node566Labels = Sparse.eval nodeValue566 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 566) = mixedMoment B node566 node566Labels := rfl
  simpa [nodeValue566, Sparse.eval] using hc.symm

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

theorem sound4070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4070 node4070Labels = Sparse.eval nodeValue4070 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4070) = mixedMoment B node4070 node4070Labels := rfl
  simpa [nodeValue4070, Sparse.eval] using hc.symm

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

theorem zero4136 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4136 node4136Labels = 0 := by
  exact mixedMoment_order_one B hB node4136 node4136Labels 1
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

theorem sound4122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4122 node4122Labels = Sparse.eval nodeValue4122 (mixedVector B) := by
  have h := singleton4122 B _hB
  rw [sound556 B _hB _hF, sound670 B _hB _hF] at h
  norm_num [nodeValue4122, nodeValue556, nodeValue670, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4136 node4136Labels = Sparse.eval nodeValue4136 (mixedVector B) := by
  simpa only [nodeValue4136, Sparse.eval_nil] using zero4136 B _hB _hF

theorem sound4138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4138 node4138Labels = Sparse.eval nodeValue4138 (mixedVector B) := by
  have h := singleton4138 B _hB
  rw [sound566 B _hB _hF, sound694 B _hB _hF] at h
  norm_num [nodeValue4138, nodeValue566, nodeValue694, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4213 node4213Labels = Sparse.eval nodeValue4213 (mixedVector B) := by
  have h := singleton4213 B _hB
  rw [sound716 B _hB _hF, sound752 B _hB _hF] at h
  norm_num [nodeValue4213, nodeValue716, nodeValue752, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem zero4227 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4227 node4227Labels = 0 := by
  exact mixedMoment_order_one B hB node4227 node4227Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4269 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4269 node4269Labels = 0 := by
  exact mixedMoment_order_one B hB node4269 node4269Labels 1
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

theorem sound4227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4227 node4227Labels = Sparse.eval nodeValue4227 (mixedVector B) := by
  simpa only [nodeValue4227, Sparse.eval_nil] using zero4227 B _hB _hF

theorem sound4229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4229 node4229Labels = Sparse.eval nodeValue4229 (mixedVector B) := by
  have h := singleton4229 B _hB
  rw [sound729 B _hB _hF, sound773 B _hB _hF] at h
  norm_num [nodeValue4229, nodeValue729, nodeValue773, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4269 node4269Labels = Sparse.eval nodeValue4269 (mixedVector B) := by
  simpa only [nodeValue4269, Sparse.eval_nil] using zero4269 B _hB _hF

theorem sound4270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4270 node4270Labels = Sparse.eval nodeValue4270 (mixedVector B) := by
  have h := singleton4270 B _hB
  rw [sound813 B _hB _hF, sound853 B _hB _hF] at h
  norm_num [nodeValue4270, nodeValue813, nodeValue853, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4285 node4285Labels = Sparse.eval nodeValue4285 (mixedVector B) := by
  have h := singleton4285 B _hB
  rw [sound860 B _hB _hF] at h
  norm_num [nodeValue4285, nodeValue860, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4428 node4428Labels = Sparse.eval nodeValue4428 (mixedVector B) := by
  have h := singleton4428 B _hB
  rw [sound1009 B _hB _hF, sound1630 B _hB _hF] at h
  norm_num [nodeValue4428, nodeValue1009, nodeValue1630, Sparse.eval] at h ⊢
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

theorem zero4505 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4505 node4505Labels = 0 := by
  exact mixedMoment_order_one B hB node4505 node4505Labels 1
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

theorem sound4505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4505 node4505Labels = Sparse.eval nodeValue4505 (mixedVector B) := by
  simpa only [nodeValue4505, Sparse.eval_nil] using zero4505 B _hB _hF

theorem sound4507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4507 node4507Labels = Sparse.eval nodeValue4507 (mixedVector B) := by
  have h := singleton4507 B _hB
  rw [sound1091 B _hB _hF, sound1756 B _hB _hF] at h
  norm_num [nodeValue4507, nodeValue1091, nodeValue1756, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources44
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1438 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1438 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1438 + difference 0 1) (sourceB1438 + difference 1 0) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4428) := by
    have ha : (tripleCharges (sourceA1438 + difference 0 1) (sourceB1438 + difference 1 0) sourceC1438) = raw21750 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw21750; decide +kernel
    rw [ha]
    exact (canonical21750 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1438 + difference 0 2) (sourceB1438 + difference 2 0) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4428) := by
    have ha : (tripleCharges (sourceA1438 + difference 0 2) (sourceB1438 + difference 2 0) sourceC1438) = raw21751 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw21751; decide +kernel
    rw [ha]
    exact (canonical21751 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1438 + difference 0 3) (sourceB1438 + difference 3 0) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4428) := by
    have ha : (tripleCharges (sourceA1438 + difference 0 3) (sourceB1438 + difference 3 0) sourceC1438) = raw20803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw20803; decide +kernel
    rw [ha]
    exact (canonical20803 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1438 + difference 0 4) (sourceB1438 + difference 4 0) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4505) := by
    have ha : (tripleCharges (sourceA1438 + difference 0 4) (sourceB1438 + difference 4 0) sourceC1438) = raw20434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw20434; decide +kernel
    rw [ha]
    exact (canonical20434 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1438 + difference 0 5) (sourceB1438 + difference 5 0) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4507) := by
    have ha : (tripleCharges (sourceA1438 + difference 0 5) (sourceB1438 + difference 5 0) sourceC1438) = raw21309 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw21309; decide +kernel
    rw [ha]
    exact (canonical21309 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1438 + difference 1 0) (sourceB1438 + difference 0 1) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4122) := by
    have ha : (tripleCharges (sourceA1438 + difference 1 0) (sourceB1438 + difference 0 1) sourceC1438) = raw22216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22216; decide +kernel
    rw [ha]
    exact (canonical22216 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1438 + difference 1 2) (sourceB1438 + difference 2 1) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4213) := by
    have ha : (tripleCharges (sourceA1438 + difference 1 2) (sourceB1438 + difference 2 1) sourceC1438) = raw22217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22217; decide +kernel
    rw [ha]
    exact (canonical22217 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1438 + difference 1 3) (sourceB1438 + difference 3 1) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4213) := by
    have ha : (tripleCharges (sourceA1438 + difference 1 3) (sourceB1438 + difference 3 1) sourceC1438) = raw22218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22218; decide +kernel
    rw [ha]
    exact (canonical22218 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1438 + difference 1 4) (sourceB1438 + difference 4 1) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4269) := by
    have ha : (tripleCharges (sourceA1438 + difference 1 4) (sourceB1438 + difference 4 1) sourceC1438) = raw21313 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw21313; decide +kernel
    rw [ha]
    exact (canonical21313 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1438 + difference 1 5) (sourceB1438 + difference 5 1) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4270) := by
    have ha : (tripleCharges (sourceA1438 + difference 1 5) (sourceB1438 + difference 5 1) sourceC1438) = raw21308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw21308; decide +kernel
    rw [ha]
    exact (canonical21308 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1438 + difference 2 0) (sourceB1438 + difference 0 2) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4122) := by
    have ha : (tripleCharges (sourceA1438 + difference 2 0) (sourceB1438 + difference 0 2) sourceC1438) = raw22288 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22288; decide +kernel
    rw [ha]
    exact (canonical22288 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1438 + difference 2 1) (sourceB1438 + difference 1 2) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4213) := by
    have ha : (tripleCharges (sourceA1438 + difference 2 1) (sourceB1438 + difference 1 2) sourceC1438) = raw22289 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22289; decide +kernel
    rw [ha]
    exact (canonical22289 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1438 + difference 2 3) (sourceB1438 + difference 3 2) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4213) := by
    have ha : (tripleCharges (sourceA1438 + difference 2 3) (sourceB1438 + difference 3 2) sourceC1438) = raw22290 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22290; decide +kernel
    rw [ha]
    exact (canonical22290 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1438 + difference 2 4) (sourceB1438 + difference 4 2) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4269) := by
    have ha : (tripleCharges (sourceA1438 + difference 2 4) (sourceB1438 + difference 4 2) sourceC1438) = raw22211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22211; decide +kernel
    rw [ha]
    exact (canonical22211 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1438 + difference 2 5) (sourceB1438 + difference 5 2) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4270) := by
    have ha : (tripleCharges (sourceA1438 + difference 2 5) (sourceB1438 + difference 5 2) sourceC1438) = raw21736 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw21736; decide +kernel
    rw [ha]
    exact (canonical21736 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1438 + difference 3 0) (sourceB1438 + difference 0 3) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4122) := by
    have ha : (tripleCharges (sourceA1438 + difference 3 0) (sourceB1438 + difference 0 3) sourceC1438) = raw22291 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22291; decide +kernel
    rw [ha]
    exact (canonical22291 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1438 + difference 3 1) (sourceB1438 + difference 1 3) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4213) := by
    have ha : (tripleCharges (sourceA1438 + difference 3 1) (sourceB1438 + difference 1 3) sourceC1438) = raw22292 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22292; decide +kernel
    rw [ha]
    exact (canonical22292 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1438 + difference 3 2) (sourceB1438 + difference 2 3) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4213) := by
    have ha : (tripleCharges (sourceA1438 + difference 3 2) (sourceB1438 + difference 2 3) sourceC1438) = raw22293 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22293; decide +kernel
    rw [ha]
    exact (canonical22293 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1438 + difference 3 4) (sourceB1438 + difference 4 3) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4269) := by
    have ha : (tripleCharges (sourceA1438 + difference 3 4) (sourceB1438 + difference 4 3) sourceC1438) = raw22214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22214; decide +kernel
    rw [ha]
    exact (canonical22214 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1438 + difference 3 5) (sourceB1438 + difference 5 3) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4270) := by
    have ha : (tripleCharges (sourceA1438 + difference 3 5) (sourceB1438 + difference 5 3) sourceC1438) = raw21740 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw21740; decide +kernel
    rw [ha]
    exact (canonical21740 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1438 + difference 4 0) (sourceB1438 + difference 0 4) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4138) := by
    have ha : (tripleCharges (sourceA1438 + difference 4 0) (sourceB1438 + difference 0 4) sourceC1438) = raw22294 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22294; decide +kernel
    rw [ha]
    exact (canonical22294 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1438 + difference 4 1) (sourceB1438 + difference 1 4) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4229) := by
    have ha : (tripleCharges (sourceA1438 + difference 4 1) (sourceB1438 + difference 1 4) sourceC1438) = raw22295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22295; decide +kernel
    rw [ha]
    exact (canonical22295 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1438 + difference 4 2) (sourceB1438 + difference 2 4) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4229) := by
    have ha : (tripleCharges (sourceA1438 + difference 4 2) (sourceB1438 + difference 2 4) sourceC1438) = raw22296 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22296; decide +kernel
    rw [ha]
    exact (canonical22296 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1438 + difference 4 3) (sourceB1438 + difference 3 4) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4229) := by
    have ha : (tripleCharges (sourceA1438 + difference 4 3) (sourceB1438 + difference 3 4) sourceC1438) = raw22297 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22297; decide +kernel
    rw [ha]
    exact (canonical22297 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1438 + difference 4 5) (sourceB1438 + difference 5 4) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4285) := by
    have ha : (tripleCharges (sourceA1438 + difference 4 5) (sourceB1438 + difference 5 4) sourceC1438) = raw21744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw21744; decide +kernel
    rw [ha]
    exact (canonical21744 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1438 + difference 5 0) (sourceB1438 + difference 0 5) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4136) := by
    have ha : (tripleCharges (sourceA1438 + difference 5 0) (sourceB1438 + difference 0 5) sourceC1438) = raw22298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22298; decide +kernel
    rw [ha]
    exact (canonical22298 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1438 + difference 5 1) (sourceB1438 + difference 1 5) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4227) := by
    have ha : (tripleCharges (sourceA1438 + difference 5 1) (sourceB1438 + difference 1 5) sourceC1438) = raw22299 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22299; decide +kernel
    rw [ha]
    exact (canonical22299 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1438 + difference 5 2) (sourceB1438 + difference 2 5) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4227) := by
    have ha : (tripleCharges (sourceA1438 + difference 5 2) (sourceB1438 + difference 2 5) sourceC1438) = raw22300 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22300; decide +kernel
    rw [ha]
    exact (canonical22300 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1438 + difference 5 3) (sourceB1438 + difference 3 5) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4227) := by
    have ha : (tripleCharges (sourceA1438 + difference 5 3) (sourceB1438 + difference 3 5) sourceC1438) = raw21994 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw21994; decide +kernel
    rw [ha]
    exact (canonical21994 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1438 + difference 5 4) (sourceB1438 + difference 4 5) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1438 + difference 5 4) (sourceB1438 + difference 4 5) sourceC1438) = raw21991 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw21991; decide +kernel
    rw [ha]
    exact (canonical21991 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1438 sourceB1438 sourceC1438
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1438, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1233 : Integer.Sparse.reindex keyMap MixedData.row1233 = numericRow1233 := by decide +kernel

theorem numericCheck1233 (x : Master → ℝ) : Integer.Sparse.eval numericRow1233 x =
    (4 : ℝ) * reducedSource1233 x := by
  norm_num [numericRow1233, reducedSource1233, Integer.Sparse.eval, Sparse.eval, nodeValue4070, nodeValue4122, nodeValue4136, nodeValue4138, nodeValue4213, nodeValue4227, nodeValue4229, nodeValue4269, nodeValue4270, nodeValue4285, nodeValue4428, nodeValue4505, nodeValue4507] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1233 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1233 (mixedVector B) = 0 := by
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  have h4122 : mixedVector B (Sum.inr 4122) = Sparse.eval nodeValue4122 (mixedVector B) := by
    change mixedMoment B node4122 node4122Labels = _
    exact sound4122 B hB hF
  have h4136 : mixedVector B (Sum.inr 4136) = Sparse.eval nodeValue4136 (mixedVector B) := by
    change mixedMoment B node4136 node4136Labels = _
    exact sound4136 B hB hF
  have h4138 : mixedVector B (Sum.inr 4138) = Sparse.eval nodeValue4138 (mixedVector B) := by
    change mixedMoment B node4138 node4138Labels = _
    exact sound4138 B hB hF
  have h4213 : mixedVector B (Sum.inr 4213) = Sparse.eval nodeValue4213 (mixedVector B) := by
    change mixedMoment B node4213 node4213Labels = _
    exact sound4213 B hB hF
  have h4227 : mixedVector B (Sum.inr 4227) = Sparse.eval nodeValue4227 (mixedVector B) := by
    change mixedMoment B node4227 node4227Labels = _
    exact sound4227 B hB hF
  have h4229 : mixedVector B (Sum.inr 4229) = Sparse.eval nodeValue4229 (mixedVector B) := by
    change mixedMoment B node4229 node4229Labels = _
    exact sound4229 B hB hF
  have h4269 : mixedVector B (Sum.inr 4269) = Sparse.eval nodeValue4269 (mixedVector B) := by
    change mixedMoment B node4269 node4269Labels = _
    exact sound4269 B hB hF
  have h4270 : mixedVector B (Sum.inr 4270) = Sparse.eval nodeValue4270 (mixedVector B) := by
    change mixedMoment B node4270 node4270Labels = _
    exact sound4270 B hB hF
  have h4285 : mixedVector B (Sum.inr 4285) = Sparse.eval nodeValue4285 (mixedVector B) := by
    change mixedMoment B node4285 node4285Labels = _
    exact sound4285 B hB hF
  have h4428 : mixedVector B (Sum.inr 4428) = Sparse.eval nodeValue4428 (mixedVector B) := by
    change mixedMoment B node4428 node4428Labels = _
    exact sound4428 B hB hF
  have h4505 : mixedVector B (Sum.inr 4505) = Sparse.eval nodeValue4505 (mixedVector B) := by
    change mixedMoment B node4505 node4505Labels = _
    exact sound4505 B hB hF
  have h4507 : mixedVector B (Sum.inr 4507) = Sparse.eval nodeValue4507 (mixedVector B) := by
    change mixedMoment B node4507 node4507Labels = _
    exact sound4507 B hB hF
  simpa only [sourceForm1438, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4070, h4122, h4136, h4138, h4213, h4227, h4229, h4269, h4270, h4285, h4428, h4505, h4507, reducedSource1233] using sourceEq1438 B hB

theorem rowSound1233_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1233 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1233, numericCheck1233, reducedZero1233 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1233_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1233_e_oai
