-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound214_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T23:10:25.692217+00:00
-- url     : https://prove2.me/submissions/c6b650d9-4250-4cb4-9e61-c6451fe63c32

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3852_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw532 raw532Labels = mixedMoment B node3856 node3856Labels := by
  calc
    mixedMoment B raw532 raw532Labels = mixedMoment B raw532step0 raw532step0Labels := by
      have ha : raw532step0 = (fun i j => raw532 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw532step0 raw532; decide +kernel
      have hl : raw532step0Labels = raw532Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw532 raw532Labels permutation32 permutation5
    mixedMoment B raw532step0 raw532step0Labels = mixedMoment B raw532step1 raw532step1Labels := by
      have ha : raw532step1 = raw532step0 := by apply Matrix.ext; unfold raw532step1 raw532step0; decide +kernel
      have hl : raw532step0Labels = labelEmbedding1 ∘ raw532step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw532step0 raw532step0Labels raw532step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3856 node3856Labels := by rfl

theorem canonical533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw533 raw533Labels = mixedMoment B node468 node468Labels := by
  calc
    mixedMoment B raw533 raw533Labels = mixedMoment B raw533step0 raw533step0Labels := by
      have ha : raw533step0 = (fun i j => raw533 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw533step0 raw533; decide +kernel
      have hl : raw533step0Labels = raw533Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw533 raw533Labels permutation151 permutation4
    mixedMoment B raw533step0 raw533step0Labels = mixedMoment B raw533step1 raw533step1Labels := by
      have ha : raw533step1 = -raw533step0 := by apply Matrix.ext; change ∀ i j, raw533step1 i j = -(raw533step0 i j); unfold raw533step1 raw533step0; decide +kernel
      have hl : raw533step1Labels = raw533step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node468 node468Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6186 raw6186Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw6186 raw6186Labels = mixedMoment B raw6186step0 raw6186step0Labels := by
      have hz : ∀ j, raw6186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6186step0 = (fun i j => raw6186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6186step0 raw6186; decide +kernel
      have hl : raw6186step0Labels = raw6186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6186 raw6186Labels permutation346 hz
    mixedMoment B raw6186step0 raw6186step0Labels = mixedMoment B raw6186step1 raw6186step1Labels := by
      have ha : raw6186step1 = (fun i j => raw6186step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6186step1 raw6186step0; decide +kernel
      have hl : raw6186step1Labels = raw6186step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6186step0 raw6186step0Labels permutation36 permutation7
    mixedMoment B raw6186step1 raw6186step1Labels = mixedMoment B raw6186step2 raw6186step2Labels := by
      have ha : raw6186step2 = -raw6186step1 := by apply Matrix.ext; change ∀ i j, raw6186step2 i j = -(raw6186step1 i j); unfold raw6186step2 raw6186step1; decide +kernel
      have hl : raw6186step2Labels = raw6186step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6186step2 raw6186step2Labels = mixedMoment B raw6186step3 raw6186step3Labels := by
      have ha : raw6186step3 = raw6186step2 := by apply Matrix.ext; unfold raw6186step3 raw6186step2; decide +kernel
      have hl : raw6186step2Labels = labelEmbedding1 ∘ raw6186step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6186step2 raw6186step2Labels raw6186step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3813 node3813Labels := by rfl

theorem canonical6187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6187 raw6187Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw6187 raw6187Labels = mixedMoment B raw6187step0 raw6187step0Labels := by
      have ha : raw6187step0 = (fun i j => raw6187 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6187step0 raw6187; decide +kernel
      have hl : raw6187step0Labels = raw6187Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6187 raw6187Labels permutation156 permutation7
    mixedMoment B raw6187step0 raw6187step0Labels = mixedMoment B raw6187step1 raw6187step1Labels := by
      have ha : raw6187step1 = -raw6187step0 := by apply Matrix.ext; change ∀ i j, raw6187step1 i j = -(raw6187step0 i j); unfold raw6187step1 raw6187step0; decide +kernel
      have hl : raw6187step1Labels = raw6187step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6187step1 raw6187step1Labels = mixedMoment B raw6187step2 raw6187step2Labels := by
      have ha : raw6187step2 = raw6187step1 := by apply Matrix.ext; unfold raw6187step2 raw6187step1; decide +kernel
      have hl : raw6187step1Labels = labelEmbedding1 ∘ raw6187step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6187step1 raw6187step1Labels raw6187step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

theorem canonical6188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6188 raw6188Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw6188 raw6188Labels = mixedMoment B raw6188step0 raw6188step0Labels := by
      have hz : ∀ j, raw6188 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6188step0 = (fun i j => raw6188 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6188step0 raw6188; decide +kernel
      have hl : raw6188step0Labels = raw6188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6188 raw6188Labels permutation346 hz
    mixedMoment B raw6188step0 raw6188step0Labels = mixedMoment B raw6188step1 raw6188step1Labels := by
      have ha : raw6188step1 = (fun i j => raw6188step0 (permutation135 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6188step1 raw6188step0; decide +kernel
      have hl : raw6188step1Labels = raw6188step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6188step0 raw6188step0Labels permutation135 permutation5
    mixedMoment B raw6188step1 raw6188step1Labels = mixedMoment B raw6188step2 raw6188step2Labels := by
      have ha : raw6188step2 = raw6188step1 := by apply Matrix.ext; unfold raw6188step2 raw6188step1; decide +kernel
      have hl : raw6188step1Labels = labelEmbedding1 ∘ raw6188step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6188step1 raw6188step1Labels raw6188step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3854 node3854Labels := by rfl

theorem canonical6189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6189 raw6189Labels = mixedMoment B node3856 node3856Labels := by
  calc
    mixedMoment B raw6189 raw6189Labels = mixedMoment B raw6189step0 raw6189step0Labels := by
      have hz : ∀ j, raw6189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6189step0 = (fun i j => raw6189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6189step0 raw6189; decide +kernel
      have hl : raw6189step0Labels = raw6189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6189 raw6189Labels permutation346 hz
    mixedMoment B raw6189step0 raw6189step0Labels = mixedMoment B raw6189step1 raw6189step1Labels := by
      have ha : raw6189step1 = (fun i j => raw6189step0 (permutation134 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6189step1 raw6189step0; decide +kernel
      have hl : raw6189step1Labels = raw6189step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6189step0 raw6189step0Labels permutation134 permutation5
    mixedMoment B raw6189step1 raw6189step1Labels = mixedMoment B raw6189step2 raw6189step2Labels := by
      have ha : raw6189step2 = raw6189step1 := by apply Matrix.ext; unfold raw6189step2 raw6189step1; decide +kernel
      have hl : raw6189step1Labels = labelEmbedding1 ∘ raw6189step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6189step1 raw6189step1Labels raw6189step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3856 node3856Labels := by rfl

theorem canonical6190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6190 raw6190Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw6190 raw6190Labels = mixedMoment B raw6190step0 raw6190step0Labels := by
      have hz : ∀ j, raw6190 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6190step0 = (fun i j => raw6190 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6190step0 raw6190; decide +kernel
      have hl : raw6190step0Labels = raw6190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6190 raw6190Labels permutation346 hz
    mixedMoment B raw6190step0 raw6190step0Labels = mixedMoment B raw6190step1 raw6190step1Labels := by
      have ha : raw6190step1 = (fun i j => raw6190step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6190step1 raw6190step0; decide +kernel
      have hl : raw6190step1Labels = raw6190step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6190step0 raw6190step0Labels permutation36 permutation7
    mixedMoment B raw6190step1 raw6190step1Labels = mixedMoment B raw6190step2 raw6190step2Labels := by
      have ha : raw6190step2 = -raw6190step1 := by apply Matrix.ext; change ∀ i j, raw6190step2 i j = -(raw6190step1 i j); unfold raw6190step2 raw6190step1; decide +kernel
      have hl : raw6190step2Labels = raw6190step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6190step2 raw6190step2Labels = mixedMoment B raw6190step3 raw6190step3Labels := by
      have ha : raw6190step3 = raw6190step2 := by apply Matrix.ext; unfold raw6190step3 raw6190step2; decide +kernel
      have hl : raw6190step2Labels = labelEmbedding1 ∘ raw6190step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6190step2 raw6190step2Labels raw6190step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3852 node3852Labels := by rfl

theorem canonical6191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6191 raw6191Labels = mixedMoment B node3287 node3287Labels := by
  calc
    mixedMoment B raw6191 raw6191Labels = mixedMoment B raw6191step0 raw6191step0Labels := by
      have hz : ∀ j, raw6191 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6191step0 = (fun i j => raw6191 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6191step0 raw6191; decide +kernel
      have hl : raw6191step0Labels = raw6191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6191 raw6191Labels permutation346 hz
    mixedMoment B raw6191step0 raw6191step0Labels = mixedMoment B raw6191step1 raw6191step1Labels := by
      have ha : raw6191step1 = (fun i j => raw6191step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6191step1 raw6191step0; decide +kernel
      have hl : raw6191step1Labels = raw6191step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6191step0 raw6191step0Labels permutation40 permutation5
    mixedMoment B raw6191step1 raw6191step1Labels = mixedMoment B raw6191step2 raw6191step2Labels := by
      have ha : raw6191step2 = -raw6191step1 := by apply Matrix.ext; change ∀ i j, raw6191step2 i j = -(raw6191step1 i j); unfold raw6191step2 raw6191step1; decide +kernel
      have hl : raw6191step2Labels = raw6191step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6191step2 raw6191step2Labels = mixedMoment B raw6191step3 raw6191step3Labels := by
      have ha : raw6191step3 = raw6191step2 := by apply Matrix.ext; unfold raw6191step3 raw6191step2; decide +kernel
      have hl : raw6191step2Labels = labelEmbedding1 ∘ raw6191step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6191step2 raw6191step2Labels raw6191step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3287 node3287Labels := by rfl

theorem canonical6192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6192 raw6192Labels = mixedMoment B node3560 node3560Labels := by
  calc
    mixedMoment B raw6192 raw6192Labels = mixedMoment B raw6192step0 raw6192step0Labels := by
      have ha : raw6192step0 = (fun i j => raw6192 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6192step0 raw6192; decide +kernel
      have hl : raw6192step0Labels = raw6192Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6192 raw6192Labels permutation156 permutation7
    mixedMoment B raw6192step0 raw6192step0Labels = mixedMoment B raw6192step1 raw6192step1Labels := by
      have ha : raw6192step1 = -raw6192step0 := by apply Matrix.ext; change ∀ i j, raw6192step1 i j = -(raw6192step0 i j); unfold raw6192step1 raw6192step0; decide +kernel
      have hl : raw6192step1Labels = raw6192step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6192step1 raw6192step1Labels = mixedMoment B raw6192step2 raw6192step2Labels := by
      have ha : raw6192step2 = raw6192step1 := by apply Matrix.ext; unfold raw6192step2 raw6192step1; decide +kernel
      have hl : raw6192step1Labels = labelEmbedding1 ∘ raw6192step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6192step1 raw6192step1Labels raw6192step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3560 node3560Labels := by rfl

theorem canonical6193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6193 raw6193Labels = mixedMoment B node3575 node3575Labels := by
  calc
    mixedMoment B raw6193 raw6193Labels = mixedMoment B raw6193step0 raw6193step0Labels := by
      have hz : ∀ j, raw6193 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6193step0 = (fun i j => raw6193 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6193step0 raw6193; decide +kernel
      have hl : raw6193step0Labels = raw6193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6193 raw6193Labels permutation346 hz
    mixedMoment B raw6193step0 raw6193step0Labels = mixedMoment B raw6193step1 raw6193step1Labels := by
      have ha : raw6193step1 = (fun i j => raw6193step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6193step1 raw6193step0; decide +kernel
      have hl : raw6193step1Labels = raw6193step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6193step0 raw6193step0Labels permutation36 permutation7
    mixedMoment B raw6193step1 raw6193step1Labels = mixedMoment B raw6193step2 raw6193step2Labels := by
      have ha : raw6193step2 = -raw6193step1 := by apply Matrix.ext; change ∀ i j, raw6193step2 i j = -(raw6193step1 i j); unfold raw6193step2 raw6193step1; decide +kernel
      have hl : raw6193step2Labels = raw6193step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6193step2 raw6193step2Labels = mixedMoment B raw6193step3 raw6193step3Labels := by
      have ha : raw6193step3 = raw6193step2 := by apply Matrix.ext; unfold raw6193step3 raw6193step2; decide +kernel
      have hl : raw6193step2Labels = labelEmbedding1 ∘ raw6193step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6193step2 raw6193step2Labels raw6193step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3575 node3575Labels := by rfl

theorem canonical6194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6194 raw6194Labels = mixedMoment B node3577 node3577Labels := by
  calc
    mixedMoment B raw6194 raw6194Labels = mixedMoment B raw6194step0 raw6194step0Labels := by
      have hz : ∀ j, raw6194 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6194step0 = (fun i j => raw6194 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6194step0 raw6194; decide +kernel
      have hl : raw6194step0Labels = raw6194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6194 raw6194Labels permutation346 hz
    mixedMoment B raw6194step0 raw6194step0Labels = mixedMoment B raw6194step1 raw6194step1Labels := by
      have ha : raw6194step1 = (fun i j => raw6194step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6194step1 raw6194step0; decide +kernel
      have hl : raw6194step1Labels = raw6194step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6194step0 raw6194step0Labels permutation36 permutation7
    mixedMoment B raw6194step1 raw6194step1Labels = mixedMoment B raw6194step2 raw6194step2Labels := by
      have ha : raw6194step2 = -raw6194step1 := by apply Matrix.ext; change ∀ i j, raw6194step2 i j = -(raw6194step1 i j); unfold raw6194step2 raw6194step1; decide +kernel
      have hl : raw6194step2Labels = raw6194step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6194step2 raw6194step2Labels = mixedMoment B raw6194step3 raw6194step3Labels := by
      have ha : raw6194step3 = raw6194step2 := by apply Matrix.ext; unfold raw6194step3 raw6194step2; decide +kernel
      have hl : raw6194step2Labels = labelEmbedding1 ∘ raw6194step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6194step2 raw6194step2Labels raw6194step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3577 node3577Labels := by rfl

theorem canonical6195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6195 raw6195Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw6195 raw6195Labels = mixedMoment B raw6195step0 raw6195step0Labels := by
      have hz : ∀ j, raw6195 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6195step0 = (fun i j => raw6195 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6195step0 raw6195; decide +kernel
      have hl : raw6195step0Labels = raw6195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6195 raw6195Labels permutation346 hz
    mixedMoment B raw6195step0 raw6195step0Labels = mixedMoment B raw6195step1 raw6195step1Labels := by
      have ha : raw6195step1 = (fun i j => raw6195step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6195step1 raw6195step0; decide +kernel
      have hl : raw6195step1Labels = raw6195step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6195step0 raw6195step0Labels permutation36 permutation7
    mixedMoment B raw6195step1 raw6195step1Labels = mixedMoment B raw6195step2 raw6195step2Labels := by
      have ha : raw6195step2 = -raw6195step1 := by apply Matrix.ext; change ∀ i j, raw6195step2 i j = -(raw6195step1 i j); unfold raw6195step2 raw6195step1; decide +kernel
      have hl : raw6195step2Labels = raw6195step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6195step2 raw6195step2Labels = mixedMoment B raw6195step3 raw6195step3Labels := by
      have ha : raw6195step3 = raw6195step2 := by apply Matrix.ext; unfold raw6195step3 raw6195step2; decide +kernel
      have hl : raw6195step2Labels = labelEmbedding1 ∘ raw6195step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6195step2 raw6195step2Labels raw6195step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical6196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6196 raw6196Labels = mixedMoment B node3285 node3285Labels := by
  calc
    mixedMoment B raw6196 raw6196Labels = mixedMoment B raw6196step0 raw6196step0Labels := by
      have ha : raw6196step0 = (fun i j => raw6196 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6196step0 raw6196; decide +kernel
      have hl : raw6196step0Labels = raw6196Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6196 raw6196Labels permutation212 permutation5
    mixedMoment B raw6196step0 raw6196step0Labels = mixedMoment B raw6196step1 raw6196step1Labels := by
      have ha : raw6196step1 = -raw6196step0 := by apply Matrix.ext; change ∀ i j, raw6196step1 i j = -(raw6196step0 i j); unfold raw6196step1 raw6196step0; decide +kernel
      have hl : raw6196step1Labels = raw6196step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6196step1 raw6196step1Labels = mixedMoment B raw6196step2 raw6196step2Labels := by
      have ha : raw6196step2 = raw6196step1 := by apply Matrix.ext; unfold raw6196step2 raw6196step1; decide +kernel
      have hl : raw6196step1Labels = labelEmbedding1 ∘ raw6196step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6196step1 raw6196step1Labels raw6196step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3285 node3285Labels := by rfl

theorem canonical6197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6197 raw6197Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw6197 raw6197Labels = mixedMoment B raw6197step0 raw6197step0Labels := by
      have ha : raw6197step0 = (fun i j => raw6197 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6197step0 raw6197; decide +kernel
      have hl : raw6197step0Labels = raw6197Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6197 raw6197Labels permutation156 permutation7
    mixedMoment B raw6197step0 raw6197step0Labels = mixedMoment B raw6197step1 raw6197step1Labels := by
      have ha : raw6197step1 = -raw6197step0 := by apply Matrix.ext; change ∀ i j, raw6197step1 i j = -(raw6197step0 i j); unfold raw6197step1 raw6197step0; decide +kernel
      have hl : raw6197step1Labels = raw6197step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6197step1 raw6197step1Labels = mixedMoment B raw6197step2 raw6197step2Labels := by
      have ha : raw6197step2 = raw6197step1 := by apply Matrix.ext; unfold raw6197step2 raw6197step1; decide +kernel
      have hl : raw6197step1Labels = labelEmbedding1 ∘ raw6197step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6197step1 raw6197step1Labels raw6197step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

theorem canonical6198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6198 raw6198Labels = mixedMoment B node3527 node3527Labels := by
  calc
    mixedMoment B raw6198 raw6198Labels = mixedMoment B raw6198step0 raw6198step0Labels := by
      have ha : raw6198step0 = (fun i j => raw6198 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6198step0 raw6198; decide +kernel
      have hl : raw6198step0Labels = raw6198Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6198 raw6198Labels permutation156 permutation7
    mixedMoment B raw6198step0 raw6198step0Labels = mixedMoment B raw6198step1 raw6198step1Labels := by
      have ha : raw6198step1 = -raw6198step0 := by apply Matrix.ext; change ∀ i j, raw6198step1 i j = -(raw6198step0 i j); unfold raw6198step1 raw6198step0; decide +kernel
      have hl : raw6198step1Labels = raw6198step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6198step1 raw6198step1Labels = mixedMoment B raw6198step2 raw6198step2Labels := by
      have ha : raw6198step2 = raw6198step1 := by apply Matrix.ext; unfold raw6198step2 raw6198step1; decide +kernel
      have hl : raw6198step1Labels = labelEmbedding1 ∘ raw6198step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6198step1 raw6198step1Labels raw6198step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3527 node3527Labels := by rfl

theorem canonical6199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6199 raw6199Labels = mixedMoment B node3528 node3528Labels := by
  calc
    mixedMoment B raw6199 raw6199Labels = mixedMoment B raw6199step0 raw6199step0Labels := by
      have ha : raw6199step0 = (fun i j => raw6199 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6199step0 raw6199; decide +kernel
      have hl : raw6199step0Labels = raw6199Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6199 raw6199Labels permutation156 permutation7
    mixedMoment B raw6199step0 raw6199step0Labels = mixedMoment B raw6199step1 raw6199step1Labels := by
      have ha : raw6199step1 = -raw6199step0 := by apply Matrix.ext; change ∀ i j, raw6199step1 i j = -(raw6199step0 i j); unfold raw6199step1 raw6199step0; decide +kernel
      have hl : raw6199step1Labels = raw6199step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6199step1 raw6199step1Labels = mixedMoment B raw6199step2 raw6199step2Labels := by
      have ha : raw6199step2 = raw6199step1 := by apply Matrix.ext; unfold raw6199step2 raw6199step1; decide +kernel
      have hl : raw6199step1Labels = labelEmbedding1 ∘ raw6199step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6199step1 raw6199step1Labels raw6199step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3528 node3528Labels := by rfl

theorem canonical6200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6200 raw6200Labels = mixedMoment B node3525 node3525Labels := by
  calc
    mixedMoment B raw6200 raw6200Labels = mixedMoment B raw6200step0 raw6200step0Labels := by
      have ha : raw6200step0 = (fun i j => raw6200 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6200step0 raw6200; decide +kernel
      have hl : raw6200step0Labels = raw6200Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6200 raw6200Labels permutation156 permutation7
    mixedMoment B raw6200step0 raw6200step0Labels = mixedMoment B raw6200step1 raw6200step1Labels := by
      have ha : raw6200step1 = -raw6200step0 := by apply Matrix.ext; change ∀ i j, raw6200step1 i j = -(raw6200step0 i j); unfold raw6200step1 raw6200step0; decide +kernel
      have hl : raw6200step1Labels = raw6200step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6200step1 raw6200step1Labels = mixedMoment B raw6200step2 raw6200step2Labels := by
      have ha : raw6200step2 = raw6200step1 := by apply Matrix.ext; unfold raw6200step2 raw6200step1; decide +kernel
      have hl : raw6200step1Labels = labelEmbedding1 ∘ raw6200step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6200step1 raw6200step1Labels raw6200step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3525 node3525Labels := by rfl

theorem canonical6201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6201 raw6201Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw6201 raw6201Labels = mixedMoment B raw6201step0 raw6201step0Labels := by
      have hz : ∀ j, raw6201 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6201step0 = (fun i j => raw6201 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6201step0 raw6201; decide +kernel
      have hl : raw6201step0Labels = raw6201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6201 raw6201Labels permutation346 hz
    mixedMoment B raw6201step0 raw6201step0Labels = mixedMoment B raw6201step1 raw6201step1Labels := by
      have ha : raw6201step1 = (fun i j => raw6201step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6201step1 raw6201step0; decide +kernel
      have hl : raw6201step1Labels = raw6201step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6201step0 raw6201step0Labels permutation36 permutation7
    mixedMoment B raw6201step1 raw6201step1Labels = mixedMoment B raw6201step2 raw6201step2Labels := by
      have ha : raw6201step2 = -raw6201step1 := by apply Matrix.ext; change ∀ i j, raw6201step2 i j = -(raw6201step1 i j); unfold raw6201step2 raw6201step1; decide +kernel
      have hl : raw6201step2Labels = raw6201step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6201step2 raw6201step2Labels = mixedMoment B raw6201step3 raw6201step3Labels := by
      have ha : raw6201step3 = raw6201step2 := by apply Matrix.ext; unfold raw6201step3 raw6201step2; decide +kernel
      have hl : raw6201step2Labels = labelEmbedding1 ∘ raw6201step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6201step2 raw6201step2Labels raw6201step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

theorem canonical6202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6202 raw6202Labels = mixedMoment B node3479 node3479Labels := by
  calc
    mixedMoment B raw6202 raw6202Labels = mixedMoment B raw6202step0 raw6202step0Labels := by
      have hz : ∀ j, raw6202 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6202step0 = (fun i j => raw6202 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6202step0 raw6202; decide +kernel
      have hl : raw6202step0Labels = raw6202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6202 raw6202Labels permutation346 hz
    mixedMoment B raw6202step0 raw6202step0Labels = mixedMoment B raw6202step1 raw6202step1Labels := by
      have ha : raw6202step1 = (fun i j => raw6202step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6202step1 raw6202step0; decide +kernel
      have hl : raw6202step1Labels = raw6202step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6202step0 raw6202step0Labels permutation36 permutation7
    mixedMoment B raw6202step1 raw6202step1Labels = mixedMoment B raw6202step2 raw6202step2Labels := by
      have ha : raw6202step2 = -raw6202step1 := by apply Matrix.ext; change ∀ i j, raw6202step2 i j = -(raw6202step1 i j); unfold raw6202step2 raw6202step1; decide +kernel
      have hl : raw6202step2Labels = raw6202step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6202step2 raw6202step2Labels = mixedMoment B raw6202step3 raw6202step3Labels := by
      have ha : raw6202step3 = raw6202step2 := by apply Matrix.ext; unfold raw6202step3 raw6202step2; decide +kernel
      have hl : raw6202step2Labels = labelEmbedding1 ∘ raw6202step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6202step2 raw6202step2Labels raw6202step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3479 node3479Labels := by rfl

theorem canonical6203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6203 raw6203Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw6203 raw6203Labels = mixedMoment B raw6203step0 raw6203step0Labels := by
      have ha : raw6203step0 = (fun i j => raw6203 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6203step0 raw6203; decide +kernel
      have hl : raw6203step0Labels = raw6203Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6203 raw6203Labels permutation156 permutation7
    mixedMoment B raw6203step0 raw6203step0Labels = mixedMoment B raw6203step1 raw6203step1Labels := by
      have ha : raw6203step1 = -raw6203step0 := by apply Matrix.ext; change ∀ i j, raw6203step1 i j = -(raw6203step0 i j); unfold raw6203step1 raw6203step0; decide +kernel
      have hl : raw6203step1Labels = raw6203step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6203step1 raw6203step1Labels = mixedMoment B raw6203step2 raw6203step2Labels := by
      have ha : raw6203step2 = raw6203step1 := by apply Matrix.ext; unfold raw6203step2 raw6203step1; decide +kernel
      have hl : raw6203step1Labels = labelEmbedding1 ∘ raw6203step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6203step1 raw6203step1Labels raw6203step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3517 node3517Labels := by rfl

theorem canonical6204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6204 raw6204Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw6204 raw6204Labels = mixedMoment B raw6204step0 raw6204step0Labels := by
      have hz : ∀ j, raw6204 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6204step0 = (fun i j => raw6204 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6204step0 raw6204; decide +kernel
      have hl : raw6204step0Labels = raw6204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6204 raw6204Labels permutation346 hz
    mixedMoment B raw6204step0 raw6204step0Labels = mixedMoment B raw6204step1 raw6204step1Labels := by
      have ha : raw6204step1 = (fun i j => raw6204step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6204step1 raw6204step0; decide +kernel
      have hl : raw6204step1Labels = raw6204step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6204step0 raw6204step0Labels permutation36 permutation7
    mixedMoment B raw6204step1 raw6204step1Labels = mixedMoment B raw6204step2 raw6204step2Labels := by
      have ha : raw6204step2 = -raw6204step1 := by apply Matrix.ext; change ∀ i j, raw6204step2 i j = -(raw6204step1 i j); unfold raw6204step2 raw6204step1; decide +kernel
      have hl : raw6204step2Labels = raw6204step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6204step2 raw6204step2Labels = mixedMoment B raw6204step3 raw6204step3Labels := by
      have ha : raw6204step3 = raw6204step2 := by apply Matrix.ext; unfold raw6204step3 raw6204step2; decide +kernel
      have hl : raw6204step2Labels = labelEmbedding1 ∘ raw6204step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6204step2 raw6204step2Labels raw6204step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

theorem canonical6205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6205 raw6205Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw6205 raw6205Labels = mixedMoment B raw6205step0 raw6205step0Labels := by
      have hz : ∀ j, raw6205 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6205step0 = (fun i j => raw6205 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6205step0 raw6205; decide +kernel
      have hl : raw6205step0Labels = raw6205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6205 raw6205Labels permutation346 hz
    mixedMoment B raw6205step0 raw6205step0Labels = mixedMoment B raw6205step1 raw6205step1Labels := by
      have ha : raw6205step1 = (fun i j => raw6205step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6205step1 raw6205step0; decide +kernel
      have hl : raw6205step1Labels = raw6205step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6205step0 raw6205step0Labels permutation36 permutation7
    mixedMoment B raw6205step1 raw6205step1Labels = mixedMoment B raw6205step2 raw6205step2Labels := by
      have ha : raw6205step2 = -raw6205step1 := by apply Matrix.ext; change ∀ i j, raw6205step2 i j = -(raw6205step1 i j); unfold raw6205step2 raw6205step1; decide +kernel
      have hl : raw6205step2Labels = raw6205step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6205step2 raw6205step2Labels = mixedMoment B raw6205step3 raw6205step3Labels := by
      have ha : raw6205step3 = raw6205step2 := by apply Matrix.ext; unfold raw6205step3 raw6205step2; decide +kernel
      have hl : raw6205step2Labels = labelEmbedding1 ∘ raw6205step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6205step2 raw6205step2Labels raw6205step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

theorem canonical6206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6206 raw6206Labels = mixedMoment B node3295 node3295Labels := by
  calc
    mixedMoment B raw6206 raw6206Labels = mixedMoment B raw6206step0 raw6206step0Labels := by
      have hz : ∀ j, raw6206 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6206step0 = (fun i j => raw6206 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6206step0 raw6206; decide +kernel
      have hl : raw6206step0Labels = raw6206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6206 raw6206Labels permutation346 hz
    mixedMoment B raw6206step0 raw6206step0Labels = mixedMoment B raw6206step1 raw6206step1Labels := by
      have ha : raw6206step1 = (fun i j => raw6206step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6206step1 raw6206step0; decide +kernel
      have hl : raw6206step1Labels = raw6206step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6206step0 raw6206step0Labels permutation40 permutation5
    mixedMoment B raw6206step1 raw6206step1Labels = mixedMoment B raw6206step2 raw6206step2Labels := by
      have ha : raw6206step2 = -raw6206step1 := by apply Matrix.ext; change ∀ i j, raw6206step2 i j = -(raw6206step1 i j); unfold raw6206step2 raw6206step1; decide +kernel
      have hl : raw6206step2Labels = raw6206step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6206step2 raw6206step2Labels = mixedMoment B raw6206step3 raw6206step3Labels := by
      have ha : raw6206step3 = raw6206step2 := by apply Matrix.ext; unfold raw6206step3 raw6206step2; decide +kernel
      have hl : raw6206step2Labels = labelEmbedding1 ∘ raw6206step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6206step2 raw6206step2Labels raw6206step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3295 node3295Labels := by rfl

theorem canonical6207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6207 raw6207Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw6207 raw6207Labels = mixedMoment B raw6207step0 raw6207step0Labels := by
      have hz : ∀ j, raw6207 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6207step0 = (fun i j => raw6207 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6207step0 raw6207; decide +kernel
      have hl : raw6207step0Labels = raw6207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6207 raw6207Labels permutation346 hz
    mixedMoment B raw6207step0 raw6207step0Labels = mixedMoment B raw6207step1 raw6207step1Labels := by
      have ha : raw6207step1 = (fun i j => raw6207step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6207step1 raw6207step0; decide +kernel
      have hl : raw6207step1Labels = raw6207step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6207step0 raw6207step0Labels permutation36 permutation7
    mixedMoment B raw6207step1 raw6207step1Labels = mixedMoment B raw6207step2 raw6207step2Labels := by
      have ha : raw6207step2 = -raw6207step1 := by apply Matrix.ext; change ∀ i j, raw6207step2 i j = -(raw6207step1 i j); unfold raw6207step2 raw6207step1; decide +kernel
      have hl : raw6207step2Labels = raw6207step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6207step2 raw6207step2Labels = mixedMoment B raw6207step3 raw6207step3Labels := by
      have ha : raw6207step3 = raw6207step2 := by apply Matrix.ext; unfold raw6207step3 raw6207step2; decide +kernel
      have hl : raw6207step2Labels = labelEmbedding1 ∘ raw6207step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6207step2 raw6207step2Labels raw6207step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3478 node3478Labels := by rfl

theorem canonical6208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6208 raw6208Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw6208 raw6208Labels = mixedMoment B raw6208step0 raw6208step0Labels := by
      have ha : raw6208step0 = (fun i j => raw6208 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6208step0 raw6208; decide +kernel
      have hl : raw6208step0Labels = raw6208Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6208 raw6208Labels permutation156 permutation7
    mixedMoment B raw6208step0 raw6208step0Labels = mixedMoment B raw6208step1 raw6208step1Labels := by
      have ha : raw6208step1 = -raw6208step0 := by apply Matrix.ext; change ∀ i j, raw6208step1 i j = -(raw6208step0 i j); unfold raw6208step1 raw6208step0; decide +kernel
      have hl : raw6208step1Labels = raw6208step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6208step1 raw6208step1Labels = mixedMoment B raw6208step2 raw6208step2Labels := by
      have ha : raw6208step2 = raw6208step1 := by apply Matrix.ext; unfold raw6208step2 raw6208step1; decide +kernel
      have hl : raw6208step1Labels = labelEmbedding1 ∘ raw6208step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6208step1 raw6208step1Labels raw6208step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

theorem canonical6209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6209 raw6209Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw6209 raw6209Labels = mixedMoment B raw6209step0 raw6209step0Labels := by
      have hz : ∀ j, raw6209 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6209step0 = (fun i j => raw6209 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6209step0 raw6209; decide +kernel
      have hl : raw6209step0Labels = raw6209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6209 raw6209Labels permutation346 hz
    mixedMoment B raw6209step0 raw6209step0Labels = mixedMoment B raw6209step1 raw6209step1Labels := by
      have ha : raw6209step1 = (fun i j => raw6209step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6209step1 raw6209step0; decide +kernel
      have hl : raw6209step1Labels = raw6209step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6209step0 raw6209step0Labels permutation36 permutation7
    mixedMoment B raw6209step1 raw6209step1Labels = mixedMoment B raw6209step2 raw6209step2Labels := by
      have ha : raw6209step2 = -raw6209step1 := by apply Matrix.ext; change ∀ i j, raw6209step2 i j = -(raw6209step1 i j); unfold raw6209step2 raw6209step1; decide +kernel
      have hl : raw6209step2Labels = raw6209step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6209step2 raw6209step2Labels = mixedMoment B raw6209step3 raw6209step3Labels := by
      have ha : raw6209step3 = raw6209step2 := by apply Matrix.ext; unfold raw6209step3 raw6209step2; decide +kernel
      have hl : raw6209step2Labels = labelEmbedding1 ∘ raw6209step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6209step2 raw6209step2Labels raw6209step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3538 node3538Labels := by rfl

theorem canonical6210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6210 raw6210Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw6210 raw6210Labels = mixedMoment B raw6210step0 raw6210step0Labels := by
      have hz : ∀ j, raw6210 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6210step0 = (fun i j => raw6210 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6210step0 raw6210; decide +kernel
      have hl : raw6210step0Labels = raw6210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6210 raw6210Labels permutation346 hz
    mixedMoment B raw6210step0 raw6210step0Labels = mixedMoment B raw6210step1 raw6210step1Labels := by
      have ha : raw6210step1 = (fun i j => raw6210step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6210step1 raw6210step0; decide +kernel
      have hl : raw6210step1Labels = raw6210step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6210step0 raw6210step0Labels permutation36 permutation7
    mixedMoment B raw6210step1 raw6210step1Labels = mixedMoment B raw6210step2 raw6210step2Labels := by
      have ha : raw6210step2 = -raw6210step1 := by apply Matrix.ext; change ∀ i j, raw6210step2 i j = -(raw6210step1 i j); unfold raw6210step2 raw6210step1; decide +kernel
      have hl : raw6210step2Labels = raw6210step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6210step2 raw6210step2Labels = mixedMoment B raw6210step3 raw6210step3Labels := by
      have ha : raw6210step3 = raw6210step2 := by apply Matrix.ext; unfold raw6210step3 raw6210step2; decide +kernel
      have hl : raw6210step2Labels = labelEmbedding1 ∘ raw6210step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6210step2 raw6210step2Labels raw6210step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical6211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6211 raw6211Labels = mixedMoment B node2045 node2045Labels := by
  calc
    mixedMoment B raw6211 raw6211Labels = mixedMoment B raw6211step0 raw6211step0Labels := by
      have hz : ∀ j, raw6211 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6211step0 = (fun i j => raw6211 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6211step0 raw6211; decide +kernel
      have hl : raw6211step0Labels = raw6211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6211 raw6211Labels permutation346 hz
    mixedMoment B raw6211step0 raw6211step0Labels = mixedMoment B raw6211step1 raw6211step1Labels := by
      have ha : raw6211step1 = (fun i j => raw6211step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6211step1 raw6211step0; decide +kernel
      have hl : raw6211step1Labels = raw6211step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6211step0 raw6211step0Labels permutation139 permutation5
    mixedMoment B raw6211step1 raw6211step1Labels = mixedMoment B raw6211step2 raw6211step2Labels := by
      have ha : raw6211step2 = raw6211step1 := by apply Matrix.ext; unfold raw6211step2 raw6211step1; decide +kernel
      have hl : raw6211step1Labels = labelEmbedding1 ∘ raw6211step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6211step1 raw6211step1Labels raw6211step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2045 node2045Labels := by rfl

theorem canonical6212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6212 raw6212Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw6212 raw6212Labels = mixedMoment B raw6212step0 raw6212step0Labels := by
      have hz : ∀ j, raw6212 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6212step0 = (fun i j => raw6212 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6212step0 raw6212; decide +kernel
      have hl : raw6212step0Labels = raw6212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6212 raw6212Labels permutation346 hz
    mixedMoment B raw6212step0 raw6212step0Labels = mixedMoment B raw6212step1 raw6212step1Labels := by
      have ha : raw6212step1 = (fun i j => raw6212step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6212step1 raw6212step0; decide +kernel
      have hl : raw6212step1Labels = raw6212step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6212step0 raw6212step0Labels permutation139 permutation5
    mixedMoment B raw6212step1 raw6212step1Labels = mixedMoment B raw6212step2 raw6212step2Labels := by
      have ha : raw6212step2 = raw6212step1 := by apply Matrix.ext; unfold raw6212step2 raw6212step1; decide +kernel
      have hl : raw6212step1Labels = labelEmbedding1 ∘ raw6212step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6212step1 raw6212step1Labels raw6212step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

theorem canonical6213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6213 raw6213Labels = mixedMoment B node2043 node2043Labels := by
  calc
    mixedMoment B raw6213 raw6213Labels = mixedMoment B raw6213step0 raw6213step0Labels := by
      have ha : raw6213step0 = (fun i j => raw6213 (permutation622 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6213step0 raw6213; decide +kernel
      have hl : raw6213step0Labels = raw6213Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6213 raw6213Labels permutation622 permutation5
    mixedMoment B raw6213step0 raw6213step0Labels = mixedMoment B raw6213step1 raw6213step1Labels := by
      have ha : raw6213step1 = raw6213step0 := by apply Matrix.ext; unfold raw6213step1 raw6213step0; decide +kernel
      have hl : raw6213step0Labels = labelEmbedding1 ∘ raw6213step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6213step0 raw6213step0Labels raw6213step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2043 node2043Labels := by rfl

theorem canonical6214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6214 raw6214Labels = mixedMoment B node2049 node2049Labels := by
  calc
    mixedMoment B raw6214 raw6214Labels = mixedMoment B raw6214step0 raw6214step0Labels := by
      have hz : ∀ j, raw6214 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6214step0 = (fun i j => raw6214 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6214step0 raw6214; decide +kernel
      have hl : raw6214step0Labels = raw6214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6214 raw6214Labels permutation346 hz
    mixedMoment B raw6214step0 raw6214step0Labels = mixedMoment B raw6214step1 raw6214step1Labels := by
      have ha : raw6214step1 = (fun i j => raw6214step0 (permutation138 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6214step1 raw6214step0; decide +kernel
      have hl : raw6214step1Labels = raw6214step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6214step0 raw6214step0Labels permutation138 permutation5
    mixedMoment B raw6214step1 raw6214step1Labels = mixedMoment B raw6214step2 raw6214step2Labels := by
      have ha : raw6214step2 = raw6214step1 := by apply Matrix.ext; unfold raw6214step2 raw6214step1; decide +kernel
      have hl : raw6214step1Labels = labelEmbedding1 ∘ raw6214step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6214step1 raw6214step1Labels raw6214step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2049 node2049Labels := by rfl

theorem canonical6215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6215 raw6215Labels = mixedMoment B node2055 node2055Labels := by
  calc
    mixedMoment B raw6215 raw6215Labels = mixedMoment B raw6215step0 raw6215step0Labels := by
      have hz : ∀ j, raw6215 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6215step0 = (fun i j => raw6215 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6215step0 raw6215; decide +kernel
      have hl : raw6215step0Labels = raw6215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6215 raw6215Labels permutation346 hz
    mixedMoment B raw6215step0 raw6215step0Labels = mixedMoment B raw6215step1 raw6215step1Labels := by
      have ha : raw6215step1 = (fun i j => raw6215step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6215step1 raw6215step0; decide +kernel
      have hl : raw6215step1Labels = raw6215step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6215step0 raw6215step0Labels permutation136 permutation5
    mixedMoment B raw6215step1 raw6215step1Labels = mixedMoment B raw6215step2 raw6215step2Labels := by
      have ha : raw6215step2 = raw6215step1 := by apply Matrix.ext; unfold raw6215step2 raw6215step1; decide +kernel
      have hl : raw6215step1Labels = labelEmbedding1 ∘ raw6215step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6215step1 raw6215step1Labels raw6215step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2055 node2055Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3928 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3928 = injectiveMoment H node656 := by
  calc
    injectiveMoment H raw3928 = injectiveMoment H raw3928step0 := by
      have heq : raw3928step0 = (fun i j => raw3928 (permutation147 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3928 permutation147 permutation6
    _ = injectiveMoment H node656 := by rfl

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

theorem canonical5128 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5128 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5128 = injectiveMoment H raw5128step0 := by
      have hz : ∀ j, raw5128 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5128step0 = (fun i j => raw5128 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5128 permutation80 hz
    _ = injectiveMoment H node46 := by rfl

theorem canonical5150 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5150 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5150 = injectiveMoment H raw5150step0 := by
      have hz : ∀ j, raw5150 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw5150step0 = (fun i j => raw5150 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5150 permutation128 hz
    injectiveMoment H raw5150step0 = injectiveMoment H raw5150step1 := by
      have heq : raw5150step1 = (fun i j => raw5150step0 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5150step0 permutation10 permutation1
    _ = injectiveMoment H node46 := by rfl

end MUB6.Certificate.PairSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7981 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7981 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7981 = injectiveMoment H raw7981step0 := by
      have hz : ∀ j, raw7981 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7981step0 = (fun i j => raw7981 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981 permutation128 hz
    injectiveMoment H raw7981step0 = injectiveMoment H raw7981step1 := by
      have hz : ∀ j, raw7981step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7981step1 = (fun i j => raw7981step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step0 permutation27 hz
    injectiveMoment H raw7981step1 = injectiveMoment H raw7981step2 := by
      have hz : ∀ j, raw7981step1 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7981step2 = (fun i j => raw7981step1 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step1 permutation7 hz
    injectiveMoment H raw7981step2 = injectiveMoment H raw7981step3 := by
      have hz : ∀ j, raw7981step2 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7981step3 = (fun i j => raw7981step2 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step2 permutation2 hz
    injectiveMoment H raw7981step3 = injectiveMoment H raw7981step4 := by
      have hz : ∀ j, raw7981step3 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7981step4 = (fun i j => raw7981step3 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step3 permutation0 hz
    injectiveMoment H raw7981step4 = injectiveMoment H raw7981step5 := by
      have hz : ∀ i, raw7981step4 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7981step5 = (fun i j => raw7981step4 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7981step4 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical282
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9036 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9036 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw9036 = injectiveMoment H raw9036step0 := by
      have hz : ∀ j, raw9036 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw9036step0 = (fun i j => raw9036 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9036 permutation104 hz
    injectiveMoment H raw9036step0 = injectiveMoment H raw9036step1 := by
      have hz : ∀ j, raw9036step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw9036step1 = (fun i j => raw9036step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9036step0 permutation15 hz
    injectiveMoment H raw9036step1 = injectiveMoment H raw9036step2 := by
      have hz : ∀ j, raw9036step1 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw9036step2 = (fun i j => raw9036step1 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9036step1 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

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

theorem canonical5210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5210 = injectiveMoment H node4 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical215
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6885 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6885 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw6885 = injectiveMoment H raw6885step0 := by
      have heq : raw6885step0 = raw6885.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6885).symm
    injectiveMoment H raw6885step0 = injectiveMoment H raw6885step1 := by
      have heq : raw6885step1 = (fun i j => raw6885step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6885step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical256
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8215 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8215 = injectiveMoment H raw8215step0 := by
      have hz : ∀ i, raw8215 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8215step0 = (fun i j => raw8215 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8215 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound37 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node37 = Sparse.eval value37 (momentVector H) := by
  have hc : momentVector H 13 = injectiveMoment H node37 := rfl
  simp [value37, Sparse.eval, hc]

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

theorem sound46 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node46 = Sparse.eval value46 (momentVector H) := by
  have heq : pivotMatrix46 = (fun u v => node46 (pivotPermutation46 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node46 = injectiveMoment H pivotMatrix46 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix46 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix46 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix46 (0 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (0 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix46 (1 : Fin 3)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (1 : Fin 3) = raw5183 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5183 hH).trans (sound4 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix46 (2 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (2 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node46 + (injectiveMoment H (mergeFirst pivotMatrix46 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix46 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix46 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value46, value10, value11, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound62 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node62 = Sparse.eval value62 (momentVector H) := by
  have heq : pivotMatrix62 = (fun u v => node62 (pivotPermutation62 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node62 = injectiveMoment H pivotMatrix62 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix62 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix62 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix62 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix62 (0 : Fin 2) = raw8215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8215 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix62 (1 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix62 (1 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node62 + (injectiveMoment H (mergeFirst pivotMatrix62 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix62 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value62, value11, value4, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4134 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4134 = injectiveMoment H raw4134step0 := by
      have heq : raw4134step0 = (fun i j => raw4134 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4134 permutation7 permutation6
    _ = injectiveMoment H node62 := by rfl

theorem canonical4141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4141 = injectiveMoment H node41 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2849 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2849 = injectiveMoment H node37 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4099 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4099 = injectiveMoment H node41 := by
  calc
    injectiveMoment H raw4099 = injectiveMoment H raw4099step0 := by
      have hz : ∀ j, raw4099 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw4099step0 = (fun i j => raw4099 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4099 permutation15 hz
    _ = injectiveMoment H node41 := by rfl

theorem canonical4117 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4117 = injectiveMoment H node207 := by
  rfl

theorem canonical4123 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4123 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw4123 = injectiveMoment H raw4123step0 := by
      have heq : raw4123step0 = -raw4123 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4123).symm
    injectiveMoment H raw4123step0 = injectiveMoment H raw4123step1 := by
      have heq : raw4123step1 = (fun i j => raw4123step0 (permutation30 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4123step0 permutation30 permutation4
    _ = injectiveMoment H node177 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4956 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4956 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4956 = injectiveMoment H raw4956step0 := by
      have heq : raw4956step0 = -raw4956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4956).symm
    injectiveMoment H raw4956step0 = injectiveMoment H raw4956step1 := by
      have heq : raw4956step1 = (fun i j => raw4956step0 (permutation4 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4956step0 permutation4 permutation8
    _ = injectiveMoment H node62 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2811 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2811 = injectiveMoment H node177 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2845 = injectiveMoment H node36 := by
  rfl

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

theorem sound177 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node177 = Sparse.eval value177 (momentVector H) := by
  have heq : pivotMatrix177 = (fun u v => node177 (pivotPermutation177 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node177 = injectiveMoment H pivotMatrix177 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix177 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix177 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix177 (0 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix177 (0 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix177 (1 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix177 (1 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix177 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix177 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node177 + (injectiveMoment H (mergeFirst pivotMatrix177 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix177 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix177 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value177, value36, value37, value41, Sparse.eval] at hc ⊢
  linarith

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

theorem sound207 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node207 = Sparse.eval value207 (momentVector H) := by
  have heq : pivotMatrix207 = (fun u v => node207 (pivotPermutation207 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node207 = injectiveMoment H pivotMatrix207 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix207 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix207 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix207 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix207 (0 : Fin 3) = raw4956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4956 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix207 (1 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix207 (1 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix207 (2 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix207 (2 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node207 + (injectiveMoment H (mergeFirst pivotMatrix207 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix207 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix207 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value207, value41, value62, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound10
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound656 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node656 = Sparse.eval value656 (momentVector H) := by
  have heq : pivotMatrix656 = (fun u v => node656 (pivotPermutation656 u) v) := by apply Matrix.ext; unfold pivotMatrix656 node656 pivotPermutation656; decide +kernel
  have hmoment : injectiveMoment H node656 = injectiveMoment H pivotMatrix656 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix656 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix656 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix656 (0 : Fin 4)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix656 (0 : Fin 4) = raw2811 := by apply Matrix.ext; unfold mergeFirst pivotMatrix656 raw2811; decide +kernel
    rw [heq]
    exact (canonical2811 hH).trans (sound177 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix656 (1 : Fin 4)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix656 (1 : Fin 4) = raw4099 := by apply Matrix.ext; unfold mergeFirst pivotMatrix656 raw4099; decide +kernel
    rw [heq]
    exact (canonical4099 hH).trans (sound41 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix656 (2 : Fin 4)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix656 (2 : Fin 4) = raw4117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix656 raw4117; decide +kernel
    rw [heq]
    exact (canonical4117 hH).trans (sound207 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix656 (3 : Fin 4)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix656 (3 : Fin 4) = raw4123 := by apply Matrix.ext; unfold mergeFirst pivotMatrix656 raw4123; decide +kernel
    rw [heq]
    exact (canonical4123 hH).trans (sound177 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node656 + (injectiveMoment H (mergeFirst pivotMatrix656 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix656 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix656 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix656 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value656, value177, value207, value41, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair468 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node468 node468Labels = Sparse.eval singlePairValue468 (familyPairVector B) := by
  have hp := single_label_three B hB node468
  have hl : node468Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node468 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node468 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node468 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node468 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node468 (EqualityPatterns.family3.label 1) = PairSemantics.raw5150 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node468 PairSemantics.raw5150; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5150 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node468 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node468 (EqualityPatterns.family3.label 2) = PairSemantics.raw9036 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node468 PairSemantics.raw9036; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9036 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node468 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node468 (EqualityPatterns.family3.label 3) = PairSemantics.raw5128 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node468 PairSemantics.raw5128; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5128 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node468 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value656 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node468 (EqualityPatterns.family3.label 4) = PairSemantics.raw3928 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node468 PairSemantics.raw3928; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3928 hH).trans (PairSemantics.sound656 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue468, PairSemantics.value0, PairSemantics.value4, PairSemantics.value46, PairSemantics.value656, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3856 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3856 node3856Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node468 node468Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw532 singletonSmall3856
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3856) = raw532Labels := by decide +kernel
  rw [hl, canonical532 B hB] at h
  have hc0 : mixedMoment B raw532 (Fin.cases (0 : Fin 1) singletonSmall3856) =
      mixedMoment B node468 node468Labels := by
    have ha : raw532 = raw533 := by apply Matrix.ext; unfold raw532 raw533; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3856 = raw533Labels := by decide +kernel
    rw [ha, hj, canonical533 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2043 node2043Labels = Sparse.eval nodeValue2043 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2043) = mixedMoment B node2043 node2043Labels := rfl
  simpa [nodeValue2043, Sparse.eval] using hc.symm

theorem sound2045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2045 node2045Labels = Sparse.eval nodeValue2045 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2045) = mixedMoment B node2045 node2045Labels := rfl
  simpa [nodeValue2045, Sparse.eval] using hc.symm

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

theorem sound2049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2049 node2049Labels = Sparse.eval nodeValue2049 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2049) = mixedMoment B node2049 node2049Labels := rfl
  simpa [nodeValue2049, Sparse.eval] using hc.symm

theorem sound2055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2055 node2055Labels = Sparse.eval nodeValue2055 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2055) = mixedMoment B node2055 node2055Labels := rfl
  simpa [nodeValue2055, Sparse.eval] using hc.symm

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

theorem sound2259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2259 node2259Labels = Sparse.eval nodeValue2259 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2259) = mixedMoment B node2259 node2259Labels := rfl
  simpa [nodeValue2259, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3285 node3285Labels = Sparse.eval nodeValue3285 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3285) = mixedMoment B node3285 node3285Labels := rfl
  simpa [nodeValue3285, Sparse.eval] using hc.symm

theorem sound3287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3287 node3287Labels = Sparse.eval nodeValue3287 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3287) = mixedMoment B node3287 node3287Labels := rfl
  simpa [nodeValue3287, Sparse.eval] using hc.symm

theorem sound3295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3295 node3295Labels = Sparse.eval nodeValue3295 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3295) = mixedMoment B node3295 node3295Labels := rfl
  simpa [nodeValue3295, Sparse.eval] using hc.symm

theorem sound3296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3296 node3296Labels = Sparse.eval nodeValue3296 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3296) = mixedMoment B node3296 node3296Labels := rfl
  simpa [nodeValue3296, Sparse.eval] using hc.symm

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

theorem sound3463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3463 node3463Labels = Sparse.eval nodeValue3463 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3463) = mixedMoment B node3463 node3463Labels := rfl
  simpa [nodeValue3463, Sparse.eval] using hc.symm

theorem sound3478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3478 node3478Labels = Sparse.eval nodeValue3478 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3478) = mixedMoment B node3478 node3478Labels := rfl
  simpa [nodeValue3478, Sparse.eval] using hc.symm

theorem sound3479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3479 node3479Labels = Sparse.eval nodeValue3479 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3479) = mixedMoment B node3479 node3479Labels := rfl
  simpa [nodeValue3479, Sparse.eval] using hc.symm

theorem sound3516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3516 node3516Labels = Sparse.eval nodeValue3516 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3516) = mixedMoment B node3516 node3516Labels := rfl
  simpa [nodeValue3516, Sparse.eval] using hc.symm

theorem sound3517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3517 node3517Labels = Sparse.eval nodeValue3517 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3517) = mixedMoment B node3517 node3517Labels := rfl
  simpa [nodeValue3517, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3525 node3525Labels = 0 := by
  exact mixedMoment_alpha B hF node3525 node3525Labels 1 permutation434
    (by decide +kernel)

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

theorem sound3525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3525 node3525Labels = Sparse.eval nodeValue3525 (mixedVector B) := by
  simpa only [nodeValue3525, Sparse.eval_nil] using zero3525 B _hB _hF

theorem sound3527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3527 node3527Labels = Sparse.eval nodeValue3527 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3527) = mixedMoment B node3527 node3527Labels := rfl
  simpa [nodeValue3527, Sparse.eval] using hc.symm

theorem sound3528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3528 node3528Labels = Sparse.eval nodeValue3528 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3528) = mixedMoment B node3528 node3528Labels := rfl
  simpa [nodeValue3528, Sparse.eval] using hc.symm

theorem sound3533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3533 node3533Labels = Sparse.eval nodeValue3533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3533) = mixedMoment B node3533 node3533Labels := rfl
  simpa [nodeValue3533, Sparse.eval] using hc.symm

theorem sound3534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3534 node3534Labels = Sparse.eval nodeValue3534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3534) = mixedMoment B node3534 node3534Labels := rfl
  simpa [nodeValue3534, Sparse.eval] using hc.symm

theorem sound3538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3538 node3538Labels = Sparse.eval nodeValue3538 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3538) = mixedMoment B node3538 node3538Labels := rfl
  simpa [nodeValue3538, Sparse.eval] using hc.symm

theorem sound3541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3541 node3541Labels = Sparse.eval nodeValue3541 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3541) = mixedMoment B node3541 node3541Labels := rfl
  simpa [nodeValue3541, Sparse.eval] using hc.symm

theorem sound3560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3560 node3560Labels = Sparse.eval nodeValue3560 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3560) = mixedMoment B node3560 node3560Labels := rfl
  simpa [nodeValue3560, Sparse.eval] using hc.symm

theorem sound3572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3572 node3572Labels = Sparse.eval nodeValue3572 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3572) = mixedMoment B node3572 node3572Labels := rfl
  simpa [nodeValue3572, Sparse.eval] using hc.symm

theorem sound3575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3575 node3575Labels = Sparse.eval nodeValue3575 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3575) = mixedMoment B node3575 node3575Labels := rfl
  simpa [nodeValue3575, Sparse.eval] using hc.symm

theorem sound3577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3577 node3577Labels = Sparse.eval nodeValue3577 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3577) = mixedMoment B node3577 node3577Labels := rfl
  simpa [nodeValue3577, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node468 node468Labels = Sparse.eval nodeValue468 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue468 (familyPairVector B) := singlePair468 B _hB
    _ = _ := by norm_num [singlePairValue468, nodeValue468, Sparse.eval, mixedVector] <;> ring

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

theorem sound3813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3813 node3813Labels = Sparse.eval nodeValue3813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3813) = mixedMoment B node3813 node3813Labels := rfl
  simpa [nodeValue3813, Sparse.eval] using hc.symm

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

theorem sound3840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3840 node3840Labels = Sparse.eval nodeValue3840 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3840) = mixedMoment B node3840 node3840Labels := rfl
  simpa [nodeValue3840, Sparse.eval] using hc.symm

theorem sound3854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3854 node3854Labels = Sparse.eval nodeValue3854 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3854) = mixedMoment B node3854 node3854Labels := rfl
  simpa [nodeValue3854, Sparse.eval] using hc.symm

theorem sound3856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3856 node3856Labels = Sparse.eval nodeValue3856 (mixedVector B) := by
  have h := singleton3856 B _hB
  rw [sound468 B _hB _hF] at h
  norm_num [nodeValue3856, nodeValue468, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources7
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq254 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm254 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA254 + difference 0 1) (sourceB254 + difference 1 0) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA254 + difference 0 1) (sourceB254 + difference 1 0) sourceC254) = raw6186 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6186; decide +kernel
    rw [ha]
    exact (canonical6186 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA254 + difference 0 2) (sourceB254 + difference 2 0) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA254 + difference 0 2) (sourceB254 + difference 2 0) sourceC254) = raw6187 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6187; decide +kernel
    rw [ha]
    exact (canonical6187 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA254 + difference 0 3) (sourceB254 + difference 3 0) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA254 + difference 0 3) (sourceB254 + difference 3 0) sourceC254) = raw6188 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6188; decide +kernel
    rw [ha]
    exact (canonical6188 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA254 + difference 0 4) (sourceB254 + difference 4 0) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3856) := by
    have ha : (tripleCharges (sourceA254 + difference 0 4) (sourceB254 + difference 4 0) sourceC254) = raw6189 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6189; decide +kernel
    rw [ha]
    exact (canonical6189 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA254 + difference 0 5) (sourceB254 + difference 5 0) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA254 + difference 0 5) (sourceB254 + difference 5 0) sourceC254) = raw6190 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6190; decide +kernel
    rw [ha]
    exact (canonical6190 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA254 + difference 1 0) (sourceB254 + difference 0 1) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3287) := by
    have ha : (tripleCharges (sourceA254 + difference 1 0) (sourceB254 + difference 0 1) sourceC254) = raw6191 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6191; decide +kernel
    rw [ha]
    exact (canonical6191 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA254 + difference 1 2) (sourceB254 + difference 2 1) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3560) := by
    have ha : (tripleCharges (sourceA254 + difference 1 2) (sourceB254 + difference 2 1) sourceC254) = raw6192 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6192; decide +kernel
    rw [ha]
    exact (canonical6192 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA254 + difference 1 3) (sourceB254 + difference 3 1) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3575) := by
    have ha : (tripleCharges (sourceA254 + difference 1 3) (sourceB254 + difference 3 1) sourceC254) = raw6193 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6193; decide +kernel
    rw [ha]
    exact (canonical6193 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA254 + difference 1 4) (sourceB254 + difference 4 1) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3577) := by
    have ha : (tripleCharges (sourceA254 + difference 1 4) (sourceB254 + difference 4 1) sourceC254) = raw6194 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6194; decide +kernel
    rw [ha]
    exact (canonical6194 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA254 + difference 1 5) (sourceB254 + difference 5 1) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA254 + difference 1 5) (sourceB254 + difference 5 1) sourceC254) = raw6195 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6195; decide +kernel
    rw [ha]
    exact (canonical6195 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA254 + difference 2 0) (sourceB254 + difference 0 2) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3285) := by
    have ha : (tripleCharges (sourceA254 + difference 2 0) (sourceB254 + difference 0 2) sourceC254) = raw6196 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6196; decide +kernel
    rw [ha]
    exact (canonical6196 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA254 + difference 2 1) (sourceB254 + difference 1 2) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA254 + difference 2 1) (sourceB254 + difference 1 2) sourceC254) = raw6197 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6197; decide +kernel
    rw [ha]
    exact (canonical6197 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA254 + difference 2 3) (sourceB254 + difference 3 2) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3527) := by
    have ha : (tripleCharges (sourceA254 + difference 2 3) (sourceB254 + difference 3 2) sourceC254) = raw6198 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6198; decide +kernel
    rw [ha]
    exact (canonical6198 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA254 + difference 2 4) (sourceB254 + difference 4 2) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3528) := by
    have ha : (tripleCharges (sourceA254 + difference 2 4) (sourceB254 + difference 4 2) sourceC254) = raw6199 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6199; decide +kernel
    rw [ha]
    exact (canonical6199 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA254 + difference 2 5) (sourceB254 + difference 5 2) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA254 + difference 2 5) (sourceB254 + difference 5 2) sourceC254) = raw6200 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6200; decide +kernel
    rw [ha]
    exact (canonical6200 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA254 + difference 3 0) (sourceB254 + difference 0 3) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA254 + difference 3 0) (sourceB254 + difference 0 3) sourceC254) = raw6201 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6201; decide +kernel
    rw [ha]
    exact (canonical6201 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA254 + difference 3 1) (sourceB254 + difference 1 3) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3479) := by
    have ha : (tripleCharges (sourceA254 + difference 3 1) (sourceB254 + difference 1 3) sourceC254) = raw6202 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6202; decide +kernel
    rw [ha]
    exact (canonical6202 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA254 + difference 3 2) (sourceB254 + difference 2 3) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3517) := by
    have ha : (tripleCharges (sourceA254 + difference 3 2) (sourceB254 + difference 2 3) sourceC254) = raw6203 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6203; decide +kernel
    rw [ha]
    exact (canonical6203 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA254 + difference 3 4) (sourceB254 + difference 4 3) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA254 + difference 3 4) (sourceB254 + difference 4 3) sourceC254) = raw6204 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6204; decide +kernel
    rw [ha]
    exact (canonical6204 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA254 + difference 3 5) (sourceB254 + difference 5 3) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA254 + difference 3 5) (sourceB254 + difference 5 3) sourceC254) = raw6205 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6205; decide +kernel
    rw [ha]
    exact (canonical6205 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA254 + difference 4 0) (sourceB254 + difference 0 4) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3295) := by
    have ha : (tripleCharges (sourceA254 + difference 4 0) (sourceB254 + difference 0 4) sourceC254) = raw6206 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6206; decide +kernel
    rw [ha]
    exact (canonical6206 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA254 + difference 4 1) (sourceB254 + difference 1 4) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA254 + difference 4 1) (sourceB254 + difference 1 4) sourceC254) = raw6207 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6207; decide +kernel
    rw [ha]
    exact (canonical6207 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA254 + difference 4 2) (sourceB254 + difference 2 4) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA254 + difference 4 2) (sourceB254 + difference 2 4) sourceC254) = raw6208 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6208; decide +kernel
    rw [ha]
    exact (canonical6208 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA254 + difference 4 3) (sourceB254 + difference 3 4) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA254 + difference 4 3) (sourceB254 + difference 3 4) sourceC254) = raw6209 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6209; decide +kernel
    rw [ha]
    exact (canonical6209 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA254 + difference 4 5) (sourceB254 + difference 5 4) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA254 + difference 4 5) (sourceB254 + difference 5 4) sourceC254) = raw6210 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6210; decide +kernel
    rw [ha]
    exact (canonical6210 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA254 + difference 5 0) (sourceB254 + difference 0 5) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2045) := by
    have ha : (tripleCharges (sourceA254 + difference 5 0) (sourceB254 + difference 0 5) sourceC254) = raw6211 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6211; decide +kernel
    rw [ha]
    exact (canonical6211 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA254 + difference 5 1) (sourceB254 + difference 1 5) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA254 + difference 5 1) (sourceB254 + difference 1 5) sourceC254) = raw6212 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6212; decide +kernel
    rw [ha]
    exact (canonical6212 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA254 + difference 5 2) (sourceB254 + difference 2 5) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2043) := by
    have ha : (tripleCharges (sourceA254 + difference 5 2) (sourceB254 + difference 2 5) sourceC254) = raw6213 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6213; decide +kernel
    rw [ha]
    exact (canonical6213 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA254 + difference 5 3) (sourceB254 + difference 3 5) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2049) := by
    have ha : (tripleCharges (sourceA254 + difference 5 3) (sourceB254 + difference 3 5) sourceC254) = raw6214 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6214; decide +kernel
    rw [ha]
    exact (canonical6214 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA254 + difference 5 4) (sourceB254 + difference 4 5) sourceC254) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2055) := by
    have ha : (tripleCharges (sourceA254 + difference 5 4) (sourceB254 + difference 4 5) sourceC254) = raw6215 := by
      apply Matrix.ext; unfold tripleCharges sourceA254 sourceB254 sourceC254 difference raw6215; decide +kernel
    rw [ha]
    exact (canonical6215 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA254 sourceB254 sourceC254
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm254, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck214 : Integer.Sparse.reindex keyMap MixedData.row214 = numericRow214 := by decide +kernel

theorem numericCheck214 (x : Master → ℝ) : Integer.Sparse.eval numericRow214 x =
    (4320 : ℝ) * reducedSource214 x := by
  norm_num [numericRow214, reducedSource214, Integer.Sparse.eval, Sparse.eval, nodeValue2043, nodeValue2045, nodeValue2049, nodeValue2055, nodeValue2259, nodeValue3285, nodeValue3287, nodeValue3295, nodeValue3296, nodeValue3463, nodeValue3478, nodeValue3479, nodeValue3516, nodeValue3517, nodeValue3525, nodeValue3527, nodeValue3528, nodeValue3533, nodeValue3534, nodeValue3538, nodeValue3541, nodeValue3560, nodeValue3572, nodeValue3575, nodeValue3577, nodeValue3813, nodeValue3840, nodeValue3852, nodeValue3854, nodeValue3856]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero214 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource214 (mixedVector B) = 0 := by
  have h2043 : mixedVector B (Sum.inr 2043) = Sparse.eval nodeValue2043 (mixedVector B) := by
    change mixedMoment B node2043 node2043Labels = _
    exact sound2043 B hB hF
  have h2045 : mixedVector B (Sum.inr 2045) = Sparse.eval nodeValue2045 (mixedVector B) := by
    change mixedMoment B node2045 node2045Labels = _
    exact sound2045 B hB hF
  have h2049 : mixedVector B (Sum.inr 2049) = Sparse.eval nodeValue2049 (mixedVector B) := by
    change mixedMoment B node2049 node2049Labels = _
    exact sound2049 B hB hF
  have h2055 : mixedVector B (Sum.inr 2055) = Sparse.eval nodeValue2055 (mixedVector B) := by
    change mixedMoment B node2055 node2055Labels = _
    exact sound2055 B hB hF
  have h2259 : mixedVector B (Sum.inr 2259) = Sparse.eval nodeValue2259 (mixedVector B) := by
    change mixedMoment B node2259 node2259Labels = _
    exact sound2259 B hB hF
  have h3285 : mixedVector B (Sum.inr 3285) = Sparse.eval nodeValue3285 (mixedVector B) := by
    change mixedMoment B node3285 node3285Labels = _
    exact sound3285 B hB hF
  have h3287 : mixedVector B (Sum.inr 3287) = Sparse.eval nodeValue3287 (mixedVector B) := by
    change mixedMoment B node3287 node3287Labels = _
    exact sound3287 B hB hF
  have h3295 : mixedVector B (Sum.inr 3295) = Sparse.eval nodeValue3295 (mixedVector B) := by
    change mixedMoment B node3295 node3295Labels = _
    exact sound3295 B hB hF
  have h3296 : mixedVector B (Sum.inr 3296) = Sparse.eval nodeValue3296 (mixedVector B) := by
    change mixedMoment B node3296 node3296Labels = _
    exact sound3296 B hB hF
  have h3463 : mixedVector B (Sum.inr 3463) = Sparse.eval nodeValue3463 (mixedVector B) := by
    change mixedMoment B node3463 node3463Labels = _
    exact sound3463 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h3479 : mixedVector B (Sum.inr 3479) = Sparse.eval nodeValue3479 (mixedVector B) := by
    change mixedMoment B node3479 node3479Labels = _
    exact sound3479 B hB hF
  have h3516 : mixedVector B (Sum.inr 3516) = Sparse.eval nodeValue3516 (mixedVector B) := by
    change mixedMoment B node3516 node3516Labels = _
    exact sound3516 B hB hF
  have h3517 : mixedVector B (Sum.inr 3517) = Sparse.eval nodeValue3517 (mixedVector B) := by
    change mixedMoment B node3517 node3517Labels = _
    exact sound3517 B hB hF
  have h3525 : mixedVector B (Sum.inr 3525) = Sparse.eval nodeValue3525 (mixedVector B) := by
    change mixedMoment B node3525 node3525Labels = _
    exact sound3525 B hB hF
  have h3527 : mixedVector B (Sum.inr 3527) = Sparse.eval nodeValue3527 (mixedVector B) := by
    change mixedMoment B node3527 node3527Labels = _
    exact sound3527 B hB hF
  have h3528 : mixedVector B (Sum.inr 3528) = Sparse.eval nodeValue3528 (mixedVector B) := by
    change mixedMoment B node3528 node3528Labels = _
    exact sound3528 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h3538 : mixedVector B (Sum.inr 3538) = Sparse.eval nodeValue3538 (mixedVector B) := by
    change mixedMoment B node3538 node3538Labels = _
    exact sound3538 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h3560 : mixedVector B (Sum.inr 3560) = Sparse.eval nodeValue3560 (mixedVector B) := by
    change mixedMoment B node3560 node3560Labels = _
    exact sound3560 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3575 : mixedVector B (Sum.inr 3575) = Sparse.eval nodeValue3575 (mixedVector B) := by
    change mixedMoment B node3575 node3575Labels = _
    exact sound3575 B hB hF
  have h3577 : mixedVector B (Sum.inr 3577) = Sparse.eval nodeValue3577 (mixedVector B) := by
    change mixedMoment B node3577 node3577Labels = _
    exact sound3577 B hB hF
  have h3813 : mixedVector B (Sum.inr 3813) = Sparse.eval nodeValue3813 (mixedVector B) := by
    change mixedMoment B node3813 node3813Labels = _
    exact sound3813 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h3852 : mixedVector B (Sum.inr 3852) = Sparse.eval nodeValue3852 (mixedVector B) := by
    change mixedMoment B node3852 node3852Labels = _
    exact sound3852_e B hB hF
  have h3854 : mixedVector B (Sum.inr 3854) = Sparse.eval nodeValue3854 (mixedVector B) := by
    change mixedMoment B node3854 node3854Labels = _
    exact sound3854 B hB hF
  have h3856 : mixedVector B (Sum.inr 3856) = Sparse.eval nodeValue3856 (mixedVector B) := by
    change mixedMoment B node3856 node3856Labels = _
    exact sound3856 B hB hF
  simpa only [sourceForm254, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2043, h2045, h2049, h2055, h2259, h3285, h3287, h3295, h3296, h3463, h3478, h3479, h3516, h3517, h3525, h3527, h3528, h3533, h3534, h3538, h3541, h3560, h3572, h3575, h3577, h3813, h3840, h3852, h3854, h3856, reducedSource214] using sourceEq254 B hB

theorem rowSound214_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row214 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck214, numericCheck214, reducedZero214 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound214_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound214_e_oai
