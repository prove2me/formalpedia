-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:12:17.001263+00:00
-- url     : https://prove2.me/submissions/92a63610-4c4d-4899-b5e2-0a5d2de3dfe4

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E105
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5172_e

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

theorem canonical1302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1302 raw1302Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw1302 raw1302Labels = mixedMoment B raw1302step0 raw1302step0Labels := by
      have ha : raw1302step0 = (fun i j => raw1302 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1302step0 raw1302; decide +kernel
      have hl : raw1302step0Labels = raw1302Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1302 raw1302Labels permutation8 permutation4
    mixedMoment B raw1302step0 raw1302step0Labels = mixedMoment B raw1302step1 raw1302step1Labels := by
      have ha : raw1302step1 = raw1302step0 := by apply Matrix.ext; unfold raw1302step1 raw1302step0; decide +kernel
      have hl : raw1302step0Labels = labelEmbedding7 ∘ raw1302step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1302step0 raw1302step0Labels raw1302step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

theorem canonical1303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1303 raw1303Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw1303 raw1303Labels = mixedMoment B raw1303step0 raw1303step0Labels := by
      have ha : raw1303step0 = (fun i j => raw1303 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1303step0 raw1303; decide +kernel
      have hl : raw1303step0Labels = raw1303Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1303 raw1303Labels permutation8 permutation4
    _ = mixedMoment B node1087 node1087Labels := by rfl

theorem canonical1304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1304 raw1304Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw1304 raw1304Labels = mixedMoment B raw1304step0 raw1304step0Labels := by
      have ha : raw1304step0 = (fun i j => raw1304 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1304step0 raw1304; decide +kernel
      have hl : raw1304step0Labels = raw1304Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1304 raw1304Labels permutation12 permutation6
    mixedMoment B raw1304step0 raw1304step0Labels = mixedMoment B raw1304step1 raw1304step1Labels := by
      have ha : raw1304step1 = -raw1304step0 := by apply Matrix.ext; change ∀ i j, raw1304step1 i j = -(raw1304step0 i j); unfold raw1304step1 raw1304step0; decide +kernel
      have hl : raw1304step1Labels = raw1304step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1304step1 raw1304step1Labels = mixedMoment B raw1304step2 raw1304step2Labels := by
      have ha : raw1304step2 = raw1304step1 := by apply Matrix.ext; unfold raw1304step2 raw1304step1; decide +kernel
      have hl : raw1304step1Labels = labelEmbedding1 ∘ raw1304step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1304step1 raw1304step1Labels raw1304step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1739 node1739Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13574 raw13574Labels = mixedMoment B node4489 node4489Labels := by
  calc
    mixedMoment B raw13574 raw13574Labels = mixedMoment B raw13574step0 raw13574step0Labels := by
      have hz : ∀ j, raw13574 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13574step0 = (fun i j => raw13574 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13574step0 raw13574; decide +kernel
      have hl : raw13574step0Labels = raw13574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13574 raw13574Labels permutation346 hz
    mixedMoment B raw13574step0 raw13574step0Labels = mixedMoment B raw13574step1 raw13574step1Labels := by
      have ha : raw13574step1 = (fun i j => raw13574step0 (permutation53 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13574step1 raw13574step0; decide +kernel
      have hl : raw13574step1Labels = raw13574step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13574step0 raw13574step0Labels permutation53 permutation3
    mixedMoment B raw13574step1 raw13574step1Labels = mixedMoment B raw13574step2 raw13574step2Labels := by
      have ha : raw13574step2 = raw13574step1 := by apply Matrix.ext; unfold raw13574step2 raw13574step1; decide +kernel
      have hl : raw13574step1Labels = labelEmbedding6 ∘ raw13574step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13574step1 raw13574step1Labels raw13574step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4489 node4489Labels := by rfl

theorem canonical13578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13578 raw13578Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw13578 raw13578Labels = mixedMoment B raw13578step0 raw13578step0Labels := by
      have ha : raw13578step0 = (fun i j => raw13578 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13578step0 raw13578; decide +kernel
      have hl : raw13578step0Labels = raw13578Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13578 raw13578Labels permutation170 permutation3
    mixedMoment B raw13578step0 raw13578step0Labels = mixedMoment B raw13578step1 raw13578step1Labels := by
      have ha : raw13578step1 = raw13578step0 := by apply Matrix.ext; unfold raw13578step1 raw13578step0; decide +kernel
      have hl : raw13578step0Labels = labelEmbedding6 ∘ raw13578step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13578step0 raw13578step0Labels raw13578step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4451 node4451Labels := by rfl

theorem canonical13582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13582 raw13582Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw13582 raw13582Labels = mixedMoment B raw13582step0 raw13582step0Labels := by
      have hz : ∀ j, raw13582 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13582step0 = (fun i j => raw13582 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13582step0 raw13582; decide +kernel
      have hl : raw13582step0Labels = raw13582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13582 raw13582Labels permutation346 hz
    mixedMoment B raw13582step0 raw13582step0Labels = mixedMoment B raw13582step1 raw13582step1Labels := by
      have ha : raw13582step1 = (fun i j => raw13582step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13582step1 raw13582step0; decide +kernel
      have hl : raw13582step1Labels = raw13582step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13582step0 raw13582step0Labels permutation37 permutation3
    mixedMoment B raw13582step1 raw13582step1Labels = mixedMoment B raw13582step2 raw13582step2Labels := by
      have ha : raw13582step2 = raw13582step1 := by apply Matrix.ext; unfold raw13582step2 raw13582step1; decide +kernel
      have hl : raw13582step1Labels = labelEmbedding6 ∘ raw13582step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13582step1 raw13582step1Labels raw13582step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

theorem canonical13587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13587 raw13587Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw13587 raw13587Labels = mixedMoment B raw13587step0 raw13587step0Labels := by
      have hz : ∀ j, raw13587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13587step0 = (fun i j => raw13587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13587step0 raw13587; decide +kernel
      have hl : raw13587step0Labels = raw13587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13587 raw13587Labels permutation346 hz
    mixedMoment B raw13587step0 raw13587step0Labels = mixedMoment B raw13587step1 raw13587step1Labels := by
      have ha : raw13587step1 = (fun i j => raw13587step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13587step1 raw13587step0; decide +kernel
      have hl : raw13587step1Labels = raw13587step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13587step0 raw13587step0Labels permutation36 permutation3
    mixedMoment B raw13587step1 raw13587step1Labels = mixedMoment B raw13587step2 raw13587step2Labels := by
      have ha : raw13587step2 = raw13587step1 := by apply Matrix.ext; unfold raw13587step2 raw13587step1; decide +kernel
      have hl : raw13587step1Labels = labelEmbedding6 ∘ raw13587step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13587step1 raw13587step1Labels raw13587step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

theorem canonical13592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13592 raw13592Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw13592 raw13592Labels = mixedMoment B raw13592step0 raw13592step0Labels := by
      have hz : ∀ j, raw13592 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13592step0 = (fun i j => raw13592 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13592step0 raw13592; decide +kernel
      have hl : raw13592step0Labels = raw13592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13592 raw13592Labels permutation346 hz
    mixedMoment B raw13592step0 raw13592step0Labels = mixedMoment B raw13592step1 raw13592step1Labels := by
      have ha : raw13592step1 = (fun i j => raw13592step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13592step1 raw13592step0; decide +kernel
      have hl : raw13592step1Labels = raw13592step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13592step0 raw13592step0Labels permutation32 permutation3
    mixedMoment B raw13592step1 raw13592step1Labels = mixedMoment B raw13592step2 raw13592step2Labels := by
      have ha : raw13592step2 = raw13592step1 := by apply Matrix.ext; unfold raw13592step2 raw13592step1; decide +kernel
      have hl : raw13592step1Labels = labelEmbedding6 ∘ raw13592step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13592step1 raw13592step1Labels raw13592step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5172 node5172Labels := by rfl

theorem canonical13593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13593 raw13593Labels = mixedMoment B node5076 node5076Labels := by
  calc
    mixedMoment B raw13593 raw13593Labels = mixedMoment B raw13593step0 raw13593step0Labels := by
      have ha : raw13593step0 = (fun i j => raw13593 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13593step0 raw13593; decide +kernel
      have hl : raw13593step0Labels = raw13593Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13593 raw13593Labels permutation176 permutation3
    mixedMoment B raw13593step0 raw13593step0Labels = mixedMoment B raw13593step1 raw13593step1Labels := by
      have ha : raw13593step1 = raw13593step0 := by apply Matrix.ext; unfold raw13593step1 raw13593step0; decide +kernel
      have hl : raw13593step0Labels = labelEmbedding6 ∘ raw13593step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13593step0 raw13593step0Labels raw13593step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5076 node5076Labels := by rfl

theorem canonical13594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13594 raw13594Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw13594 raw13594Labels = mixedMoment B raw13594step0 raw13594step0Labels := by
      have hz : ∀ j, raw13594 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13594step0 = (fun i j => raw13594 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13594step0 raw13594; decide +kernel
      have hl : raw13594step0Labels = raw13594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13594 raw13594Labels permutation520 hz
    mixedMoment B raw13594step0 raw13594step0Labels = mixedMoment B raw13594step1 raw13594step1Labels := by
      have hz : ∀ j, raw13594step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw13594step1 = (fun i j => raw13594step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw13594step1 raw13594step0; decide +kernel
      have hl : raw13594step1Labels = raw13594step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13594step0 raw13594step0Labels permutation80 hz
    mixedMoment B raw13594step1 raw13594step1Labels = mixedMoment B raw13594step2 raw13594step2Labels := by
      have ha : raw13594step2 = (fun i j => raw13594step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13594step2 raw13594step1; decide +kernel
      have hl : raw13594step2Labels = raw13594step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13594step1 raw13594step1Labels permutation8 permutation3
    mixedMoment B raw13594step2 raw13594step2Labels = mixedMoment B raw13594step3 raw13594step3Labels := by
      have ha : raw13594step3 = raw13594step2 := by apply Matrix.ext; unfold raw13594step3 raw13594step2; decide +kernel
      have hl : raw13594step2Labels = labelEmbedding6 ∘ raw13594step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13594step2 raw13594step2Labels raw13594step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

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

theorem canonical2100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2100 raw2100Labels = mixedMoment B node5076 node5076Labels := by
  calc
    mixedMoment B raw2100 raw2100Labels = mixedMoment B raw2100step0 raw2100step0Labels := by
      have ha : raw2100step0 = (fun i j => raw2100 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2100step0 raw2100; decide +kernel
      have hl : raw2100step0Labels = raw2100Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2100 raw2100Labels permutation152 permutation4
    mixedMoment B raw2100step0 raw2100step0Labels = mixedMoment B raw2100step1 raw2100step1Labels := by
      have ha : raw2100step1 = raw2100step0 := by apply Matrix.ext; unfold raw2100step1 raw2100step0; decide +kernel
      have hl : raw2100step0Labels = labelEmbedding7 ∘ raw2100step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2100step0 raw2100step0Labels raw2100step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5076 node5076Labels := by rfl

theorem canonical2101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2101 raw2101Labels = mixedMoment B node2483 node2483Labels := by
  calc
    mixedMoment B raw2101 raw2101Labels = mixedMoment B raw2101step0 raw2101step0Labels := by
      have ha : raw2101step0 = (fun i j => raw2101 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2101step0 raw2101; decide +kernel
      have hl : raw2101step0Labels = raw2101Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2101 raw2101Labels permutation152 permutation4
    _ = mixedMoment B node2483 node2483Labels := by rfl

theorem canonical2102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2102 raw2102Labels = mixedMoment B node3477 node3477Labels := by
  calc
    mixedMoment B raw2102 raw2102Labels = mixedMoment B raw2102step0 raw2102step0Labels := by
      have ha : raw2102step0 = (fun i j => raw2102 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2102step0 raw2102; decide +kernel
      have hl : raw2102step0Labels = raw2102Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2102 raw2102Labels permutation170 permutation6
    mixedMoment B raw2102step0 raw2102step0Labels = mixedMoment B raw2102step1 raw2102step1Labels := by
      have ha : raw2102step1 = -raw2102step0 := by apply Matrix.ext; change ∀ i j, raw2102step1 i j = -(raw2102step0 i j); unfold raw2102step1 raw2102step0; decide +kernel
      have hl : raw2102step1Labels = raw2102step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2102step1 raw2102step1Labels = mixedMoment B raw2102step2 raw2102step2Labels := by
      have ha : raw2102step2 = raw2102step1 := by apply Matrix.ext; unfold raw2102step2 raw2102step1; decide +kernel
      have hl : raw2102step1Labels = labelEmbedding1 ∘ raw2102step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2102step1 raw2102step1Labels raw2102step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3477 node3477Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical165
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21243 raw21243Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw21243 raw21243Labels = mixedMoment B raw21243step0 raw21243step0Labels := by
      have hz : ∀ j, raw21243 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21243step0 = (fun i j => raw21243 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21243step0 raw21243; decide +kernel
      have hl : raw21243step0Labels = raw21243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21243 raw21243Labels permutation434 hz
    mixedMoment B raw21243step0 raw21243step0Labels = mixedMoment B raw21243step1 raw21243step1Labels := by
      have hz : ∀ j, raw21243step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21243step1 = (fun i j => raw21243step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21243step1 raw21243step0; decide +kernel
      have hl : raw21243step1Labels = raw21243step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21243step0 raw21243step0Labels permutation80 hz
    mixedMoment B raw21243step1 raw21243step1Labels = mixedMoment B raw21243step2 raw21243step2Labels := by
      have ha : raw21243step2 = (fun i j => raw21243step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21243step2 raw21243step1; decide +kernel
      have hl : raw21243step2Labels = raw21243step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21243step1 raw21243step1Labels permutation10 permutation3
    mixedMoment B raw21243step2 raw21243step2Labels = mixedMoment B raw21243step3 raw21243step3Labels := by
      have ha : raw21243step3 = raw21243step2 := by apply Matrix.ext; unfold raw21243step3 raw21243step2; decide +kernel
      have hl : raw21243step2Labels = labelEmbedding6 ∘ raw21243step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21243step2 raw21243step2Labels raw21243step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

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

theorem canonical21248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21248 raw21248Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw21248 raw21248Labels = mixedMoment B raw21248step0 raw21248step0Labels := by
      have hz : ∀ j, raw21248 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21248step0 = (fun i j => raw21248 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21248step0 raw21248; decide +kernel
      have hl : raw21248step0Labels = raw21248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21248 raw21248Labels permutation434 hz
    mixedMoment B raw21248step0 raw21248step0Labels = mixedMoment B raw21248step1 raw21248step1Labels := by
      have ha : raw21248step1 = (fun i j => raw21248step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21248step1 raw21248step0; decide +kernel
      have hl : raw21248step1Labels = raw21248step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21248step0 raw21248step0Labels permutation32 permutation3
    mixedMoment B raw21248step1 raw21248step1Labels = mixedMoment B raw21248step2 raw21248step2Labels := by
      have ha : raw21248step2 = raw21248step1 := by apply Matrix.ext; unfold raw21248step2 raw21248step1; decide +kernel
      have hl : raw21248step1Labels = labelEmbedding6 ∘ raw21248step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21248step1 raw21248step1Labels raw21248step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4461 node4461Labels := by rfl

theorem canonical21249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21249 raw21249Labels = mixedMoment B node4105 node4105Labels := by
  calc
    mixedMoment B raw21249 raw21249Labels = mixedMoment B raw21249step0 raw21249step0Labels := by
      have hz : ∀ j, raw21249 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21249step0 = (fun i j => raw21249 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21249step0 raw21249; decide +kernel
      have hl : raw21249step0Labels = raw21249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21249 raw21249Labels permutation346 hz
    mixedMoment B raw21249step0 raw21249step0Labels = mixedMoment B raw21249step1 raw21249step1Labels := by
      have ha : raw21249step1 = (fun i j => raw21249step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21249step1 raw21249step0; decide +kernel
      have hl : raw21249step1Labels = raw21249step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21249step0 raw21249step0Labels permutation32 permutation3
    mixedMoment B raw21249step1 raw21249step1Labels = mixedMoment B raw21249step2 raw21249step2Labels := by
      have ha : raw21249step2 = raw21249step1 := by apply Matrix.ext; unfold raw21249step2 raw21249step1; decide +kernel
      have hl : raw21249step1Labels = labelEmbedding6 ∘ raw21249step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21249step1 raw21249step1Labels raw21249step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4105 node4105Labels := by rfl

theorem canonical21250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21250 raw21250Labels = mixedMoment B node4352 node4352Labels := by
  calc
    mixedMoment B raw21250 raw21250Labels = mixedMoment B raw21250step0 raw21250step0Labels := by
      have hz : ∀ j, raw21250 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21250step0 = (fun i j => raw21250 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21250step0 raw21250; decide +kernel
      have hl : raw21250step0Labels = raw21250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21250 raw21250Labels permutation346 hz
    mixedMoment B raw21250step0 raw21250step0Labels = mixedMoment B raw21250step1 raw21250step1Labels := by
      have ha : raw21250step1 = (fun i j => raw21250step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21250step1 raw21250step0; decide +kernel
      have hl : raw21250step1Labels = raw21250step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21250step0 raw21250step0Labels permutation32 permutation3
    mixedMoment B raw21250step1 raw21250step1Labels = mixedMoment B raw21250step2 raw21250step2Labels := by
      have ha : raw21250step2 = raw21250step1 := by apply Matrix.ext; unfold raw21250step2 raw21250step1; decide +kernel
      have hl : raw21250step1Labels = labelEmbedding6 ∘ raw21250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21250step1 raw21250step1Labels raw21250step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4352 node4352Labels := by rfl

theorem canonical21251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21251 raw21251Labels = mixedMoment B node4290 node4290Labels := by
  calc
    mixedMoment B raw21251 raw21251Labels = mixedMoment B raw21251step0 raw21251step0Labels := by
      have ha : raw21251step0 = (fun i j => raw21251 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21251step0 raw21251; decide +kernel
      have hl : raw21251step0Labels = raw21251Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21251 raw21251Labels permutation176 permutation3
    mixedMoment B raw21251step0 raw21251step0Labels = mixedMoment B raw21251step1 raw21251step1Labels := by
      have ha : raw21251step1 = raw21251step0 := by apply Matrix.ext; unfold raw21251step1 raw21251step0; decide +kernel
      have hl : raw21251step0Labels = labelEmbedding6 ∘ raw21251step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21251step0 raw21251step0Labels raw21251step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4290 node4290Labels := by rfl

theorem canonical21252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21252 raw21252Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw21252 raw21252Labels = mixedMoment B raw21252step0 raw21252step0Labels := by
      have hz : ∀ j, raw21252 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21252step0 = (fun i j => raw21252 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21252step0 raw21252; decide +kernel
      have hl : raw21252step0Labels = raw21252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21252 raw21252Labels permutation520 hz
    mixedMoment B raw21252step0 raw21252step0Labels = mixedMoment B raw21252step1 raw21252step1Labels := by
      have hz : ∀ j, raw21252step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21252step1 = (fun i j => raw21252step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21252step1 raw21252step0; decide +kernel
      have hl : raw21252step1Labels = raw21252step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21252step0 raw21252step0Labels permutation80 hz
    mixedMoment B raw21252step1 raw21252step1Labels = mixedMoment B raw21252step2 raw21252step2Labels := by
      have ha : raw21252step2 = (fun i j => raw21252step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21252step2 raw21252step1; decide +kernel
      have hl : raw21252step2Labels = raw21252step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21252step1 raw21252step1Labels permutation8 permutation3
    mixedMoment B raw21252step2 raw21252step2Labels = mixedMoment B raw21252step3 raw21252step3Labels := by
      have ha : raw21252step3 = raw21252step2 := by apply Matrix.ext; unfold raw21252step3 raw21252step2; decide +kernel
      have hl : raw21252step2Labels = labelEmbedding6 ∘ raw21252step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21252step2 raw21252step2Labels raw21252step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

theorem canonical21257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21257 raw21257Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw21257 raw21257Labels = mixedMoment B raw21257step0 raw21257step0Labels := by
      have hz : ∀ j, raw21257 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21257step0 = (fun i j => raw21257 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21257step0 raw21257; decide +kernel
      have hl : raw21257step0Labels = raw21257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21257 raw21257Labels permutation434 hz
    mixedMoment B raw21257step0 raw21257step0Labels = mixedMoment B raw21257step1 raw21257step1Labels := by
      have hz : ∀ j, raw21257step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21257step1 = (fun i j => raw21257step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21257step1 raw21257step0; decide +kernel
      have hl : raw21257step1Labels = raw21257step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21257step0 raw21257step0Labels permutation80 hz
    mixedMoment B raw21257step1 raw21257step1Labels = mixedMoment B raw21257step2 raw21257step2Labels := by
      have ha : raw21257step2 = (fun i j => raw21257step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21257step2 raw21257step1; decide +kernel
      have hl : raw21257step2Labels = raw21257step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21257step1 raw21257step1Labels permutation9 permutation3
    mixedMoment B raw21257step2 raw21257step2Labels = mixedMoment B raw21257step3 raw21257step3Labels := by
      have ha : raw21257step3 = raw21257step2 := by apply Matrix.ext; unfold raw21257step3 raw21257step2; decide +kernel
      have hl : raw21257step2Labels = labelEmbedding6 ∘ raw21257step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21257step2 raw21257step2Labels raw21257step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

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

theorem canonical2292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2292 raw2292Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw2292 raw2292Labels = mixedMoment B raw2292step0 raw2292step0Labels := by
      have ha : raw2292step0 = (fun i j => raw2292 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2292step0 raw2292; decide +kernel
      have hl : raw2292step0Labels = raw2292Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2292 raw2292Labels permutation32 permutation4
    mixedMoment B raw2292step0 raw2292step0Labels = mixedMoment B raw2292step1 raw2292step1Labels := by
      have ha : raw2292step1 = raw2292step0 := by apply Matrix.ext; unfold raw2292step1 raw2292step0; decide +kernel
      have hl : raw2292step0Labels = labelEmbedding7 ∘ raw2292step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2292step0 raw2292step0Labels raw2292step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical2293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2293 raw2293Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw2293 raw2293Labels = mixedMoment B raw2293step0 raw2293step0Labels := by
      have ha : raw2293step0 = (fun i j => raw2293 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2293step0 raw2293; decide +kernel
      have hl : raw2293step0Labels = raw2293Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2293 raw2293Labels permutation32 permutation4
    _ = mixedMoment B node2764 node2764Labels := by rfl

theorem canonical2294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2294 raw2294Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw2294 raw2294Labels = mixedMoment B raw2294step0 raw2294step0Labels := by
      have ha : raw2294step0 = (fun i j => raw2294 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2294step0 raw2294; decide +kernel
      have hl : raw2294step0Labels = raw2294Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2294 raw2294Labels permutation38 permutation6
    mixedMoment B raw2294step0 raw2294step0Labels = mixedMoment B raw2294step1 raw2294step1Labels := by
      have ha : raw2294step1 = -raw2294step0 := by apply Matrix.ext; change ∀ i j, raw2294step1 i j = -(raw2294step0 i j); unfold raw2294step1 raw2294step0; decide +kernel
      have hl : raw2294step1Labels = raw2294step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2294step1 raw2294step1Labels = mixedMoment B raw2294step2 raw2294step2Labels := by
      have ha : raw2294step2 = raw2294step1 := by apply Matrix.ext; unfold raw2294step2 raw2294step1; decide +kernel
      have hl : raw2294step1Labels = labelEmbedding1 ∘ raw2294step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2294step1 raw2294step1Labels raw2294step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

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

theorem canonical2304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2304 raw2304Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw2304 raw2304Labels = mixedMoment B raw2304step0 raw2304step0Labels := by
      have ha : raw2304step0 = (fun i j => raw2304 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2304step0 raw2304; decide +kernel
      have hl : raw2304step0Labels = raw2304Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2304 raw2304Labels permutation8 permutation4
    mixedMoment B raw2304step0 raw2304step0Labels = mixedMoment B raw2304step1 raw2304step1Labels := by
      have ha : raw2304step1 = raw2304step0 := by apply Matrix.ext; unfold raw2304step1 raw2304step0; decide +kernel
      have hl : raw2304step0Labels = labelEmbedding7 ∘ raw2304step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2304step0 raw2304step0Labels raw2304step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

theorem canonical2305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2305 raw2305Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw2305 raw2305Labels = mixedMoment B raw2305step0 raw2305step0Labels := by
      have ha : raw2305step0 = (fun i j => raw2305 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2305step0 raw2305; decide +kernel
      have hl : raw2305step0Labels = raw2305Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2305 raw2305Labels permutation8 permutation4
    _ = mixedMoment B node2768 node2768Labels := by rfl

theorem canonical2306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2306 raw2306Labels = mixedMoment B node3632 node3632Labels := by
  calc
    mixedMoment B raw2306 raw2306Labels = mixedMoment B raw2306step0 raw2306step0Labels := by
      have ha : raw2306step0 = (fun i j => raw2306 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2306step0 raw2306; decide +kernel
      have hl : raw2306step0Labels = raw2306Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2306 raw2306Labels permutation12 permutation6
    mixedMoment B raw2306step0 raw2306step0Labels = mixedMoment B raw2306step1 raw2306step1Labels := by
      have ha : raw2306step1 = -raw2306step0 := by apply Matrix.ext; change ∀ i j, raw2306step1 i j = -(raw2306step0 i j); unfold raw2306step1 raw2306step0; decide +kernel
      have hl : raw2306step1Labels = raw2306step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2306step1 raw2306step1Labels = mixedMoment B raw2306step2 raw2306step2Labels := by
      have ha : raw2306step2 = raw2306step1 := by apply Matrix.ext; unfold raw2306step2 raw2306step1; decide +kernel
      have hl : raw2306step1Labels = labelEmbedding1 ∘ raw2306step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2306step1 raw2306step1Labels raw2306step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3632 node3632Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical180
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23046 raw23046Labels = mixedMoment B node4106 node4106Labels := by
  calc
    mixedMoment B raw23046 raw23046Labels = mixedMoment B raw23046step0 raw23046step0Labels := by
      have hz : ∀ j, raw23046 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23046step0 = (fun i j => raw23046 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23046step0 raw23046; decide +kernel
      have hl : raw23046step0Labels = raw23046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23046 raw23046Labels permutation346 hz
    mixedMoment B raw23046step0 raw23046step0Labels = mixedMoment B raw23046step1 raw23046step1Labels := by
      have ha : raw23046step1 = (fun i j => raw23046step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23046step1 raw23046step0; decide +kernel
      have hl : raw23046step1Labels = raw23046step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23046step0 raw23046step0Labels permutation33 permutation3
    mixedMoment B raw23046step1 raw23046step1Labels = mixedMoment B raw23046step2 raw23046step2Labels := by
      have ha : raw23046step2 = raw23046step1 := by apply Matrix.ext; unfold raw23046step2 raw23046step1; decide +kernel
      have hl : raw23046step1Labels = labelEmbedding6 ∘ raw23046step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23046step1 raw23046step1Labels raw23046step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4106 node4106Labels := by rfl

theorem canonical23047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23047 raw23047Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw23047 raw23047Labels = mixedMoment B raw23047step0 raw23047step0Labels := by
      have hz : ∀ j, raw23047 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23047step0 = (fun i j => raw23047 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23047step0 raw23047; decide +kernel
      have hl : raw23047step0Labels = raw23047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23047 raw23047Labels permutation346 hz
    mixedMoment B raw23047step0 raw23047step0Labels = mixedMoment B raw23047step1 raw23047step1Labels := by
      have ha : raw23047step1 = (fun i j => raw23047step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23047step1 raw23047step0; decide +kernel
      have hl : raw23047step1Labels = raw23047step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23047step0 raw23047step0Labels permutation33 permutation3
    mixedMoment B raw23047step1 raw23047step1Labels = mixedMoment B raw23047step2 raw23047step2Labels := by
      have ha : raw23047step2 = raw23047step1 := by apply Matrix.ext; unfold raw23047step2 raw23047step1; decide +kernel
      have hl : raw23047step1Labels = labelEmbedding6 ∘ raw23047step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23047step1 raw23047step1Labels raw23047step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4354 node4354Labels := by rfl

theorem canonical23048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23048 raw23048Labels = mixedMoment B node4291 node4291Labels := by
  calc
    mixedMoment B raw23048 raw23048Labels = mixedMoment B raw23048step0 raw23048step0Labels := by
      have ha : raw23048step0 = (fun i j => raw23048 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23048step0 raw23048; decide +kernel
      have hl : raw23048step0Labels = raw23048Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23048 raw23048Labels permutation177 permutation3
    mixedMoment B raw23048step0 raw23048step0Labels = mixedMoment B raw23048step1 raw23048step1Labels := by
      have ha : raw23048step1 = raw23048step0 := by apply Matrix.ext; unfold raw23048step1 raw23048step0; decide +kernel
      have hl : raw23048step0Labels = labelEmbedding6 ∘ raw23048step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23048step0 raw23048step0Labels raw23048step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4291 node4291Labels := by rfl

theorem canonical23054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23054 raw23054Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw23054 raw23054Labels = mixedMoment B raw23054step0 raw23054step0Labels := by
      have hz : ∀ j, raw23054 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23054step0 = (fun i j => raw23054 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23054step0 raw23054; decide +kernel
      have hl : raw23054step0Labels = raw23054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23054 raw23054Labels permutation434 hz
    mixedMoment B raw23054step0 raw23054step0Labels = mixedMoment B raw23054step1 raw23054step1Labels := by
      have hz : ∀ j, raw23054step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23054step1 = (fun i j => raw23054step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23054step1 raw23054step0; decide +kernel
      have hl : raw23054step1Labels = raw23054step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23054step0 raw23054step0Labels permutation80 hz
    mixedMoment B raw23054step1 raw23054step1Labels = mixedMoment B raw23054step2 raw23054step2Labels := by
      have ha : raw23054step2 = (fun i j => raw23054step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23054step2 raw23054step1; decide +kernel
      have hl : raw23054step2Labels = raw23054step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23054step1 raw23054step1Labels permutation8 permutation3
    mixedMoment B raw23054step2 raw23054step2Labels = mixedMoment B raw23054step3 raw23054step3Labels := by
      have ha : raw23054step3 = raw23054step2 := by apply Matrix.ext; unfold raw23054step3 raw23054step2; decide +kernel
      have hl : raw23054step2Labels = labelEmbedding6 ∘ raw23054step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23054step2 raw23054step2Labels raw23054step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical195
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25067 raw25067Labels = mixedMoment B node4126 node4126Labels := by
  calc
    mixedMoment B raw25067 raw25067Labels = mixedMoment B raw25067step0 raw25067step0Labels := by
      have hz : ∀ j, raw25067 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25067step0 = (fun i j => raw25067 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25067step0 raw25067; decide +kernel
      have hl : raw25067step0Labels = raw25067Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25067 raw25067Labels permutation346 hz
    mixedMoment B raw25067step0 raw25067step0Labels = mixedMoment B raw25067step1 raw25067step1Labels := by
      have ha : raw25067step1 = (fun i j => raw25067step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25067step1 raw25067step0; decide +kernel
      have hl : raw25067step1Labels = raw25067step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25067step0 raw25067step0Labels permutation40 permutation3
    mixedMoment B raw25067step1 raw25067step1Labels = mixedMoment B raw25067step2 raw25067step2Labels := by
      have ha : raw25067step2 = raw25067step1 := by apply Matrix.ext; unfold raw25067step2 raw25067step1; decide +kernel
      have hl : raw25067step1Labels = labelEmbedding6 ∘ raw25067step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25067step1 raw25067step1Labels raw25067step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4126 node4126Labels := by rfl

theorem canonical25068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25068 raw25068Labels = mixedMoment B node4307 node4307Labels := by
  calc
    mixedMoment B raw25068 raw25068Labels = mixedMoment B raw25068step0 raw25068step0Labels := by
      have ha : raw25068step0 = (fun i j => raw25068 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25068step0 raw25068; decide +kernel
      have hl : raw25068step0Labels = raw25068Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25068 raw25068Labels permutation184 permutation3
    mixedMoment B raw25068step0 raw25068step0Labels = mixedMoment B raw25068step1 raw25068step1Labels := by
      have ha : raw25068step1 = raw25068step0 := by apply Matrix.ext; unfold raw25068step1 raw25068step0; decide +kernel
      have hl : raw25068step0Labels = labelEmbedding6 ∘ raw25068step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25068step0 raw25068step0Labels raw25068step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4307 node4307Labels := by rfl

theorem canonical25069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25069 raw25069Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw25069 raw25069Labels = mixedMoment B raw25069step0 raw25069step0Labels := by
      have hz : ∀ j, raw25069 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25069step0 = (fun i j => raw25069 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25069step0 raw25069; decide +kernel
      have hl : raw25069step0Labels = raw25069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25069 raw25069Labels permutation520 hz
    mixedMoment B raw25069step0 raw25069step0Labels = mixedMoment B raw25069step1 raw25069step1Labels := by
      have hz : ∀ j, raw25069step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25069step1 = (fun i j => raw25069step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25069step1 raw25069step0; decide +kernel
      have hl : raw25069step1Labels = raw25069step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25069step0 raw25069step0Labels permutation80 hz
    mixedMoment B raw25069step1 raw25069step1Labels = mixedMoment B raw25069step2 raw25069step2Labels := by
      have ha : raw25069step2 = (fun i j => raw25069step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25069step2 raw25069step1; decide +kernel
      have hl : raw25069step2Labels = raw25069step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25069step1 raw25069step1Labels permutation10 permutation3
    mixedMoment B raw25069step2 raw25069step2Labels = mixedMoment B raw25069step3 raw25069step3Labels := by
      have ha : raw25069step3 = raw25069step2 := by apply Matrix.ext; unfold raw25069step3 raw25069step2; decide +kernel
      have hl : raw25069step2Labels = labelEmbedding6 ∘ raw25069step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25069step2 raw25069step2Labels raw25069step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

theorem canonical25070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25070 raw25070Labels = mixedMoment B node4104 node4104Labels := by
  calc
    mixedMoment B raw25070 raw25070Labels = mixedMoment B raw25070step0 raw25070step0Labels := by
      have ha : raw25070step0 = (fun i j => raw25070 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25070step0 raw25070; decide +kernel
      have hl : raw25070step0Labels = raw25070Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25070 raw25070Labels permutation152 permutation3
    mixedMoment B raw25070step0 raw25070step0Labels = mixedMoment B raw25070step1 raw25070step1Labels := by
      have ha : raw25070step1 = raw25070step0 := by apply Matrix.ext; unfold raw25070step1 raw25070step0; decide +kernel
      have hl : raw25070step0Labels = labelEmbedding6 ∘ raw25070step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25070step0 raw25070step0Labels raw25070step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4104 node4104Labels := by rfl

theorem canonical25071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25071 raw25071Labels = mixedMoment B node4351 node4351Labels := by
  calc
    mixedMoment B raw25071 raw25071Labels = mixedMoment B raw25071step0 raw25071step0Labels := by
      have ha : raw25071step0 = (fun i j => raw25071 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25071step0 raw25071; decide +kernel
      have hl : raw25071step0Labels = raw25071Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25071 raw25071Labels permutation152 permutation3
    mixedMoment B raw25071step0 raw25071step0Labels = mixedMoment B raw25071step1 raw25071step1Labels := by
      have ha : raw25071step1 = raw25071step0 := by apply Matrix.ext; unfold raw25071step1 raw25071step0; decide +kernel
      have hl : raw25071step0Labels = labelEmbedding6 ∘ raw25071step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25071step0 raw25071step0Labels raw25071step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4351 node4351Labels := by rfl

theorem canonical25072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25072 raw25072Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw25072 raw25072Labels = mixedMoment B raw25072step0 raw25072step0Labels := by
      have hz : ∀ j, raw25072 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25072step0 = (fun i j => raw25072 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25072step0 raw25072; decide +kernel
      have hl : raw25072step0Labels = raw25072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25072 raw25072Labels permutation520 hz
    mixedMoment B raw25072step0 raw25072step0Labels = mixedMoment B raw25072step1 raw25072step1Labels := by
      have ha : raw25072step1 = (fun i j => raw25072step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25072step1 raw25072step0; decide +kernel
      have hl : raw25072step1Labels = raw25072step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25072step0 raw25072step0Labels permutation32 permutation3
    mixedMoment B raw25072step1 raw25072step1Labels = mixedMoment B raw25072step2 raw25072step2Labels := by
      have ha : raw25072step2 = raw25072step1 := by apply Matrix.ext; unfold raw25072step2 raw25072step1; decide +kernel
      have hl : raw25072step1Labels = labelEmbedding6 ∘ raw25072step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25072step1 raw25072step1Labels raw25072step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4461 node4461Labels := by rfl

theorem canonical25073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25073 raw25073Labels = mixedMoment B node4106 node4106Labels := by
  calc
    mixedMoment B raw25073 raw25073Labels = mixedMoment B raw25073step0 raw25073step0Labels := by
      have hz : ∀ j, raw25073 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25073step0 = (fun i j => raw25073 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25073step0 raw25073; decide +kernel
      have hl : raw25073step0Labels = raw25073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25073 raw25073Labels permutation346 hz
    mixedMoment B raw25073step0 raw25073step0Labels = mixedMoment B raw25073step1 raw25073step1Labels := by
      have ha : raw25073step1 = (fun i j => raw25073step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25073step1 raw25073step0; decide +kernel
      have hl : raw25073step1Labels = raw25073step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25073step0 raw25073step0Labels permutation35 permutation3
    mixedMoment B raw25073step1 raw25073step1Labels = mixedMoment B raw25073step2 raw25073step2Labels := by
      have ha : raw25073step2 = raw25073step1 := by apply Matrix.ext; unfold raw25073step2 raw25073step1; decide +kernel
      have hl : raw25073step1Labels = labelEmbedding6 ∘ raw25073step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25073step1 raw25073step1Labels raw25073step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4106 node4106Labels := by rfl

theorem canonical25074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25074 raw25074Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw25074 raw25074Labels = mixedMoment B raw25074step0 raw25074step0Labels := by
      have hz : ∀ j, raw25074 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25074step0 = (fun i j => raw25074 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25074step0 raw25074; decide +kernel
      have hl : raw25074step0Labels = raw25074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25074 raw25074Labels permutation346 hz
    mixedMoment B raw25074step0 raw25074step0Labels = mixedMoment B raw25074step1 raw25074step1Labels := by
      have ha : raw25074step1 = (fun i j => raw25074step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25074step1 raw25074step0; decide +kernel
      have hl : raw25074step1Labels = raw25074step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25074step0 raw25074step0Labels permutation35 permutation3
    mixedMoment B raw25074step1 raw25074step1Labels = mixedMoment B raw25074step2 raw25074step2Labels := by
      have ha : raw25074step2 = raw25074step1 := by apply Matrix.ext; unfold raw25074step2 raw25074step1; decide +kernel
      have hl : raw25074step1Labels = labelEmbedding6 ∘ raw25074step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25074step1 raw25074step1Labels raw25074step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4354 node4354Labels := by rfl

theorem canonical25075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25075 raw25075Labels = mixedMoment B node4291 node4291Labels := by
  calc
    mixedMoment B raw25075 raw25075Labels = mixedMoment B raw25075step0 raw25075step0Labels := by
      have ha : raw25075step0 = (fun i j => raw25075 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25075step0 raw25075; decide +kernel
      have hl : raw25075step0Labels = raw25075Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25075 raw25075Labels permutation179 permutation3
    mixedMoment B raw25075step0 raw25075step0Labels = mixedMoment B raw25075step1 raw25075step1Labels := by
      have ha : raw25075step1 = raw25075step0 := by apply Matrix.ext; unfold raw25075step1 raw25075step0; decide +kernel
      have hl : raw25075step0Labels = labelEmbedding6 ∘ raw25075step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25075step0 raw25075step0Labels raw25075step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4291 node4291Labels := by rfl

theorem canonical25076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25076 raw25076Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw25076 raw25076Labels = mixedMoment B raw25076step0 raw25076step0Labels := by
      have hz : ∀ j, raw25076 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25076step0 = (fun i j => raw25076 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25076step0 raw25076; decide +kernel
      have hl : raw25076step0Labels = raw25076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25076 raw25076Labels permutation520 hz
    mixedMoment B raw25076step0 raw25076step0Labels = mixedMoment B raw25076step1 raw25076step1Labels := by
      have hz : ∀ j, raw25076step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25076step1 = (fun i j => raw25076step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25076step1 raw25076step0; decide +kernel
      have hl : raw25076step1Labels = raw25076step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25076step0 raw25076step0Labels permutation80 hz
    mixedMoment B raw25076step1 raw25076step1Labels = mixedMoment B raw25076step2 raw25076step2Labels := by
      have ha : raw25076step2 = (fun i j => raw25076step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25076step2 raw25076step1; decide +kernel
      have hl : raw25076step2Labels = raw25076step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25076step1 raw25076step1Labels permutation9 permutation3
    mixedMoment B raw25076step2 raw25076step2Labels = mixedMoment B raw25076step3 raw25076step3Labels := by
      have ha : raw25076step3 = raw25076step2 := by apply Matrix.ext; unfold raw25076step3 raw25076step2; decide +kernel
      have hl : raw25076step2Labels = labelEmbedding6 ∘ raw25076step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25076step2 raw25076step2Labels raw25076step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw272 raw272Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw272 raw272Labels = mixedMoment B raw272step0 raw272step0Labels := by
      have ha : raw272step0 = (fun i j => raw272 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw272step0 raw272; decide +kernel
      have hl : raw272step0Labels = raw272Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw272 raw272Labels permutation8 permutation5
    mixedMoment B raw272step0 raw272step0Labels = mixedMoment B raw272step1 raw272step1Labels := by
      have ha : raw272step1 = raw272step0 := by apply Matrix.ext; unfold raw272step1 raw272step0; decide +kernel
      have hl : raw272step0Labels = labelEmbedding1 ∘ raw272step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw272step0 raw272step0Labels raw272step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2768 node2768Labels := by rfl

theorem canonical273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw273 raw273Labels = mixedMoment B node405 node405Labels := by
  calc
    mixedMoment B raw273 raw273Labels = mixedMoment B raw273step0 raw273step0Labels := by
      have ha : raw273step0 = (fun i j => raw273 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw273step0 raw273; decide +kernel
      have hl : raw273step0Labels = raw273Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw273 raw273Labels permutation8 permutation5
    _ = mixedMoment B node405 node405Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3044 raw3044Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw3044 raw3044Labels = mixedMoment B raw3044step0 raw3044step0Labels := by
      have hz : ∀ j, raw3044 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3044step0 = (fun i j => raw3044 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3044step0 raw3044; decide +kernel
      have hl : raw3044step0Labels = raw3044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3044 raw3044Labels permutation346 hz
    mixedMoment B raw3044step0 raw3044step0Labels = mixedMoment B raw3044step1 raw3044step1Labels := by
      have ha : raw3044step1 = (fun i j => raw3044step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3044step1 raw3044step0; decide +kernel
      have hl : raw3044step1Labels = raw3044step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3044step0 raw3044step0Labels permutation36 permutation3
    mixedMoment B raw3044step1 raw3044step1Labels = mixedMoment B raw3044step2 raw3044step2Labels := by
      have ha : raw3044step2 = raw3044step1 := by apply Matrix.ext; unfold raw3044step2 raw3044step1; decide +kernel
      have hl : raw3044step1Labels = labelEmbedding6 ∘ raw3044step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3044step1 raw3044step1Labels raw3044step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical3054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3054 raw3054Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw3054 raw3054Labels = mixedMoment B raw3054step0 raw3054step0Labels := by
      have hz : ∀ j, raw3054 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3054step0 = (fun i j => raw3054 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3054step0 raw3054; decide +kernel
      have hl : raw3054step0Labels = raw3054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3054 raw3054Labels permutation434 hz
    mixedMoment B raw3054step0 raw3054step0Labels = mixedMoment B raw3054step1 raw3054step1Labels := by
      have hz : ∀ j, raw3054step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3054step1 = (fun i j => raw3054step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3054step1 raw3054step0; decide +kernel
      have hl : raw3054step1Labels = raw3054step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3054step0 raw3054step0Labels permutation80 hz
    mixedMoment B raw3054step1 raw3054step1Labels = mixedMoment B raw3054step2 raw3054step2Labels := by
      have ha : raw3054step2 = (fun i j => raw3054step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3054step2 raw3054step1; decide +kernel
      have hl : raw3054step2Labels = raw3054step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3054step1 raw3054step1Labels permutation8 permutation3
    mixedMoment B raw3054step2 raw3054step2Labels = mixedMoment B raw3054step3 raw3054step3Labels := by
      have ha : raw3054step3 = raw3054step2 := by apply Matrix.ext; unfold raw3054step3 raw3054step2; decide +kernel
      have hl : raw3054step2Labels = labelEmbedding6 ∘ raw3054step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3054step2 raw3054step2Labels raw3054step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

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

theorem canonical684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw684 raw684Labels = mixedMoment B node4104 node4104Labels := by
  calc
    mixedMoment B raw684 raw684Labels = mixedMoment B raw684step0 raw684step0Labels := by
      have ha : raw684step0 = (fun i j => raw684 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw684step0 raw684; decide +kernel
      have hl : raw684step0Labels = raw684Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw684 raw684Labels permutation152 permutation4
    mixedMoment B raw684step0 raw684step0Labels = mixedMoment B raw684step1 raw684step1Labels := by
      have ha : raw684step1 = raw684step0 := by apply Matrix.ext; unfold raw684step1 raw684step0; decide +kernel
      have hl : raw684step0Labels = labelEmbedding7 ∘ raw684step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw684step0 raw684step0Labels raw684step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4104 node4104Labels := by rfl

theorem canonical685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw685 raw685Labels = mixedMoment B node541 node541Labels := by
  calc
    mixedMoment B raw685 raw685Labels = mixedMoment B raw685step0 raw685step0Labels := by
      have ha : raw685step0 = (fun i j => raw685 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw685step0 raw685; decide +kernel
      have hl : raw685step0Labels = raw685Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw685 raw685Labels permutation152 permutation4
    _ = mixedMoment B node541 node541Labels := by rfl

theorem canonical686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw686 raw686Labels = mixedMoment B node674 node674Labels := by
  calc
    mixedMoment B raw686 raw686Labels = mixedMoment B raw686step0 raw686step0Labels := by
      have ha : raw686step0 = (fun i j => raw686 (permutation246 i) (permutation6 j)) := by apply Matrix.ext; unfold raw686step0 raw686; decide +kernel
      have hl : raw686step0Labels = raw686Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw686 raw686Labels permutation246 permutation6
    mixedMoment B raw686step0 raw686step0Labels = mixedMoment B raw686step1 raw686step1Labels := by
      have ha : raw686step1 = -raw686step0 := by apply Matrix.ext; change ∀ i j, raw686step1 i j = -(raw686step0 i j); unfold raw686step1 raw686step0; decide +kernel
      have hl : raw686step1Labels = raw686step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw686step1 raw686step1Labels = mixedMoment B raw686step2 raw686step2Labels := by
      have ha : raw686step2 = raw686step1 := by apply Matrix.ext; unfold raw686step2 raw686step1; decide +kernel
      have hl : raw686step1Labels = labelEmbedding1 ∘ raw686step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw686step1 raw686step1Labels raw686step2Labels labelEmbedding1 hl
    _ = mixedMoment B node674 node674Labels := by rfl

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

theorem canonical690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw690 raw690Labels = mixedMoment B node4106 node4106Labels := by
  calc
    mixedMoment B raw690 raw690Labels = mixedMoment B raw690step0 raw690step0Labels := by
      have ha : raw690step0 = (fun i j => raw690 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw690step0 raw690; decide +kernel
      have hl : raw690step0Labels = raw690Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw690 raw690Labels permutation32 permutation4
    mixedMoment B raw690step0 raw690step0Labels = mixedMoment B raw690step1 raw690step1Labels := by
      have ha : raw690step1 = raw690step0 := by apply Matrix.ext; unfold raw690step1 raw690step0; decide +kernel
      have hl : raw690step0Labels = labelEmbedding7 ∘ raw690step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw690step0 raw690step0Labels raw690step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4106 node4106Labels := by rfl

theorem canonical691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw691 raw691Labels = mixedMoment B node543 node543Labels := by
  calc
    mixedMoment B raw691 raw691Labels = mixedMoment B raw691step0 raw691step0Labels := by
      have ha : raw691step0 = (fun i j => raw691 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw691step0 raw691; decide +kernel
      have hl : raw691step0Labels = raw691Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw691 raw691Labels permutation32 permutation4
    _ = mixedMoment B node543 node543Labels := by rfl

theorem canonical692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw692 raw692Labels = mixedMoment B node675 node675Labels := by
  calc
    mixedMoment B raw692 raw692Labels = mixedMoment B raw692step0 raw692step0Labels := by
      have ha : raw692step0 = (fun i j => raw692 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw692step0 raw692; decide +kernel
      have hl : raw692step0Labels = raw692Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw692 raw692Labels permutation44 permutation6
    mixedMoment B raw692step0 raw692step0Labels = mixedMoment B raw692step1 raw692step1Labels := by
      have ha : raw692step1 = -raw692step0 := by apply Matrix.ext; change ∀ i j, raw692step1 i j = -(raw692step0 i j); unfold raw692step1 raw692step0; decide +kernel
      have hl : raw692step1Labels = raw692step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw692step1 raw692step1Labels = mixedMoment B raw692step2 raw692step2Labels := by
      have ha : raw692step2 = raw692step1 := by apply Matrix.ext; unfold raw692step2 raw692step1; decide +kernel
      have hl : raw692step1Labels = labelEmbedding1 ∘ raw692step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw692step1 raw692step1Labels raw692step2Labels labelEmbedding1 hl
    _ = mixedMoment B node675 node675Labels := by rfl

theorem canonical732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw732 raw732Labels = mixedMoment B node4126 node4126Labels := by
  calc
    mixedMoment B raw732 raw732Labels = mixedMoment B raw732step0 raw732step0Labels := by
      have ha : raw732step0 = (fun i j => raw732 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw732step0 raw732; decide +kernel
      have hl : raw732step0Labels = raw732Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw732 raw732Labels permutation32 permutation4
    mixedMoment B raw732step0 raw732step0Labels = mixedMoment B raw732step1 raw732step1Labels := by
      have ha : raw732step1 = raw732step0 := by apply Matrix.ext; unfold raw732step1 raw732step0; decide +kernel
      have hl : raw732step0Labels = labelEmbedding7 ∘ raw732step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw732step0 raw732step0Labels raw732step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4126 node4126Labels := by rfl

theorem canonical733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw733 raw733Labels = mixedMoment B node557 node557Labels := by
  calc
    mixedMoment B raw733 raw733Labels = mixedMoment B raw733step0 raw733step0Labels := by
      have ha : raw733step0 = (fun i j => raw733 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw733step0 raw733; decide +kernel
      have hl : raw733step0Labels = raw733Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw733 raw733Labels permutation32 permutation4
    _ = mixedMoment B node557 node557Labels := by rfl

theorem canonical734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw734 raw734Labels = mixedMoment B node677 node677Labels := by
  calc
    mixedMoment B raw734 raw734Labels = mixedMoment B raw734step0 raw734step0Labels := by
      have ha : raw734step0 = (fun i j => raw734 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw734step0 raw734; decide +kernel
      have hl : raw734step0Labels = raw734Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw734 raw734Labels permutation50 permutation6
    mixedMoment B raw734step0 raw734step0Labels = mixedMoment B raw734step1 raw734step1Labels := by
      have ha : raw734step1 = -raw734step0 := by apply Matrix.ext; change ∀ i j, raw734step1 i j = -(raw734step0 i j); unfold raw734step1 raw734step0; decide +kernel
      have hl : raw734step1Labels = raw734step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw734step1 raw734step1Labels = mixedMoment B raw734step2 raw734step2Labels := by
      have ha : raw734step2 = raw734step1 := by apply Matrix.ext; unfold raw734step2 raw734step1; decide +kernel
      have hl : raw734step1Labels = labelEmbedding1 ∘ raw734step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw734step1 raw734step1Labels raw734step2Labels labelEmbedding1 hl
    _ = mixedMoment B node677 node677Labels := by rfl

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

theorem canonical1032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1032 raw1032Labels = mixedMoment B node4290 node4290Labels := by
  calc
    mixedMoment B raw1032 raw1032Labels = mixedMoment B raw1032step0 raw1032step0Labels := by
      have ha : raw1032step0 = (fun i j => raw1032 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1032step0 raw1032; decide +kernel
      have hl : raw1032step0Labels = raw1032Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1032 raw1032Labels permutation152 permutation4
    mixedMoment B raw1032step0 raw1032step0Labels = mixedMoment B raw1032step1 raw1032step1Labels := by
      have ha : raw1032step1 = raw1032step0 := by apply Matrix.ext; unfold raw1032step1 raw1032step0; decide +kernel
      have hl : raw1032step0Labels = labelEmbedding7 ∘ raw1032step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1032step0 raw1032step0Labels raw1032step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4290 node4290Labels := by rfl

theorem canonical1033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1033 raw1033Labels = mixedMoment B node868 node868Labels := by
  calc
    mixedMoment B raw1033 raw1033Labels = mixedMoment B raw1033step0 raw1033step0Labels := by
      have ha : raw1033step0 = (fun i j => raw1033 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1033step0 raw1033; decide +kernel
      have hl : raw1033step0Labels = raw1033Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1033 raw1033Labels permutation152 permutation4
    _ = mixedMoment B node868 node868Labels := by rfl

theorem canonical1034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1034 raw1034Labels = mixedMoment B node1566 node1566Labels := by
  calc
    mixedMoment B raw1034 raw1034Labels = mixedMoment B raw1034step0 raw1034step0Labels := by
      have ha : raw1034step0 = (fun i j => raw1034 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1034step0 raw1034; decide +kernel
      have hl : raw1034step0Labels = raw1034Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1034 raw1034Labels permutation152 permutation6
    mixedMoment B raw1034step0 raw1034step0Labels = mixedMoment B raw1034step1 raw1034step1Labels := by
      have ha : raw1034step1 = -raw1034step0 := by apply Matrix.ext; change ∀ i j, raw1034step1 i j = -(raw1034step0 i j); unfold raw1034step1 raw1034step0; decide +kernel
      have hl : raw1034step1Labels = raw1034step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1034step1 raw1034step1Labels = mixedMoment B raw1034step2 raw1034step2Labels := by
      have ha : raw1034step2 = raw1034step1 := by apply Matrix.ext; unfold raw1034step2 raw1034step1; decide +kernel
      have hl : raw1034step1Labels = labelEmbedding1 ∘ raw1034step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1034step1 raw1034step1Labels raw1034step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1566 node1566Labels := by rfl

theorem canonical1035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1035 raw1035Labels = mixedMoment B node4291 node4291Labels := by
  calc
    mixedMoment B raw1035 raw1035Labels = mixedMoment B raw1035step0 raw1035step0Labels := by
      have ha : raw1035step0 = (fun i j => raw1035 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1035step0 raw1035; decide +kernel
      have hl : raw1035step0Labels = raw1035Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1035 raw1035Labels permutation152 permutation4
    mixedMoment B raw1035step0 raw1035step0Labels = mixedMoment B raw1035step1 raw1035step1Labels := by
      have ha : raw1035step1 = raw1035step0 := by apply Matrix.ext; unfold raw1035step1 raw1035step0; decide +kernel
      have hl : raw1035step0Labels = labelEmbedding7 ∘ raw1035step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1035step0 raw1035step0Labels raw1035step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4291 node4291Labels := by rfl

theorem canonical1036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1036 raw1036Labels = mixedMoment B node869 node869Labels := by
  calc
    mixedMoment B raw1036 raw1036Labels = mixedMoment B raw1036step0 raw1036step0Labels := by
      have ha : raw1036step0 = (fun i j => raw1036 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1036step0 raw1036; decide +kernel
      have hl : raw1036step0Labels = raw1036Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1036 raw1036Labels permutation152 permutation4
    _ = mixedMoment B node869 node869Labels := by rfl

theorem canonical1037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1037 raw1037Labels = mixedMoment B node1561 node1561Labels := by
  calc
    mixedMoment B raw1037 raw1037Labels = mixedMoment B raw1037step0 raw1037step0Labels := by
      have ha : raw1037step0 = (fun i j => raw1037 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1037step0 raw1037; decide +kernel
      have hl : raw1037step0Labels = raw1037Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1037 raw1037Labels permutation164 permutation6
    mixedMoment B raw1037step0 raw1037step0Labels = mixedMoment B raw1037step1 raw1037step1Labels := by
      have ha : raw1037step1 = -raw1037step0 := by apply Matrix.ext; change ∀ i j, raw1037step1 i j = -(raw1037step0 i j); unfold raw1037step1 raw1037step0; decide +kernel
      have hl : raw1037step1Labels = raw1037step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1037step1 raw1037step1Labels = mixedMoment B raw1037step2 raw1037step2Labels := by
      have ha : raw1037step2 = raw1037step1 := by apply Matrix.ext; unfold raw1037step2 raw1037step1; decide +kernel
      have hl : raw1037step1Labels = labelEmbedding1 ∘ raw1037step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1037step1 raw1037step1Labels raw1037step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1561 node1561Labels := by rfl

theorem canonical1071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1071 raw1071Labels = mixedMoment B node4307 node4307Labels := by
  calc
    mixedMoment B raw1071 raw1071Labels = mixedMoment B raw1071step0 raw1071step0Labels := by
      have ha : raw1071step0 = (fun i j => raw1071 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1071step0 raw1071; decide +kernel
      have hl : raw1071step0Labels = raw1071Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1071 raw1071Labels permutation152 permutation4
    mixedMoment B raw1071step0 raw1071step0Labels = mixedMoment B raw1071step1 raw1071step1Labels := by
      have ha : raw1071step1 = raw1071step0 := by apply Matrix.ext; unfold raw1071step1 raw1071step0; decide +kernel
      have hl : raw1071step0Labels = labelEmbedding7 ∘ raw1071step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1071step0 raw1071step0Labels raw1071step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4307 node4307Labels := by rfl

theorem canonical1072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1072 raw1072Labels = mixedMoment B node885 node885Labels := by
  calc
    mixedMoment B raw1072 raw1072Labels = mixedMoment B raw1072step0 raw1072step0Labels := by
      have ha : raw1072step0 = (fun i j => raw1072 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1072step0 raw1072; decide +kernel
      have hl : raw1072step0Labels = raw1072Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1072 raw1072Labels permutation152 permutation4
    _ = mixedMoment B node885 node885Labels := by rfl

theorem canonical1073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1073 raw1073Labels = mixedMoment B node1563 node1563Labels := by
  calc
    mixedMoment B raw1073 raw1073Labels = mixedMoment B raw1073step0 raw1073step0Labels := by
      have ha : raw1073step0 = (fun i j => raw1073 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1073step0 raw1073; decide +kernel
      have hl : raw1073step0Labels = raw1073Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1073 raw1073Labels permutation170 permutation6
    mixedMoment B raw1073step0 raw1073step0Labels = mixedMoment B raw1073step1 raw1073step1Labels := by
      have ha : raw1073step1 = -raw1073step0 := by apply Matrix.ext; change ∀ i j, raw1073step1 i j = -(raw1073step0 i j); unfold raw1073step1 raw1073step0; decide +kernel
      have hl : raw1073step1Labels = raw1073step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1073step1 raw1073step1Labels = mixedMoment B raw1073step2 raw1073step2Labels := by
      have ha : raw1073step2 = raw1073step1 := by apply Matrix.ext; unfold raw1073step2 raw1073step1; decide +kernel
      have hl : raw1073step1Labels = labelEmbedding1 ∘ raw1073step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1073step1 raw1073step1Labels raw1073step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1563 node1563Labels := by rfl

theorem canonical1140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1140 raw1140Labels = mixedMoment B node4351 node4351Labels := by
  calc
    mixedMoment B raw1140 raw1140Labels = mixedMoment B raw1140step0 raw1140step0Labels := by
      have ha : raw1140step0 = (fun i j => raw1140 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1140step0 raw1140; decide +kernel
      have hl : raw1140step0Labels = raw1140Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1140 raw1140Labels permutation152 permutation4
    mixedMoment B raw1140step0 raw1140step0Labels = mixedMoment B raw1140step1 raw1140step1Labels := by
      have ha : raw1140step1 = raw1140step0 := by apply Matrix.ext; unfold raw1140step1 raw1140step0; decide +kernel
      have hl : raw1140step0Labels = labelEmbedding7 ∘ raw1140step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1140step0 raw1140step0Labels raw1140step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4351 node4351Labels := by rfl

theorem canonical1141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1141 raw1141Labels = mixedMoment B node929 node929Labels := by
  calc
    mixedMoment B raw1141 raw1141Labels = mixedMoment B raw1141step0 raw1141step0Labels := by
      have ha : raw1141step0 = (fun i j => raw1141 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1141step0 raw1141; decide +kernel
      have hl : raw1141step0Labels = raw1141Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1141 raw1141Labels permutation152 permutation4
    _ = mixedMoment B node929 node929Labels := by rfl

theorem canonical1142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1142 raw1142Labels = mixedMoment B node1680 node1680Labels := by
  calc
    mixedMoment B raw1142 raw1142Labels = mixedMoment B raw1142step0 raw1142step0Labels := by
      have ha : raw1142step0 = (fun i j => raw1142 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1142step0 raw1142; decide +kernel
      have hl : raw1142step0Labels = raw1142Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1142 raw1142Labels permutation170 permutation6
    mixedMoment B raw1142step0 raw1142step0Labels = mixedMoment B raw1142step1 raw1142step1Labels := by
      have ha : raw1142step1 = -raw1142step0 := by apply Matrix.ext; change ∀ i j, raw1142step1 i j = -(raw1142step0 i j); unfold raw1142step1 raw1142step0; decide +kernel
      have hl : raw1142step1Labels = raw1142step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1142step1 raw1142step1Labels = mixedMoment B raw1142step2 raw1142step2Labels := by
      have ha : raw1142step2 = raw1142step1 := by apply Matrix.ext; unfold raw1142step2 raw1142step1; decide +kernel
      have hl : raw1142step1Labels = labelEmbedding1 ∘ raw1142step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1142step1 raw1142step1Labels raw1142step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1680 node1680Labels := by rfl

theorem canonical1143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1143 raw1143Labels = mixedMoment B node4352 node4352Labels := by
  calc
    mixedMoment B raw1143 raw1143Labels = mixedMoment B raw1143step0 raw1143step0Labels := by
      have ha : raw1143step0 = (fun i j => raw1143 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1143step0 raw1143; decide +kernel
      have hl : raw1143step0Labels = raw1143Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1143 raw1143Labels permutation32 permutation4
    mixedMoment B raw1143step0 raw1143step0Labels = mixedMoment B raw1143step1 raw1143step1Labels := by
      have ha : raw1143step1 = raw1143step0 := by apply Matrix.ext; unfold raw1143step1 raw1143step0; decide +kernel
      have hl : raw1143step0Labels = labelEmbedding7 ∘ raw1143step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1143step0 raw1143step0Labels raw1143step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4352 node4352Labels := by rfl

theorem canonical1144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1144 raw1144Labels = mixedMoment B node930 node930Labels := by
  calc
    mixedMoment B raw1144 raw1144Labels = mixedMoment B raw1144step0 raw1144step0Labels := by
      have ha : raw1144step0 = (fun i j => raw1144 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1144step0 raw1144; decide +kernel
      have hl : raw1144step0Labels = raw1144Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1144 raw1144Labels permutation32 permutation4
    _ = mixedMoment B node930 node930Labels := by rfl

theorem canonical1145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1145 raw1145Labels = mixedMoment B node1690 node1690Labels := by
  calc
    mixedMoment B raw1145 raw1145Labels = mixedMoment B raw1145step0 raw1145step0Labels := by
      have ha : raw1145step0 = (fun i j => raw1145 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1145step0 raw1145; decide +kernel
      have hl : raw1145step0Labels = raw1145Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1145 raw1145Labels permutation32 permutation6
    mixedMoment B raw1145step0 raw1145step0Labels = mixedMoment B raw1145step1 raw1145step1Labels := by
      have ha : raw1145step1 = -raw1145step0 := by apply Matrix.ext; change ∀ i j, raw1145step1 i j = -(raw1145step0 i j); unfold raw1145step1 raw1145step0; decide +kernel
      have hl : raw1145step1Labels = raw1145step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1145step1 raw1145step1Labels = mixedMoment B raw1145step2 raw1145step2Labels := by
      have ha : raw1145step2 = raw1145step1 := by apply Matrix.ext; unfold raw1145step2 raw1145step1; decide +kernel
      have hl : raw1145step1Labels = labelEmbedding1 ∘ raw1145step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1145step1 raw1145step1Labels raw1145step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1690 node1690Labels := by rfl

theorem canonical1146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1146 raw1146Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw1146 raw1146Labels = mixedMoment B raw1146step0 raw1146step0Labels := by
      have ha : raw1146step0 = (fun i j => raw1146 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1146step0 raw1146; decide +kernel
      have hl : raw1146step0Labels = raw1146Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1146 raw1146Labels permutation32 permutation4
    mixedMoment B raw1146step0 raw1146step0Labels = mixedMoment B raw1146step1 raw1146step1Labels := by
      have ha : raw1146step1 = raw1146step0 := by apply Matrix.ext; unfold raw1146step1 raw1146step0; decide +kernel
      have hl : raw1146step0Labels = labelEmbedding7 ∘ raw1146step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1146step0 raw1146step0Labels raw1146step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4354 node4354Labels := by rfl

theorem canonical1147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1147 raw1147Labels = mixedMoment B node932 node932Labels := by
  calc
    mixedMoment B raw1147 raw1147Labels = mixedMoment B raw1147step0 raw1147step0Labels := by
      have ha : raw1147step0 = (fun i j => raw1147 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1147step0 raw1147; decide +kernel
      have hl : raw1147step0Labels = raw1147Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1147 raw1147Labels permutation32 permutation4
    _ = mixedMoment B node932 node932Labels := by rfl

theorem canonical1148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1148 raw1148Labels = mixedMoment B node1681 node1681Labels := by
  calc
    mixedMoment B raw1148 raw1148Labels = mixedMoment B raw1148step0 raw1148step0Labels := by
      have ha : raw1148step0 = (fun i j => raw1148 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1148step0 raw1148; decide +kernel
      have hl : raw1148step0Labels = raw1148Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1148 raw1148Labels permutation34 permutation6
    mixedMoment B raw1148step0 raw1148step0Labels = mixedMoment B raw1148step1 raw1148step1Labels := by
      have ha : raw1148step1 = -raw1148step0 := by apply Matrix.ext; change ∀ i j, raw1148step1 i j = -(raw1148step0 i j); unfold raw1148step1 raw1148step0; decide +kernel
      have hl : raw1148step1Labels = raw1148step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1148step1 raw1148step1Labels = mixedMoment B raw1148step2 raw1148step2Labels := by
      have ha : raw1148step2 = raw1148step1 := by apply Matrix.ext; unfold raw1148step2 raw1148step1; decide +kernel
      have hl : raw1148step1Labels = labelEmbedding1 ∘ raw1148step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1148step1 raw1148step1Labels raw1148step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1681 node1681Labels := by rfl

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

theorem canonical1245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1245 raw1245Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw1245 raw1245Labels = mixedMoment B raw1245step0 raw1245step0Labels := by
      have ha : raw1245step0 = (fun i j => raw1245 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1245step0 raw1245; decide +kernel
      have hl : raw1245step0Labels = raw1245Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1245 raw1245Labels permutation152 permutation4
    mixedMoment B raw1245step0 raw1245step0Labels = mixedMoment B raw1245step1 raw1245step1Labels := by
      have ha : raw1245step1 = raw1245step0 := by apply Matrix.ext; unfold raw1245step1 raw1245step0; decide +kernel
      have hl : raw1245step0Labels = labelEmbedding7 ∘ raw1245step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1245step0 raw1245step0Labels raw1245step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4451 node4451Labels := by rfl

theorem canonical1246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1246 raw1246Labels = mixedMoment B node1034 node1034Labels := by
  calc
    mixedMoment B raw1246 raw1246Labels = mixedMoment B raw1246step0 raw1246step0Labels := by
      have ha : raw1246step0 = (fun i j => raw1246 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1246step0 raw1246; decide +kernel
      have hl : raw1246step0Labels = raw1246Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1246 raw1246Labels permutation152 permutation4
    _ = mixedMoment B node1034 node1034Labels := by rfl

theorem canonical1247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1247 raw1247Labels = mixedMoment B node1644 node1644Labels := by
  calc
    mixedMoment B raw1247 raw1247Labels = mixedMoment B raw1247step0 raw1247step0Labels := by
      have ha : raw1247step0 = (fun i j => raw1247 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1247step0 raw1247; decide +kernel
      have hl : raw1247step0Labels = raw1247Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1247 raw1247Labels permutation176 permutation6
    mixedMoment B raw1247step0 raw1247step0Labels = mixedMoment B raw1247step1 raw1247step1Labels := by
      have ha : raw1247step1 = -raw1247step0 := by apply Matrix.ext; change ∀ i j, raw1247step1 i j = -(raw1247step0 i j); unfold raw1247step1 raw1247step0; decide +kernel
      have hl : raw1247step1Labels = raw1247step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1247step1 raw1247step1Labels = mixedMoment B raw1247step2 raw1247step2Labels := by
      have ha : raw1247step2 = raw1247step1 := by apply Matrix.ext; unfold raw1247step2 raw1247step1; decide +kernel
      have hl : raw1247step1Labels = labelEmbedding1 ∘ raw1247step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1247step1 raw1247step1Labels raw1247step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1644 node1644Labels := by rfl

theorem canonical1248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1248 raw1248Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw1248 raw1248Labels = mixedMoment B raw1248step0 raw1248step0Labels := by
      have ha : raw1248step0 = (fun i j => raw1248 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1248step0 raw1248; decide +kernel
      have hl : raw1248step0Labels = raw1248Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1248 raw1248Labels permutation32 permutation4
    mixedMoment B raw1248step0 raw1248step0Labels = mixedMoment B raw1248step1 raw1248step1Labels := by
      have ha : raw1248step1 = raw1248step0 := by apply Matrix.ext; unfold raw1248step1 raw1248step0; decide +kernel
      have hl : raw1248step0Labels = labelEmbedding7 ∘ raw1248step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1248step0 raw1248step0Labels raw1248step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

theorem canonical1249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1249 raw1249Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw1249 raw1249Labels = mixedMoment B raw1249step0 raw1249step0Labels := by
      have ha : raw1249step0 = (fun i j => raw1249 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1249step0 raw1249; decide +kernel
      have hl : raw1249step0Labels = raw1249Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1249 raw1249Labels permutation32 permutation4
    _ = mixedMoment B node1035 node1035Labels := by rfl

theorem canonical1250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1250 raw1250Labels = mixedMoment B node1645 node1645Labels := by
  calc
    mixedMoment B raw1250 raw1250Labels = mixedMoment B raw1250step0 raw1250step0Labels := by
      have ha : raw1250step0 = (fun i j => raw1250 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1250step0 raw1250; decide +kernel
      have hl : raw1250step0Labels = raw1250Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1250 raw1250Labels permutation38 permutation6
    mixedMoment B raw1250step0 raw1250step0Labels = mixedMoment B raw1250step1 raw1250step1Labels := by
      have ha : raw1250step1 = -raw1250step0 := by apply Matrix.ext; change ∀ i j, raw1250step1 i j = -(raw1250step0 i j); unfold raw1250step1 raw1250step0; decide +kernel
      have hl : raw1250step1Labels = raw1250step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1250step1 raw1250step1Labels = mixedMoment B raw1250step2 raw1250step2Labels := by
      have ha : raw1250step2 = raw1250step1 := by apply Matrix.ext; unfold raw1250step2 raw1250step1; decide +kernel
      have hl : raw1250step1Labels = labelEmbedding1 ∘ raw1250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1250step1 raw1250step1Labels raw1250step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1645 node1645Labels := by rfl

theorem canonical1266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1266 raw1266Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw1266 raw1266Labels = mixedMoment B raw1266step0 raw1266step0Labels := by
      have ha : raw1266step0 = (fun i j => raw1266 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1266step0 raw1266; decide +kernel
      have hl : raw1266step0Labels = raw1266Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1266 raw1266Labels permutation32 permutation4
    mixedMoment B raw1266step0 raw1266step0Labels = mixedMoment B raw1266step1 raw1266step1Labels := by
      have ha : raw1266step1 = raw1266step0 := by apply Matrix.ext; unfold raw1266step1 raw1266step0; decide +kernel
      have hl : raw1266step0Labels = labelEmbedding7 ∘ raw1266step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1266step0 raw1266step0Labels raw1266step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4461 node4461Labels := by rfl

theorem canonical1267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1267 raw1267Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw1267 raw1267Labels = mixedMoment B raw1267step0 raw1267step0Labels := by
      have ha : raw1267step0 = (fun i j => raw1267 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1267step0 raw1267; decide +kernel
      have hl : raw1267step0Labels = raw1267Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1267 raw1267Labels permutation32 permutation4
    _ = mixedMoment B node1044 node1044Labels := by rfl

theorem canonical1268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1268 raw1268Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw1268 raw1268Labels = mixedMoment B raw1268step0 raw1268step0Labels := by
      have ha : raw1268step0 = (fun i j => raw1268 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1268step0 raw1268; decide +kernel
      have hl : raw1268step0Labels = raw1268Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1268 raw1268Labels permutation50 permutation6
    mixedMoment B raw1268step0 raw1268step0Labels = mixedMoment B raw1268step1 raw1268step1Labels := by
      have ha : raw1268step1 = -raw1268step0 := by apply Matrix.ext; change ∀ i j, raw1268step1 i j = -(raw1268step0 i j); unfold raw1268step1 raw1268step0; decide +kernel
      have hl : raw1268step1Labels = raw1268step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1268step1 raw1268step1Labels = mixedMoment B raw1268step2 raw1268step2Labels := by
      have ha : raw1268step2 = raw1268step1 := by apply Matrix.ext; unfold raw1268step2 raw1268step1; decide +kernel
      have hl : raw1268step1Labels = labelEmbedding1 ∘ raw1268step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1268step1 raw1268step1Labels raw1268step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1737 node1737Labels := by rfl

theorem canonical1269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1269 raw1269Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw1269 raw1269Labels = mixedMoment B raw1269step0 raw1269step0Labels := by
      have ha : raw1269step0 = (fun i j => raw1269 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1269step0 raw1269; decide +kernel
      have hl : raw1269step0Labels = raw1269Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1269 raw1269Labels permutation8 permutation4
    mixedMoment B raw1269step0 raw1269step0Labels = mixedMoment B raw1269step1 raw1269step1Labels := by
      have ha : raw1269step1 = raw1269step0 := by apply Matrix.ext; unfold raw1269step1 raw1269step0; decide +kernel
      have hl : raw1269step0Labels = labelEmbedding7 ∘ raw1269step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1269step0 raw1269step0Labels raw1269step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

theorem canonical1270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1270 raw1270Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw1270 raw1270Labels = mixedMoment B raw1270step0 raw1270step0Labels := by
      have ha : raw1270step0 = (fun i j => raw1270 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1270step0 raw1270; decide +kernel
      have hl : raw1270step0Labels = raw1270Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1270 raw1270Labels permutation8 permutation4
    _ = mixedMoment B node1046 node1046Labels := by rfl

theorem canonical1271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1271 raw1271Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw1271 raw1271Labels = mixedMoment B raw1271step0 raw1271step0Labels := by
      have ha : raw1271step0 = (fun i j => raw1271 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1271step0 raw1271; decide +kernel
      have hl : raw1271step0Labels = raw1271Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1271 raw1271Labels permutation8 permutation6
    mixedMoment B raw1271step0 raw1271step0Labels = mixedMoment B raw1271step1 raw1271step1Labels := by
      have ha : raw1271step1 = -raw1271step0 := by apply Matrix.ext; change ∀ i j, raw1271step1 i j = -(raw1271step0 i j); unfold raw1271step1 raw1271step0; decide +kernel
      have hl : raw1271step1Labels = raw1271step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1271step1 raw1271step1Labels = mixedMoment B raw1271step2 raw1271step2Labels := by
      have ha : raw1271step2 = raw1271step1 := by apply Matrix.ext; unfold raw1271step2 raw1271step1; decide +kernel
      have hl : raw1271step1Labels = labelEmbedding1 ∘ raw1271step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1271step1 raw1271step1Labels raw1271step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1750 node1750Labels := by rfl

theorem canonical1272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1272 raw1272Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw1272 raw1272Labels = mixedMoment B raw1272step0 raw1272step0Labels := by
      have ha : raw1272step0 = (fun i j => raw1272 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1272step0 raw1272; decide +kernel
      have hl : raw1272step0Labels = raw1272Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1272 raw1272Labels permutation8 permutation4
    mixedMoment B raw1272step0 raw1272step0Labels = mixedMoment B raw1272step1 raw1272step1Labels := by
      have ha : raw1272step1 = raw1272step0 := by apply Matrix.ext; unfold raw1272step1 raw1272step0; decide +kernel
      have hl : raw1272step0Labels = labelEmbedding7 ∘ raw1272step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1272step0 raw1272step0Labels raw1272step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

theorem canonical1273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1273 raw1273Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw1273 raw1273Labels = mixedMoment B raw1273step0 raw1273step0Labels := by
      have ha : raw1273step0 = (fun i j => raw1273 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1273step0 raw1273; decide +kernel
      have hl : raw1273step0Labels = raw1273Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1273 raw1273Labels permutation8 permutation4
    _ = mixedMoment B node1049 node1049Labels := by rfl

theorem canonical1274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1274 raw1274Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw1274 raw1274Labels = mixedMoment B raw1274step0 raw1274step0Labels := by
      have ha : raw1274step0 = (fun i j => raw1274 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1274step0 raw1274; decide +kernel
      have hl : raw1274step0Labels = raw1274Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1274 raw1274Labels permutation10 permutation6
    mixedMoment B raw1274step0 raw1274step0Labels = mixedMoment B raw1274step1 raw1274step1Labels := by
      have ha : raw1274step1 = -raw1274step0 := by apply Matrix.ext; change ∀ i j, raw1274step1 i j = -(raw1274step0 i j); unfold raw1274step1 raw1274step0; decide +kernel
      have hl : raw1274step1Labels = raw1274step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1274step1 raw1274step1Labels = mixedMoment B raw1274step2 raw1274step2Labels := by
      have ha : raw1274step2 = raw1274step1 := by apply Matrix.ext; unfold raw1274step2 raw1274step1; decide +kernel
      have hl : raw1274step1Labels = labelEmbedding1 ∘ raw1274step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1274step1 raw1274step1Labels raw1274step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1738 node1738Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical239
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7671 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7671 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7671 = injectiveMoment H raw7671step0 := by
      have hz : ∀ j, raw7671 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw7671step0 = (fun i j => raw7671 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7671 permutation21 hz
    injectiveMoment H raw7671step0 = injectiveMoment H raw7671step1 := by
      have heq : raw7671step1 = (fun i j => raw7671step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7671step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical782 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw782 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw782 = injectiveMoment H raw782step0 := by
      have heq : raw782step0 = -raw782 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw782).symm
    injectiveMoment H raw782step0 = injectiveMoment H raw782step1 := by
      have heq : raw782step1 = (fun i j => raw782step0 (permutation13 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw782step0 permutation13 permutation8
    _ = injectiveMoment H node185 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical895 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw895 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw895 = injectiveMoment H raw895step0 := by
      have hz : ∀ j, raw895 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw895step0 = (fun i j => raw895 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw895 permutation15 hz
    _ = injectiveMoment H node10 := by rfl

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

theorem canonical926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw926 = injectiveMoment H node3 := by
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical187
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5990 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5990 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5990 = injectiveMoment H raw5990step0 := by
      have heq : raw5990step0 = raw5990.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5990).symm
    injectiveMoment H raw5990step0 = injectiveMoment H raw5990step1 := by
      have heq : raw5990step1 = (fun i j => raw5990step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5990step0 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

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

theorem sound56 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node56 = Sparse.eval value56 (momentVector H) := by
  have heq : pivotMatrix56 = (fun u v => node56 (pivotPermutation56 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node56 = injectiveMoment H pivotMatrix56 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix56 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix56 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix56 (0 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix56 (0 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix56 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix56 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node56 + (injectiveMoment H (mergeFirst pivotMatrix56 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix56 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value56, value10, value11, Sparse.eval] at hc ⊢
  linarith

theorem sound57 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node57 = Sparse.eval value57 (momentVector H) := by
  have heq : pivotMatrix57 = (fun u v => node57 (pivotPermutation57 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node57 = injectiveMoment H pivotMatrix57 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix57 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix57 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix57 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix57 (0 : Fin 2) = raw8215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8215 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix57 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix57 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node57 + (injectiveMoment H (mergeFirst pivotMatrix57 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix57 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value57, value10, value4, Sparse.eval] at hc ⊢
  linarith

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

theorem canonical2863 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2863 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2863 = injectiveMoment H raw2863step0 := by
      have heq : raw2863step0 = (fun i j => raw2863 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2863 permutation4 permutation5
    _ = injectiveMoment H node56 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical186
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5979 = injectiveMoment H node57 := by
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

theorem sound185 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node185 = Sparse.eval value185 (momentVector H) := by
  have heq : pivotMatrix185 = (fun u v => node185 (pivotPermutation185 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node185 = injectiveMoment H pivotMatrix185 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix185 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix185 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix185 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (0 : Fin 3) = raw5979 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix185 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (1 : Fin 3) = raw2863 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2863 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix185 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node185 + (injectiveMoment H (mergeFirst pivotMatrix185 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix185 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix185 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value185, value36, value56, value57, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node405 node405Labels = Sparse.eval singlePairValue405 (familyPairVector B) := by
  have hp := single_label_three B hB node405
  have hl : node405Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node405 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 1) = PairSemantics.raw5204 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node405 PairSemantics.raw5204; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5204 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 2) = PairSemantics.raw7671 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node405 PairSemantics.raw7671; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7671 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node405 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value185 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 4) = PairSemantics.raw782 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node405 PairSemantics.raw782; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical782 hH).trans (PairSemantics.sound185 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue405, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value185, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton2768 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2768 node2768Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node405 node405Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw272 singletonSmall2768
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2768) = raw272Labels := by decide +kernel
  rw [hl, canonical272 B hB] at h
  have hc0 : mixedMoment B raw272 (Fin.cases (0 : Fin 1) singletonSmall2768) =
      mixedMoment B node405 node405Labels := by
    have ha : raw272 = raw273 := by apply Matrix.ext; unfold raw272 raw273; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2768 = raw273Labels := by decide +kernel
    rw [ha, hj, canonical273 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton4104 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4104 node4104Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node541 node541Labels + mixedMoment B node674 node674Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw684 singletonSmall4104
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4104) = raw684Labels := by decide +kernel
  rw [hl, canonical684 B hB] at h
  have hc0 : mixedMoment B raw684 (Fin.cases (0 : Fin 2) singletonSmall4104) =
      mixedMoment B node541 node541Labels := by
    have ha : raw684 = raw685 := by apply Matrix.ext; unfold raw684 raw685; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4104 = raw685Labels := by decide +kernel
    rw [ha, hj, canonical685 B hB]
  have hc1 : mixedMoment B raw684 (Fin.cases (1 : Fin 2) singletonSmall4104) =
      mixedMoment B node674 node674Labels := by
    have ha : raw684 = raw686 := by apply Matrix.ext; unfold raw684 raw686; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4104 = raw686Labels := by decide +kernel
    rw [ha, hj, canonical686 B hB]
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

theorem singleton4106 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4106 node4106Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node543 node543Labels + mixedMoment B node675 node675Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw690 singletonSmall4106
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4106) = raw690Labels := by decide +kernel
  rw [hl, canonical690 B hB] at h
  have hc0 : mixedMoment B raw690 (Fin.cases (0 : Fin 2) singletonSmall4106) =
      mixedMoment B node543 node543Labels := by
    have ha : raw690 = raw691 := by apply Matrix.ext; unfold raw690 raw691; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4106 = raw691Labels := by decide +kernel
    rw [ha, hj, canonical691 B hB]
  have hc1 : mixedMoment B raw690 (Fin.cases (1 : Fin 2) singletonSmall4106) =
      mixedMoment B node675 node675Labels := by
    have ha : raw690 = raw692 := by apply Matrix.ext; unfold raw690 raw692; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4106 = raw692Labels := by decide +kernel
    rw [ha, hj, canonical692 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4126 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4126 node4126Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node557 node557Labels + mixedMoment B node677 node677Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw732 singletonSmall4126
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4126) = raw732Labels := by decide +kernel
  rw [hl, canonical732 B hB] at h
  have hc0 : mixedMoment B raw732 (Fin.cases (0 : Fin 2) singletonSmall4126) =
      mixedMoment B node557 node557Labels := by
    have ha : raw732 = raw733 := by apply Matrix.ext; unfold raw732 raw733; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4126 = raw733Labels := by decide +kernel
    rw [ha, hj, canonical733 B hB]
  have hc1 : mixedMoment B raw732 (Fin.cases (1 : Fin 2) singletonSmall4126) =
      mixedMoment B node677 node677Labels := by
    have ha : raw732 = raw734 := by apply Matrix.ext; unfold raw732 raw734; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4126 = raw734Labels := by decide +kernel
    rw [ha, hj, canonical734 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton4290 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4290 node4290Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node868 node868Labels + mixedMoment B node1566 node1566Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1032 singletonSmall4290
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4290) = raw1032Labels := by decide +kernel
  rw [hl, canonical1032 B hB] at h
  have hc0 : mixedMoment B raw1032 (Fin.cases (0 : Fin 2) singletonSmall4290) =
      mixedMoment B node868 node868Labels := by
    have ha : raw1032 = raw1033 := by apply Matrix.ext; unfold raw1032 raw1033; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4290 = raw1033Labels := by decide +kernel
    rw [ha, hj, canonical1033 B hB]
  have hc1 : mixedMoment B raw1032 (Fin.cases (1 : Fin 2) singletonSmall4290) =
      mixedMoment B node1566 node1566Labels := by
    have ha : raw1032 = raw1034 := by apply Matrix.ext; unfold raw1032 raw1034; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4290 = raw1034Labels := by decide +kernel
    rw [ha, hj, canonical1034 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4291 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4291 node4291Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node869 node869Labels + mixedMoment B node1561 node1561Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1035 singletonSmall4291
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4291) = raw1035Labels := by decide +kernel
  rw [hl, canonical1035 B hB] at h
  have hc0 : mixedMoment B raw1035 (Fin.cases (0 : Fin 2) singletonSmall4291) =
      mixedMoment B node869 node869Labels := by
    have ha : raw1035 = raw1036 := by apply Matrix.ext; unfold raw1035 raw1036; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4291 = raw1036Labels := by decide +kernel
    rw [ha, hj, canonical1036 B hB]
  have hc1 : mixedMoment B raw1035 (Fin.cases (1 : Fin 2) singletonSmall4291) =
      mixedMoment B node1561 node1561Labels := by
    have ha : raw1035 = raw1037 := by apply Matrix.ext; unfold raw1035 raw1037; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4291 = raw1037Labels := by decide +kernel
    rw [ha, hj, canonical1037 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4307 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4307 node4307Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node885 node885Labels + mixedMoment B node1563 node1563Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1071 singletonSmall4307
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4307) = raw1071Labels := by decide +kernel
  rw [hl, canonical1071 B hB] at h
  have hc0 : mixedMoment B raw1071 (Fin.cases (0 : Fin 2) singletonSmall4307) =
      mixedMoment B node885 node885Labels := by
    have ha : raw1071 = raw1072 := by apply Matrix.ext; unfold raw1071 raw1072; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4307 = raw1072Labels := by decide +kernel
    rw [ha, hj, canonical1072 B hB]
  have hc1 : mixedMoment B raw1071 (Fin.cases (1 : Fin 2) singletonSmall4307) =
      mixedMoment B node1563 node1563Labels := by
    have ha : raw1071 = raw1073 := by apply Matrix.ext; unfold raw1071 raw1073; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4307 = raw1073Labels := by decide +kernel
    rw [ha, hj, canonical1073 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4351 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4351 node4351Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node929 node929Labels + mixedMoment B node1680 node1680Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1140 singletonSmall4351
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4351) = raw1140Labels := by decide +kernel
  rw [hl, canonical1140 B hB] at h
  have hc0 : mixedMoment B raw1140 (Fin.cases (0 : Fin 2) singletonSmall4351) =
      mixedMoment B node929 node929Labels := by
    have ha : raw1140 = raw1141 := by apply Matrix.ext; unfold raw1140 raw1141; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4351 = raw1141Labels := by decide +kernel
    rw [ha, hj, canonical1141 B hB]
  have hc1 : mixedMoment B raw1140 (Fin.cases (1 : Fin 2) singletonSmall4351) =
      mixedMoment B node1680 node1680Labels := by
    have ha : raw1140 = raw1142 := by apply Matrix.ext; unfold raw1140 raw1142; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4351 = raw1142Labels := by decide +kernel
    rw [ha, hj, canonical1142 B hB]
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

theorem singleton4352 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4352 node4352Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node930 node930Labels + mixedMoment B node1690 node1690Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1143 singletonSmall4352
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4352) = raw1143Labels := by decide +kernel
  rw [hl, canonical1143 B hB] at h
  have hc0 : mixedMoment B raw1143 (Fin.cases (0 : Fin 2) singletonSmall4352) =
      mixedMoment B node930 node930Labels := by
    have ha : raw1143 = raw1144 := by apply Matrix.ext; unfold raw1143 raw1144; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4352 = raw1144Labels := by decide +kernel
    rw [ha, hj, canonical1144 B hB]
  have hc1 : mixedMoment B raw1143 (Fin.cases (1 : Fin 2) singletonSmall4352) =
      mixedMoment B node1690 node1690Labels := by
    have ha : raw1143 = raw1145 := by apply Matrix.ext; unfold raw1143 raw1145; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4352 = raw1145Labels := by decide +kernel
    rw [ha, hj, canonical1145 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4354 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4354 node4354Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node932 node932Labels + mixedMoment B node1681 node1681Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1146 singletonSmall4354
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4354) = raw1146Labels := by decide +kernel
  rw [hl, canonical1146 B hB] at h
  have hc0 : mixedMoment B raw1146 (Fin.cases (0 : Fin 2) singletonSmall4354) =
      mixedMoment B node932 node932Labels := by
    have ha : raw1146 = raw1147 := by apply Matrix.ext; unfold raw1146 raw1147; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4354 = raw1147Labels := by decide +kernel
    rw [ha, hj, canonical1147 B hB]
  have hc1 : mixedMoment B raw1146 (Fin.cases (1 : Fin 2) singletonSmall4354) =
      mixedMoment B node1681 node1681Labels := by
    have ha : raw1146 = raw1148 := by apply Matrix.ext; unfold raw1146 raw1148; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4354 = raw1148Labels := by decide +kernel
    rw [ha, hj, canonical1148 B hB]
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

theorem singleton4451 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4451 node4451Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1034 node1034Labels + mixedMoment B node1644 node1644Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1245 singletonSmall4451
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4451) = raw1245Labels := by decide +kernel
  rw [hl, canonical1245 B hB] at h
  have hc0 : mixedMoment B raw1245 (Fin.cases (0 : Fin 2) singletonSmall4451) =
      mixedMoment B node1034 node1034Labels := by
    have ha : raw1245 = raw1246 := by apply Matrix.ext; unfold raw1245 raw1246; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4451 = raw1246Labels := by decide +kernel
    rw [ha, hj, canonical1246 B hB]
  have hc1 : mixedMoment B raw1245 (Fin.cases (1 : Fin 2) singletonSmall4451) =
      mixedMoment B node1644 node1644Labels := by
    have ha : raw1245 = raw1247 := by apply Matrix.ext; unfold raw1245 raw1247; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4451 = raw1247Labels := by decide +kernel
    rw [ha, hj, canonical1247 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4452 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4452 node4452Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1035 node1035Labels + mixedMoment B node1645 node1645Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1248 singletonSmall4452
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4452) = raw1248Labels := by decide +kernel
  rw [hl, canonical1248 B hB] at h
  have hc0 : mixedMoment B raw1248 (Fin.cases (0 : Fin 2) singletonSmall4452) =
      mixedMoment B node1035 node1035Labels := by
    have ha : raw1248 = raw1249 := by apply Matrix.ext; unfold raw1248 raw1249; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4452 = raw1249Labels := by decide +kernel
    rw [ha, hj, canonical1249 B hB]
  have hc1 : mixedMoment B raw1248 (Fin.cases (1 : Fin 2) singletonSmall4452) =
      mixedMoment B node1645 node1645Labels := by
    have ha : raw1248 = raw1250 := by apply Matrix.ext; unfold raw1248 raw1250; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4452 = raw1250Labels := by decide +kernel
    rw [ha, hj, canonical1250 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4461 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4461 node4461Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1044 node1044Labels + mixedMoment B node1737 node1737Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1266 singletonSmall4461
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4461) = raw1266Labels := by decide +kernel
  rw [hl, canonical1266 B hB] at h
  have hc0 : mixedMoment B raw1266 (Fin.cases (0 : Fin 2) singletonSmall4461) =
      mixedMoment B node1044 node1044Labels := by
    have ha : raw1266 = raw1267 := by apply Matrix.ext; unfold raw1266 raw1267; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4461 = raw1267Labels := by decide +kernel
    rw [ha, hj, canonical1267 B hB]
  have hc1 : mixedMoment B raw1266 (Fin.cases (1 : Fin 2) singletonSmall4461) =
      mixedMoment B node1737 node1737Labels := by
    have ha : raw1266 = raw1268 := by apply Matrix.ext; unfold raw1266 raw1268; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4461 = raw1268Labels := by decide +kernel
    rw [ha, hj, canonical1268 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4463 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4463 node4463Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1046 node1046Labels + mixedMoment B node1750 node1750Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1269 singletonSmall4463
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4463) = raw1269Labels := by decide +kernel
  rw [hl, canonical1269 B hB] at h
  have hc0 : mixedMoment B raw1269 (Fin.cases (0 : Fin 2) singletonSmall4463) =
      mixedMoment B node1046 node1046Labels := by
    have ha : raw1269 = raw1270 := by apply Matrix.ext; unfold raw1269 raw1270; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4463 = raw1270Labels := by decide +kernel
    rw [ha, hj, canonical1270 B hB]
  have hc1 : mixedMoment B raw1269 (Fin.cases (1 : Fin 2) singletonSmall4463) =
      mixedMoment B node1750 node1750Labels := by
    have ha : raw1269 = raw1271 := by apply Matrix.ext; unfold raw1269 raw1271; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4463 = raw1271Labels := by decide +kernel
    rw [ha, hj, canonical1271 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4466 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4466 node4466Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1049 node1049Labels + mixedMoment B node1738 node1738Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1272 singletonSmall4466
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4466) = raw1272Labels := by decide +kernel
  rw [hl, canonical1272 B hB] at h
  have hc0 : mixedMoment B raw1272 (Fin.cases (0 : Fin 2) singletonSmall4466) =
      mixedMoment B node1049 node1049Labels := by
    have ha : raw1272 = raw1273 := by apply Matrix.ext; unfold raw1272 raw1273; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4466 = raw1273Labels := by decide +kernel
    rw [ha, hj, canonical1273 B hB]
  have hc1 : mixedMoment B raw1272 (Fin.cases (1 : Fin 2) singletonSmall4466) =
      mixedMoment B node1738 node1738Labels := by
    have ha : raw1272 = raw1274 := by apply Matrix.ext; unfold raw1272 raw1274; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4466 = raw1274Labels := by decide +kernel
    rw [ha, hj, canonical1274 B hB]
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

theorem singleton4503 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4503 node4503Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1087 node1087Labels + mixedMoment B node1739 node1739Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1302 singletonSmall4503
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4503) = raw1302Labels := by decide +kernel
  rw [hl, canonical1302 B hB] at h
  have hc0 : mixedMoment B raw1302 (Fin.cases (0 : Fin 2) singletonSmall4503) =
      mixedMoment B node1087 node1087Labels := by
    have ha : raw1302 = raw1303 := by apply Matrix.ext; unfold raw1302 raw1303; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4503 = raw1303Labels := by decide +kernel
    rw [ha, hj, canonical1303 B hB]
  have hc1 : mixedMoment B raw1302 (Fin.cases (1 : Fin 2) singletonSmall4503) =
      mixedMoment B node1739 node1739Labels := by
    have ha : raw1302 = raw1304 := by apply Matrix.ext; unfold raw1302 raw1304; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4503 = raw1304Labels := by decide +kernel
    rw [ha, hj, canonical1304 B hB]
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

theorem singleton5076 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5076 node5076Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2483 node2483Labels + mixedMoment B node3477 node3477Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2100 singletonSmall5076
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5076) = raw2100Labels := by decide +kernel
  rw [hl, canonical2100 B hB] at h
  have hc0 : mixedMoment B raw2100 (Fin.cases (0 : Fin 2) singletonSmall5076) =
      mixedMoment B node2483 node2483Labels := by
    have ha : raw2100 = raw2101 := by apply Matrix.ext; unfold raw2100 raw2101; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5076 = raw2101Labels := by decide +kernel
    rw [ha, hj, canonical2101 B hB]
  have hc1 : mixedMoment B raw2100 (Fin.cases (1 : Fin 2) singletonSmall5076) =
      mixedMoment B node3477 node3477Labels := by
    have ha : raw2100 = raw2102 := by apply Matrix.ext; unfold raw2100 raw2102; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5076 = raw2102Labels := by decide +kernel
    rw [ha, hj, canonical2102 B hB]
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

theorem singleton5290 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5290 node5290Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2764 node2764Labels + mixedMoment B node3581 node3581Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2292 singletonSmall5290
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5290) = raw2292Labels := by decide +kernel
  rw [hl, canonical2292 B hB] at h
  have hc0 : mixedMoment B raw2292 (Fin.cases (0 : Fin 2) singletonSmall5290) =
      mixedMoment B node2764 node2764Labels := by
    have ha : raw2292 = raw2293 := by apply Matrix.ext; unfold raw2292 raw2293; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5290 = raw2293Labels := by decide +kernel
    rw [ha, hj, canonical2293 B hB]
  have hc1 : mixedMoment B raw2292 (Fin.cases (1 : Fin 2) singletonSmall5290) =
      mixedMoment B node3581 node3581Labels := by
    have ha : raw2292 = raw2294 := by apply Matrix.ext; unfold raw2292 raw2294; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5290 = raw2294Labels := by decide +kernel
    rw [ha, hj, canonical2294 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5294 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5294 node5294Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2768 node2768Labels + mixedMoment B node3632 node3632Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2304 singletonSmall5294
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5294) = raw2304Labels := by decide +kernel
  rw [hl, canonical2304 B hB] at h
  have hc0 : mixedMoment B raw2304 (Fin.cases (0 : Fin 2) singletonSmall5294) =
      mixedMoment B node2768 node2768Labels := by
    have ha : raw2304 = raw2305 := by apply Matrix.ext; unfold raw2304 raw2305; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5294 = raw2305Labels := by decide +kernel
    rw [ha, hj, canonical2305 B hB]
  have hc1 : mixedMoment B raw2304 (Fin.cases (1 : Fin 2) singletonSmall5294) =
      mixedMoment B node3632 node3632Labels := by
    have ha : raw2304 = raw2306 := by apply Matrix.ext; unfold raw2304 raw2306; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5294 = raw2306Labels := by decide +kernel
    rw [ha, hj, canonical2306 B hB]
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

theorem sound674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node674 node674Labels = Sparse.eval nodeValue674 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 674) = mixedMoment B node674 node674Labels := rfl
  simpa [nodeValue674, Sparse.eval] using hc.symm

theorem sound675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node675 node675Labels = Sparse.eval nodeValue675 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 675) = mixedMoment B node675 node675Labels := rfl
  simpa [nodeValue675, Sparse.eval] using hc.symm

theorem sound677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node677 node677Labels = Sparse.eval nodeValue677 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 677) = mixedMoment B node677 node677Labels := rfl
  simpa [nodeValue677, Sparse.eval] using hc.symm

theorem sound681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node681 node681Labels = Sparse.eval nodeValue681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 681) = mixedMoment B node681 node681Labels := rfl
  simpa [nodeValue681, Sparse.eval] using hc.symm

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

theorem sound868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node868 node868Labels = Sparse.eval nodeValue868 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 868) = mixedMoment B node868 node868Labels := rfl
  simpa [nodeValue868, Sparse.eval] using hc.symm

theorem sound869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node869 node869Labels = Sparse.eval nodeValue869 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 869) = mixedMoment B node869 node869Labels := rfl
  simpa [nodeValue869, Sparse.eval] using hc.symm

theorem sound885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node885 node885Labels = Sparse.eval nodeValue885 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 885) = mixedMoment B node885 node885Labels := rfl
  simpa [nodeValue885, Sparse.eval] using hc.symm

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

theorem sound929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node929 node929Labels = Sparse.eval nodeValue929 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 929) = mixedMoment B node929 node929Labels := rfl
  simpa [nodeValue929, Sparse.eval] using hc.symm

theorem sound930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node930 node930Labels = Sparse.eval nodeValue930 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 930) = mixedMoment B node930 node930Labels := rfl
  simpa [nodeValue930, Sparse.eval] using hc.symm

theorem sound932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node932 node932Labels = Sparse.eval nodeValue932 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 932) = mixedMoment B node932 node932Labels := rfl
  simpa [nodeValue932, Sparse.eval] using hc.symm

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

theorem sound1034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1034 node1034Labels = Sparse.eval nodeValue1034 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1034) = mixedMoment B node1034 node1034Labels := rfl
  simpa [nodeValue1034, Sparse.eval] using hc.symm

theorem sound1035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1035 node1035Labels = Sparse.eval nodeValue1035 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1035) = mixedMoment B node1035 node1035Labels := rfl
  simpa [nodeValue1035, Sparse.eval] using hc.symm

theorem sound1044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1044 node1044Labels = Sparse.eval nodeValue1044 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1044) = mixedMoment B node1044 node1044Labels := rfl
  simpa [nodeValue1044, Sparse.eval] using hc.symm

theorem sound1046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1046 node1046Labels = Sparse.eval nodeValue1046 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1046) = mixedMoment B node1046 node1046Labels := rfl
  simpa [nodeValue1046, Sparse.eval] using hc.symm

theorem sound1049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1049 node1049Labels = Sparse.eval nodeValue1049 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1049) = mixedMoment B node1049 node1049Labels := rfl
  simpa [nodeValue1049, Sparse.eval] using hc.symm

theorem sound1073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1073 node1073Labels = Sparse.eval nodeValue1073 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1073) = mixedMoment B node1073 node1073Labels := rfl
  simpa [nodeValue1073, Sparse.eval] using hc.symm

theorem sound1087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1087 node1087Labels = Sparse.eval nodeValue1087 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1087) = mixedMoment B node1087 node1087Labels := rfl
  simpa [nodeValue1087, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1561 node1561Labels = Sparse.eval nodeValue1561 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1561) = mixedMoment B node1561 node1561Labels := rfl
  simpa [nodeValue1561, Sparse.eval] using hc.symm

theorem sound1563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1563 node1563Labels = Sparse.eval nodeValue1563 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1563) = mixedMoment B node1563 node1563Labels := rfl
  simpa [nodeValue1563, Sparse.eval] using hc.symm

theorem sound1566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1566 node1566Labels = Sparse.eval nodeValue1566 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1566) = mixedMoment B node1566 node1566Labels := rfl
  simpa [nodeValue1566, Sparse.eval] using hc.symm

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

theorem sound1644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1644 node1644Labels = Sparse.eval nodeValue1644 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1644) = mixedMoment B node1644 node1644Labels := rfl
  simpa [nodeValue1644, Sparse.eval] using hc.symm

theorem sound1645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1645 node1645Labels = Sparse.eval nodeValue1645 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1645) = mixedMoment B node1645 node1645Labels := rfl
  simpa [nodeValue1645, Sparse.eval] using hc.symm

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

theorem sound1680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1680 node1680Labels = Sparse.eval nodeValue1680 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1680) = mixedMoment B node1680 node1680Labels := rfl
  simpa [nodeValue1680, Sparse.eval] using hc.symm

theorem sound1681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1681 node1681Labels = Sparse.eval nodeValue1681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1681) = mixedMoment B node1681 node1681Labels := rfl
  simpa [nodeValue1681, Sparse.eval] using hc.symm

theorem sound1690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1690 node1690Labels = Sparse.eval nodeValue1690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1690) = mixedMoment B node1690 node1690Labels := rfl
  simpa [nodeValue1690, Sparse.eval] using hc.symm

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

theorem sound1737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1737 node1737Labels = Sparse.eval nodeValue1737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1737) = mixedMoment B node1737 node1737Labels := rfl
  simpa [nodeValue1737, Sparse.eval] using hc.symm

theorem sound1738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1738 node1738Labels = Sparse.eval nodeValue1738 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1738) = mixedMoment B node1738 node1738Labels := rfl
  simpa [nodeValue1738, Sparse.eval] using hc.symm

theorem sound1739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1739 node1739Labels = Sparse.eval nodeValue1739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1739) = mixedMoment B node1739 node1739Labels := rfl
  simpa [nodeValue1739, Sparse.eval] using hc.symm

theorem sound1750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1750 node1750Labels = Sparse.eval nodeValue1750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1750) = mixedMoment B node1750 node1750Labels := rfl
  simpa [nodeValue1750, Sparse.eval] using hc.symm

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

theorem sound2483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2483 node2483Labels = Sparse.eval nodeValue2483 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2483) = mixedMoment B node2483 node2483Labels := rfl
  simpa [nodeValue2483, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node405 node405Labels = Sparse.eval nodeValue405 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue405 (familyPairVector B) := singlePair405 B _hB
    _ = _ := by
      norm_num [singlePairValue405, nodeValue405, Sparse.eval, mixedVector]
      ring

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

theorem sound2764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2764 node2764Labels = Sparse.eval nodeValue2764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2764) = mixedMoment B node2764 node2764Labels := rfl
  simpa [nodeValue2764, Sparse.eval] using hc.symm

theorem sound2768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2768 node2768Labels = Sparse.eval nodeValue2768 (mixedVector B) := by
  have h := singleton2768 B _hB
  rw [sound405 B _hB _hF] at h
  norm_num [nodeValue2768, nodeValue405, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound3477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3477 node3477Labels = Sparse.eval nodeValue3477 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3477) = mixedMoment B node3477 node3477Labels := rfl
  simpa [nodeValue3477, Sparse.eval] using hc.symm

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

theorem sound3581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3581 node3581Labels = Sparse.eval nodeValue3581 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3581) = mixedMoment B node3581 node3581Labels := rfl
  simpa [nodeValue3581, Sparse.eval] using hc.symm

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

theorem sound3632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3632 node3632Labels = Sparse.eval nodeValue3632 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3632) = mixedMoment B node3632 node3632Labels := rfl
  simpa [nodeValue3632, Sparse.eval] using hc.symm

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

theorem sound541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node541 node541Labels = Sparse.eval nodeValue541 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 541) = mixedMoment B node541 node541Labels := rfl
  simpa [nodeValue541, Sparse.eval] using hc.symm

theorem sound542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node542 node542Labels = Sparse.eval nodeValue542 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 542) = mixedMoment B node542 node542Labels := rfl
  simpa [nodeValue542, Sparse.eval] using hc.symm

theorem sound543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node543 node543Labels = Sparse.eval nodeValue543 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 543) = mixedMoment B node543 node543Labels := rfl
  simpa [nodeValue543, Sparse.eval] using hc.symm

theorem sound557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node557 node557Labels = Sparse.eval nodeValue557 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 557) = mixedMoment B node557 node557Labels := rfl
  simpa [nodeValue557, Sparse.eval] using hc.symm

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

theorem sound4104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4104 node4104Labels = Sparse.eval nodeValue4104 (mixedVector B) := by
  have h := singleton4104 B _hB
  rw [sound541 B _hB _hF, sound674 B _hB _hF] at h
  norm_num [nodeValue4104, nodeValue541, nodeValue674, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4105 node4105Labels = Sparse.eval nodeValue4105 (mixedVector B) := by
  have h := singleton4105 B _hB
  rw [sound542 B _hB _hF, sound681 B _hB _hF] at h
  norm_num [nodeValue4105, nodeValue542, nodeValue681, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4106 node4106Labels = Sparse.eval nodeValue4106 (mixedVector B) := by
  have h := singleton4106 B _hB
  rw [sound543 B _hB _hF, sound675 B _hB _hF] at h
  norm_num [nodeValue4106, nodeValue543, nodeValue675, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4126 node4126Labels = Sparse.eval nodeValue4126 (mixedVector B) := by
  have h := singleton4126 B _hB
  rw [sound557 B _hB _hF, sound677 B _hB _hF] at h
  norm_num [nodeValue4126, nodeValue557, nodeValue677, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4290 node4290Labels = Sparse.eval nodeValue4290 (mixedVector B) := by
  have h := singleton4290 B _hB
  rw [sound868 B _hB _hF, sound1566 B _hB _hF] at h
  norm_num [nodeValue4290, nodeValue868, nodeValue1566, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4291 node4291Labels = Sparse.eval nodeValue4291 (mixedVector B) := by
  have h := singleton4291 B _hB
  rw [sound869 B _hB _hF, sound1561 B _hB _hF] at h
  norm_num [nodeValue4291, nodeValue869, nodeValue1561, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4307 node4307Labels = Sparse.eval nodeValue4307 (mixedVector B) := by
  have h := singleton4307 B _hB
  rw [sound885 B _hB _hF, sound1563 B _hB _hF] at h
  norm_num [nodeValue4307, nodeValue885, nodeValue1563, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4351 node4351Labels = Sparse.eval nodeValue4351 (mixedVector B) := by
  have h := singleton4351 B _hB
  rw [sound929 B _hB _hF, sound1680 B _hB _hF] at h
  norm_num [nodeValue4351, nodeValue929, nodeValue1680, Sparse.eval] at h ⊢
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

theorem sound4352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4352 node4352Labels = Sparse.eval nodeValue4352 (mixedVector B) := by
  have h := singleton4352 B _hB
  rw [sound930 B _hB _hF, sound1690 B _hB _hF] at h
  norm_num [nodeValue4352, nodeValue930, nodeValue1690, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4354 node4354Labels = Sparse.eval nodeValue4354 (mixedVector B) := by
  have h := singleton4354 B _hB
  rw [sound932 B _hB _hF, sound1681 B _hB _hF] at h
  norm_num [nodeValue4354, nodeValue932, nodeValue1681, Sparse.eval] at h ⊢
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

theorem sound4451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4451 node4451Labels = Sparse.eval nodeValue4451 (mixedVector B) := by
  have h := singleton4451 B _hB
  rw [sound1034 B _hB _hF, sound1644 B _hB _hF] at h
  norm_num [nodeValue4451, nodeValue1034, nodeValue1644, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4452 node4452Labels = Sparse.eval nodeValue4452 (mixedVector B) := by
  have h := singleton4452 B _hB
  rw [sound1035 B _hB _hF, sound1645 B _hB _hF] at h
  norm_num [nodeValue4452, nodeValue1035, nodeValue1645, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4461 node4461Labels = Sparse.eval nodeValue4461 (mixedVector B) := by
  have h := singleton4461 B _hB
  rw [sound1044 B _hB _hF, sound1737 B _hB _hF] at h
  norm_num [nodeValue4461, nodeValue1044, nodeValue1737, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4463 node4463Labels = Sparse.eval nodeValue4463 (mixedVector B) := by
  have h := singleton4463 B _hB
  rw [sound1046 B _hB _hF, sound1750 B _hB _hF] at h
  norm_num [nodeValue4463, nodeValue1046, nodeValue1750, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4466 node4466Labels = Sparse.eval nodeValue4466 (mixedVector B) := by
  have h := singleton4466 B _hB
  rw [sound1049 B _hB _hF, sound1738 B _hB _hF] at h
  norm_num [nodeValue4466, nodeValue1049, nodeValue1738, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4503 node4503Labels = Sparse.eval nodeValue4503 (mixedVector B) := by
  have h := singleton4503 B _hB
  rw [sound1087 B _hB _hF, sound1739 B _hB _hF] at h
  norm_num [nodeValue4503, nodeValue1087, nodeValue1739, Sparse.eval] at h ⊢
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

theorem sound5076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5076 node5076Labels = Sparse.eval nodeValue5076 (mixedVector B) := by
  have h := singleton5076 B _hB
  rw [sound2483 B _hB _hF, sound3477 B _hB _hF] at h
  norm_num [nodeValue5076, nodeValue2483, nodeValue3477, Sparse.eval] at h ⊢
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

theorem sound5290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5290 node5290Labels = Sparse.eval nodeValue5290 (mixedVector B) := by
  have h := singleton5290 B _hB
  rw [sound2764 B _hB _hF, sound3581 B _hB _hF] at h
  norm_num [nodeValue5290, nodeValue2764, nodeValue3581, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5294 node5294Labels = Sparse.eval nodeValue5294 (mixedVector B) := by
  have h := singleton5294 B _hB
  rw [sound2768 B _hB _hF, sound3632 B _hB _hF] at h
  norm_num [nodeValue5294, nodeValue2768, nodeValue3632, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources53
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1720 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1720 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1720 + difference 0 1) (sourceB1720 + difference 1 0) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA1720 + difference 0 1) (sourceB1720 + difference 1 0) sourceC1720) = raw13592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw13592; decide +kernel
    rw [ha]
    exact (canonical13592 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1720 + difference 0 2) (sourceB1720 + difference 2 0) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA1720 + difference 0 2) (sourceB1720 + difference 2 0) sourceC1720) = raw13593 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw13593; decide +kernel
    rw [ha]
    exact (canonical13593 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1720 + difference 0 3) (sourceB1720 + difference 3 0) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA1720 + difference 0 3) (sourceB1720 + difference 3 0) sourceC1720) = raw3054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw3054; decide +kernel
    rw [ha]
    exact (canonical3054 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1720 + difference 0 4) (sourceB1720 + difference 4 0) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA1720 + difference 0 4) (sourceB1720 + difference 4 0) sourceC1720) = raw13594 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw13594; decide +kernel
    rw [ha]
    exact (canonical13594 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1720 + difference 0 5) (sourceB1720 + difference 5 0) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA1720 + difference 0 5) (sourceB1720 + difference 5 0) sourceC1720) = raw3044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw3044; decide +kernel
    rw [ha]
    exact (canonical3044 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1720 + difference 1 0) (sourceB1720 + difference 0 1) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4126) := by
    have ha : (tripleCharges (sourceA1720 + difference 1 0) (sourceB1720 + difference 0 1) sourceC1720) = raw25067 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw25067; decide +kernel
    rw [ha]
    exact (canonical25067 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1720 + difference 1 2) (sourceB1720 + difference 2 1) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4307) := by
    have ha : (tripleCharges (sourceA1720 + difference 1 2) (sourceB1720 + difference 2 1) sourceC1720) = raw25068 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw25068; decide +kernel
    rw [ha]
    exact (canonical25068 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1720 + difference 1 3) (sourceB1720 + difference 3 1) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1720 + difference 1 3) (sourceB1720 + difference 3 1) sourceC1720) = raw21243 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw21243; decide +kernel
    rw [ha]
    exact (canonical21243 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1720 + difference 1 4) (sourceB1720 + difference 4 1) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1720 + difference 1 4) (sourceB1720 + difference 4 1) sourceC1720) = raw25069 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw25069; decide +kernel
    rw [ha]
    exact (canonical25069 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1720 + difference 1 5) (sourceB1720 + difference 5 1) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4489) := by
    have ha : (tripleCharges (sourceA1720 + difference 1 5) (sourceB1720 + difference 5 1) sourceC1720) = raw13574 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw13574; decide +kernel
    rw [ha]
    exact (canonical13574 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1720 + difference 2 0) (sourceB1720 + difference 0 2) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4104) := by
    have ha : (tripleCharges (sourceA1720 + difference 2 0) (sourceB1720 + difference 0 2) sourceC1720) = raw25070 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw25070; decide +kernel
    rw [ha]
    exact (canonical25070 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1720 + difference 2 1) (sourceB1720 + difference 1 2) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4351) := by
    have ha : (tripleCharges (sourceA1720 + difference 2 1) (sourceB1720 + difference 1 2) sourceC1720) = raw25071 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw25071; decide +kernel
    rw [ha]
    exact (canonical25071 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1720 + difference 2 3) (sourceB1720 + difference 3 2) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1720 + difference 2 3) (sourceB1720 + difference 3 2) sourceC1720) = raw21248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw21248; decide +kernel
    rw [ha]
    exact (canonical21248 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1720 + difference 2 4) (sourceB1720 + difference 4 2) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1720 + difference 2 4) (sourceB1720 + difference 4 2) sourceC1720) = raw25072 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw25072; decide +kernel
    rw [ha]
    exact (canonical25072 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1720 + difference 2 5) (sourceB1720 + difference 5 2) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4451) := by
    have ha : (tripleCharges (sourceA1720 + difference 2 5) (sourceB1720 + difference 5 2) sourceC1720) = raw13578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw13578; decide +kernel
    rw [ha]
    exact (canonical13578 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1720 + difference 3 0) (sourceB1720 + difference 0 3) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4106) := by
    have ha : (tripleCharges (sourceA1720 + difference 3 0) (sourceB1720 + difference 0 3) sourceC1720) = raw25073 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw25073; decide +kernel
    rw [ha]
    exact (canonical25073 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1720 + difference 3 1) (sourceB1720 + difference 1 3) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA1720 + difference 3 1) (sourceB1720 + difference 1 3) sourceC1720) = raw25074 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw25074; decide +kernel
    rw [ha]
    exact (canonical25074 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1720 + difference 3 2) (sourceB1720 + difference 2 3) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4291) := by
    have ha : (tripleCharges (sourceA1720 + difference 3 2) (sourceB1720 + difference 2 3) sourceC1720) = raw25075 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw25075; decide +kernel
    rw [ha]
    exact (canonical25075 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1720 + difference 3 4) (sourceB1720 + difference 4 3) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1720 + difference 3 4) (sourceB1720 + difference 4 3) sourceC1720) = raw25076 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw25076; decide +kernel
    rw [ha]
    exact (canonical25076 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1720 + difference 3 5) (sourceB1720 + difference 5 3) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA1720 + difference 3 5) (sourceB1720 + difference 5 3) sourceC1720) = raw13582 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw13582; decide +kernel
    rw [ha]
    exact (canonical13582 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1720 + difference 4 0) (sourceB1720 + difference 0 4) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4106) := by
    have ha : (tripleCharges (sourceA1720 + difference 4 0) (sourceB1720 + difference 0 4) sourceC1720) = raw23046 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw23046; decide +kernel
    rw [ha]
    exact (canonical23046 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1720 + difference 4 1) (sourceB1720 + difference 1 4) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA1720 + difference 4 1) (sourceB1720 + difference 1 4) sourceC1720) = raw23047 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw23047; decide +kernel
    rw [ha]
    exact (canonical23047 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1720 + difference 4 2) (sourceB1720 + difference 2 4) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4291) := by
    have ha : (tripleCharges (sourceA1720 + difference 4 2) (sourceB1720 + difference 2 4) sourceC1720) = raw23048 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw23048; decide +kernel
    rw [ha]
    exact (canonical23048 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1720 + difference 4 3) (sourceB1720 + difference 3 4) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1720 + difference 4 3) (sourceB1720 + difference 3 4) sourceC1720) = raw21257 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw21257; decide +kernel
    rw [ha]
    exact (canonical21257 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1720 + difference 4 5) (sourceB1720 + difference 5 4) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA1720 + difference 4 5) (sourceB1720 + difference 5 4) sourceC1720) = raw13587 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw13587; decide +kernel
    rw [ha]
    exact (canonical13587 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1720 + difference 5 0) (sourceB1720 + difference 0 5) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4105) := by
    have ha : (tripleCharges (sourceA1720 + difference 5 0) (sourceB1720 + difference 0 5) sourceC1720) = raw21249 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw21249; decide +kernel
    rw [ha]
    exact (canonical21249 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1720 + difference 5 1) (sourceB1720 + difference 1 5) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4352) := by
    have ha : (tripleCharges (sourceA1720 + difference 5 1) (sourceB1720 + difference 1 5) sourceC1720) = raw21250 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw21250; decide +kernel
    rw [ha]
    exact (canonical21250 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1720 + difference 5 2) (sourceB1720 + difference 2 5) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4290) := by
    have ha : (tripleCharges (sourceA1720 + difference 5 2) (sourceB1720 + difference 2 5) sourceC1720) = raw21251 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw21251; decide +kernel
    rw [ha]
    exact (canonical21251 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1720 + difference 5 3) (sourceB1720 + difference 3 5) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1720 + difference 5 3) (sourceB1720 + difference 3 5) sourceC1720) = raw23054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw23054; decide +kernel
    rw [ha]
    exact (canonical23054 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1720 + difference 5 4) (sourceB1720 + difference 4 5) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1720 + difference 5 4) (sourceB1720 + difference 4 5) sourceC1720) = raw21252 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw21252; decide +kernel
    rw [ha]
    exact (canonical21252 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1720 sourceB1720 sourceC1720
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1720, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1469 : Integer.Sparse.reindex keyMap MixedData.row1469 = numericRow1469 := by decide +kernel

theorem numericCheck1469 (x : Master → ℝ) : Integer.Sparse.eval numericRow1469 x =
    (17280 : ℝ) * reducedSource1469 x := by
  norm_num [numericRow1469, reducedSource1469, Integer.Sparse.eval, Sparse.eval, nodeValue4104, nodeValue4105, nodeValue4106, nodeValue4126, nodeValue4290, nodeValue4291, nodeValue4307, nodeValue4351, nodeValue4352, nodeValue4354, nodeValue4451, nodeValue4452, nodeValue4461, nodeValue4463, nodeValue4466, nodeValue4489, nodeValue4503, nodeValue5076, nodeValue5172, nodeValue5290, nodeValue5294] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1469 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1469 (mixedVector B) = 0 := by
  have h4104 : mixedVector B (Sum.inr 4104) = Sparse.eval nodeValue4104 (mixedVector B) := by
    change mixedMoment B node4104 node4104Labels = _
    exact sound4104 B hB hF
  have h4105 : mixedVector B (Sum.inr 4105) = Sparse.eval nodeValue4105 (mixedVector B) := by
    change mixedMoment B node4105 node4105Labels = _
    exact sound4105 B hB hF
  have h4106 : mixedVector B (Sum.inr 4106) = Sparse.eval nodeValue4106 (mixedVector B) := by
    change mixedMoment B node4106 node4106Labels = _
    exact sound4106 B hB hF
  have h4126 : mixedVector B (Sum.inr 4126) = Sparse.eval nodeValue4126 (mixedVector B) := by
    change mixedMoment B node4126 node4126Labels = _
    exact sound4126 B hB hF
  have h4290 : mixedVector B (Sum.inr 4290) = Sparse.eval nodeValue4290 (mixedVector B) := by
    change mixedMoment B node4290 node4290Labels = _
    exact sound4290 B hB hF
  have h4291 : mixedVector B (Sum.inr 4291) = Sparse.eval nodeValue4291 (mixedVector B) := by
    change mixedMoment B node4291 node4291Labels = _
    exact sound4291 B hB hF
  have h4307 : mixedVector B (Sum.inr 4307) = Sparse.eval nodeValue4307 (mixedVector B) := by
    change mixedMoment B node4307 node4307Labels = _
    exact sound4307 B hB hF
  have h4351 : mixedVector B (Sum.inr 4351) = Sparse.eval nodeValue4351 (mixedVector B) := by
    change mixedMoment B node4351 node4351Labels = _
    exact sound4351 B hB hF
  have h4352 : mixedVector B (Sum.inr 4352) = Sparse.eval nodeValue4352 (mixedVector B) := by
    change mixedMoment B node4352 node4352Labels = _
    exact sound4352 B hB hF
  have h4354 : mixedVector B (Sum.inr 4354) = Sparse.eval nodeValue4354 (mixedVector B) := by
    change mixedMoment B node4354 node4354Labels = _
    exact sound4354 B hB hF
  have h4451 : mixedVector B (Sum.inr 4451) = Sparse.eval nodeValue4451 (mixedVector B) := by
    change mixedMoment B node4451 node4451Labels = _
    exact sound4451 B hB hF
  have h4452 : mixedVector B (Sum.inr 4452) = Sparse.eval nodeValue4452 (mixedVector B) := by
    change mixedMoment B node4452 node4452Labels = _
    exact sound4452 B hB hF
  have h4461 : mixedVector B (Sum.inr 4461) = Sparse.eval nodeValue4461 (mixedVector B) := by
    change mixedMoment B node4461 node4461Labels = _
    exact sound4461 B hB hF
  have h4463 : mixedVector B (Sum.inr 4463) = Sparse.eval nodeValue4463 (mixedVector B) := by
    change mixedMoment B node4463 node4463Labels = _
    exact sound4463 B hB hF
  have h4466 : mixedVector B (Sum.inr 4466) = Sparse.eval nodeValue4466 (mixedVector B) := by
    change mixedMoment B node4466 node4466Labels = _
    exact sound4466 B hB hF
  have h4489 : mixedVector B (Sum.inr 4489) = Sparse.eval nodeValue4489 (mixedVector B) := by
    change mixedMoment B node4489 node4489Labels = _
    exact sound4489 B hB hF
  have h4503 : mixedVector B (Sum.inr 4503) = Sparse.eval nodeValue4503 (mixedVector B) := by
    change mixedMoment B node4503 node4503Labels = _
    exact sound4503 B hB hF
  have h5076 : mixedVector B (Sum.inr 5076) = Sparse.eval nodeValue5076 (mixedVector B) := by
    change mixedMoment B node5076 node5076Labels = _
    exact sound5076 B hB hF
  have h5172 : mixedVector B (Sum.inr 5172) = Sparse.eval nodeValue5172 (mixedVector B) := by
    change mixedMoment B node5172 node5172Labels = _
    exact sound5172_e B hB hF
  have h5290 : mixedVector B (Sum.inr 5290) = Sparse.eval nodeValue5290 (mixedVector B) := by
    change mixedMoment B node5290 node5290Labels = _
    exact sound5290 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  simpa only [sourceForm1720, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4104, h4105, h4106, h4126, h4290, h4291, h4307, h4351, h4352, h4354, h4451, h4452, h4461, h4463, h4466, h4489, h4503, h5076, h5172, h5290, h5294, reducedSource1469] using sourceEq1720 B hB

theorem rowSound1469_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1469 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1469, numericCheck1469, reducedZero1469 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469_e_oai
