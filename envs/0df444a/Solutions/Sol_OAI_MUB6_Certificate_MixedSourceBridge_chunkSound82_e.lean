-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:36:19.194122+00:00
-- url     : https://prove2.me/submissions/1923829b-a787-412c-bc3b-5b0a8d35aac1

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E108
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1312_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1318_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1321_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1324_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1326_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Orthogonality
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

/-- The finite orthogonality contraction underlying equation (same-matrix). -/
theorem weighted_contraction {H : CMatrix} (hH : IsHadamard H)
    (u v : Coord → ℂ) (i : Coord) :
    (∑ j, (∑ k, u k * H i k * conj (H j k)) *
      (∑ l, v l * conj (H i l) * H j l)) =
      6 * ∑ k, u k * v k := by
  have hexpand :
      (∑ j, (∑ k, u k * H i k * conj (H j k)) *
        (∑ l, v l * conj (H i l) * H j l)) =
      ∑ l, ∑ k, (u k * v l * H i k * conj (H i l)) *
        (∑ j, conj (H j k) * H j l) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand]
  simp_rw [hH.column_orthogonal]
  have hunit (k : Coord) : H i k * conj (H i k) = 1 := by
    rw [Complex.mul_conj, hH.1]
    norm_num
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    u k * v k * H i k * conj (H i k) * 6 =
      6 * (u k * v k) * (H i k * conj (H i k)) := by ring
    _ = _ := by rw [hunit, mul_one]

theorem g_add_difference {H : CMatrix} (hH : IsHadamard H)
    (a : Charge) (i j : Coord) :
    g H (a + difference i j) = (6 : ℂ)⁻¹ *
      ∑ k, character (fun r => H r k) a * H i k * conj (H j k) := by
  simp only [g]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [character_add _ (fun r => unit_ne_zero (hH.1 r k)),
    character_difference _ (fun r => hH.1 r k)]
  ring

/-- Source Lemma (basic), equation (same-matrix), for arbitrary integral charges. -/
theorem same_matrix_identity {H : CMatrix} (hH : IsHadamard H)
    (a b : Charge) (i : Coord) :
    ∑ j, g H (a + difference i j) * g H (b + difference j i) = g H (a + b) := by
  simp_rw [g_add_difference hH]
  have hexpand :
      (∑ j, ((6 : ℂ)⁻¹ * ∑ k, character (fun r => H r k) a * H i k * conj (H j k)) *
        ((6 : ℂ)⁻¹ * ∑ l, character (fun r => H r l) b * H j l * conj (H i l))) =
      (6 : ℂ)⁻¹ * (6 : ℂ)⁻¹ *
        (∑ j, (∑ k, character (fun r => H r k) a * H i k * conj (H j k)) *
          (∑ l, character (fun r => H r l) b * conj (H i l) * H j l)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have he : (∑ l, character (fun r => H r l) b * H j l * conj (H i l)) =
        ∑ l, character (fun r => H r l) b * conj (H i l) * H j l := by
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [he]
    ring
  rw [hexpand, weighted_contraction hH]
  unfold g
  have hs : (∑ k, character (fun r => H r k) a * character (fun r => H r k) b) =
      ∑ k, character (fun r => H r k) (a + b) := by
    apply Finset.sum_congr rfl
    intro k _
    exact (character_add _ (fun r => unit_ne_zero (hH.1 r k)) a b).symm
  rw [hs]
  ring

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

theorem mixedIntegrand_two {l : ℕ} (B : Fin 7 → Basis) (a b : Charge)
    (s t : Fin l) (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
    mixedIntegrand B (doubleCharges a b) ![s, t] r ρ τ =
      g (sampledMatrix B r ρ (τ s)) a * g (sampledMatrix B r ρ (τ t)) b := by
  simp [mixedIntegrand, doubleCharges, Fin.prod_univ_succ, rowFourier, g, character, sampledMatrix]

theorem mixedMoment_same {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s u : Fin l) (i : Coord) :
    (∑ j, mixedMoment B (tripleCharges (a + difference i j) (b + difference j i) c) ![s, s, u]) =
      mixedMoment B (doubleCharges (a + b) c) ![s, u] := by
  simp only [mixedMoment, ← average_sum]
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  simp only [mixedIntegrand_three, mixedIntegrand_two, ← Complex.re_sum, ← Finset.sum_mul]
  rw [same_matrix_identity (sampledMatrix_isHadamard B hB r ρ _) a b i]

theorem mixedMoment_same_reversed {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s u : Fin l) (i : Coord) :
    (∑ j, mixedMoment B (tripleCharges (a + difference j i) (b + difference i j) c) ![s, s, u]) =
      mixedMoment B (doubleCharges (a + b) c) ![s, u] := by
  simp only [mixedMoment, ← average_sum]
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  simp only [mixedIntegrand_three, mixedIntegrand_two, ← Complex.re_sum, ← Finset.sum_mul]
  have h := same_matrix_identity (sampledMatrix_isHadamard B hB r ρ (τ s)) b a i
  simpa only [mul_comm, add_comm] using congrArg
    (fun z => (z * g (sampledMatrix B r ρ (τ u)) c).re) h

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

theorem canonical1296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1296 raw1296Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw1296 raw1296Labels = mixedMoment B raw1296step0 raw1296step0Labels := by
      have ha : raw1296step0 = (fun i j => raw1296 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1296step0 raw1296; decide +kernel
      have hl : raw1296step0Labels = raw1296Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1296 raw1296Labels permutation8 permutation4
    mixedMoment B raw1296step0 raw1296step0Labels = mixedMoment B raw1296step1 raw1296step1Labels := by
      have ha : raw1296step1 = raw1296step0 := by apply Matrix.ext; unfold raw1296step1 raw1296step0; decide +kernel
      have hl : raw1296step0Labels = labelEmbedding7 ∘ raw1296step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1296step0 raw1296step0Labels raw1296step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4496 node4496Labels := by rfl

theorem canonical1297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1297 raw1297Labels = mixedMoment B node1080 node1080Labels := by
  calc
    mixedMoment B raw1297 raw1297Labels = mixedMoment B raw1297step0 raw1297step0Labels := by
      have ha : raw1297step0 = (fun i j => raw1297 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1297step0 raw1297; decide +kernel
      have hl : raw1297step0Labels = raw1297Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1297 raw1297Labels permutation8 permutation4
    _ = mixedMoment B node1080 node1080Labels := by rfl

theorem canonical1298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1298 raw1298Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw1298 raw1298Labels = mixedMoment B raw1298step0 raw1298step0Labels := by
      have ha : raw1298step0 = (fun i j => raw1298 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1298step0 raw1298; decide +kernel
      have hl : raw1298step0Labels = raw1298Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1298 raw1298Labels permutation8 permutation6
    mixedMoment B raw1298step0 raw1298step0Labels = mixedMoment B raw1298step1 raw1298step1Labels := by
      have ha : raw1298step1 = -raw1298step0 := by apply Matrix.ext; change ∀ i j, raw1298step1 i j = -(raw1298step0 i j); unfold raw1298step1 raw1298step0; decide +kernel
      have hl : raw1298step1Labels = raw1298step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1298step1 raw1298step1Labels = mixedMoment B raw1298step2 raw1298step2Labels := by
      have ha : raw1298step2 = raw1298step1 := by apply Matrix.ext; unfold raw1298step2 raw1298step1; decide +kernel
      have hl : raw1298step1Labels = labelEmbedding1 ∘ raw1298step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1298step1 raw1298step1Labels raw1298step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1710 node1710Labels := by rfl

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

theorem canonical1776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1776 raw1776Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw1776 raw1776Labels = mixedMoment B raw1776step0 raw1776step0Labels := by
      have ha : raw1776step0 = (fun i j => raw1776 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1776step0 raw1776; decide +kernel
      have hl : raw1776step0Labels = raw1776Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1776 raw1776Labels permutation8 permutation4
    mixedMoment B raw1776step0 raw1776step0Labels = mixedMoment B raw1776step1 raw1776step1Labels := by
      have ha : raw1776step1 = raw1776step0 := by apply Matrix.ext; unfold raw1776step1 raw1776step0; decide +kernel
      have hl : raw1776step0Labels = labelEmbedding7 ∘ raw1776step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1776step0 raw1776step0Labels raw1776step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4845 node4845Labels := by rfl

theorem canonical1777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1777 raw1777Labels = mixedMoment B node2065 node2065Labels := by
  calc
    mixedMoment B raw1777 raw1777Labels = mixedMoment B raw1777step0 raw1777step0Labels := by
      have ha : raw1777step0 = (fun i j => raw1777 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1777step0 raw1777; decide +kernel
      have hl : raw1777step0Labels = raw1777Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1777 raw1777Labels permutation8 permutation4
    _ = mixedMoment B node2065 node2065Labels := by rfl

theorem canonical1778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1778 raw1778Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw1778 raw1778Labels = mixedMoment B raw1778step0 raw1778step0Labels := by
      have ha : raw1778step0 = (fun i j => raw1778 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1778step0 raw1778; decide +kernel
      have hl : raw1778step0Labels = raw1778Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1778 raw1778Labels permutation8 permutation6
    mixedMoment B raw1778step0 raw1778step0Labels = mixedMoment B raw1778step1 raw1778step1Labels := by
      have ha : raw1778step1 = -raw1778step0 := by apply Matrix.ext; change ∀ i j, raw1778step1 i j = -(raw1778step0 i j); unfold raw1778step1 raw1778step0; decide +kernel
      have hl : raw1778step1Labels = raw1778step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1778step1 raw1778step1Labels = mixedMoment B raw1778step2 raw1778step2Labels := by
      have ha : raw1778step2 = raw1778step1 := by apply Matrix.ext; unfold raw1778step2 raw1778step1; decide +kernel
      have hl : raw1778step1Labels = labelEmbedding1 ∘ raw1778step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1778step1 raw1778step1Labels raw1778step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2218 node2218Labels := by rfl

end MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical151
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19413 raw19413Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw19413 raw19413Labels = mixedMoment B raw19413step0 raw19413step0Labels := by
      have hz : ∀ j, raw19413 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19413step0 = (fun i j => raw19413 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19413step0 raw19413; decide +kernel
      have hl : raw19413step0Labels = raw19413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19413 raw19413Labels permutation434 hz
    mixedMoment B raw19413step0 raw19413step0Labels = mixedMoment B raw19413step1 raw19413step1Labels := by
      have hz : ∀ j, raw19413step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19413step1 = (fun i j => raw19413step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19413step1 raw19413step0; decide +kernel
      have hl : raw19413step1Labels = raw19413step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19413step0 raw19413step0Labels permutation80 hz
    mixedMoment B raw19413step1 raw19413step1Labels = mixedMoment B raw19413step2 raw19413step2Labels := by
      have hz : ∀ j, raw19413step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19413step2 = (fun i j => raw19413step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19413step2 raw19413step1; decide +kernel
      have hl : raw19413step2Labels = raw19413step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19413step1 raw19413step1Labels permutation14 hz
    mixedMoment B raw19413step2 raw19413step2Labels = mixedMoment B raw19413step3 raw19413step3Labels := by
      have ha : raw19413step3 = (fun i j => raw19413step2 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19413step3 raw19413step2; decide +kernel
      have hl : raw19413step3Labels = raw19413step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19413step2 raw19413step2Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical156
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20088 raw20088Labels = mixedMoment B node621 node621Labels := by
  calc
    mixedMoment B raw20088 raw20088Labels = mixedMoment B raw20088step0 raw20088step0Labels := by
      have hz : ∀ j, raw20088 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20088step0 = (fun i j => raw20088 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20088step0 raw20088; decide +kernel
      have hl : raw20088step0Labels = raw20088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20088 raw20088Labels permutation434 hz
    mixedMoment B raw20088step0 raw20088step0Labels = mixedMoment B raw20088step1 raw20088step1Labels := by
      have hz : ∀ j, raw20088step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20088step1 = (fun i j => raw20088step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20088step1 raw20088step0; decide +kernel
      have hl : raw20088step1Labels = raw20088step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20088step0 raw20088step0Labels permutation80 hz
    mixedMoment B raw20088step1 raw20088step1Labels = mixedMoment B raw20088step2 raw20088step2Labels := by
      have hz : ∀ j, raw20088step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20088step2 = (fun i j => raw20088step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20088step2 raw20088step1; decide +kernel
      have hl : raw20088step2Labels = raw20088step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20088step1 raw20088step1Labels permutation14 hz
    _ = mixedMoment B node621 node621Labels := by rfl

theorem canonical20092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20092 raw20092Labels = mixedMoment B node1094 node1094Labels := by
  calc
    mixedMoment B raw20092 raw20092Labels = mixedMoment B raw20092step0 raw20092step0Labels := by
      have hz : ∀ j, raw20092 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20092step0 = (fun i j => raw20092 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20092step0 raw20092; decide +kernel
      have hl : raw20092step0Labels = raw20092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20092 raw20092Labels permutation434 hz
    mixedMoment B raw20092step0 raw20092step0Labels = mixedMoment B raw20092step1 raw20092step1Labels := by
      have hz : ∀ j, raw20092step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20092step1 = (fun i j => raw20092step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20092step1 raw20092step0; decide +kernel
      have hl : raw20092step1Labels = raw20092step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20092step0 raw20092step0Labels permutation80 hz
    mixedMoment B raw20092step1 raw20092step1Labels = mixedMoment B raw20092step2 raw20092step2Labels := by
      have hz : ∀ j, raw20092step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20092step2 = (fun i j => raw20092step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20092step2 raw20092step1; decide +kernel
      have hl : raw20092step2Labels = raw20092step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20092step1 raw20092step1Labels permutation14 hz
    mixedMoment B raw20092step2 raw20092step2Labels = mixedMoment B raw20092step3 raw20092step3Labels := by
      have ha : raw20092step3 = (fun i j => raw20092step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20092step3 raw20092step2; decide +kernel
      have hl : raw20092step3Labels = raw20092step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20092step2 raw20092step2Labels permutation3 permutation2
    _ = mixedMoment B node1094 node1094Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical168
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21585 raw21585Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw21585 raw21585Labels = mixedMoment B raw21585step0 raw21585step0Labels := by
      have hz : ∀ j, raw21585 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21585step0 = (fun i j => raw21585 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21585step0 raw21585; decide +kernel
      have hl : raw21585step0Labels = raw21585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21585 raw21585Labels permutation346 hz
    mixedMoment B raw21585step0 raw21585step0Labels = mixedMoment B raw21585step1 raw21585step1Labels := by
      have ha : raw21585step1 = (fun i j => raw21585step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21585step1 raw21585step0; decide +kernel
      have hl : raw21585step1Labels = raw21585step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21585step0 raw21585step0Labels permutation38 permutation2
    _ = mixedMoment B node2206 node2206Labels := by rfl

theorem canonical21586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21586 raw21586Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw21586 raw21586Labels = mixedMoment B raw21586step0 raw21586step0Labels := by
      have hz : ∀ j, raw21586 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21586step0 = (fun i j => raw21586 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21586step0 raw21586; decide +kernel
      have hl : raw21586step0Labels = raw21586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21586 raw21586Labels permutation346 hz
    mixedMoment B raw21586step0 raw21586step0Labels = mixedMoment B raw21586step1 raw21586step1Labels := by
      have ha : raw21586step1 = (fun i j => raw21586step0 (permutation39 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21586step1 raw21586step0; decide +kernel
      have hl : raw21586step1Labels = raw21586step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21586step0 raw21586step0Labels permutation39 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical21590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21590 raw21590Labels = mixedMoment B node985 node985Labels := by
  calc
    mixedMoment B raw21590 raw21590Labels = mixedMoment B raw21590step0 raw21590step0Labels := by
      have hz : ∀ j, raw21590 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21590step0 = (fun i j => raw21590 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21590step0 raw21590; decide +kernel
      have hl : raw21590step0Labels = raw21590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21590 raw21590Labels permutation346 hz
    mixedMoment B raw21590step0 raw21590step0Labels = mixedMoment B raw21590step1 raw21590step1Labels := by
      have ha : raw21590step1 = (fun i j => raw21590step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21590step1 raw21590step0; decide +kernel
      have hl : raw21590step1Labels = raw21590step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21590step0 raw21590step0Labels permutation39 permutation2
    _ = mixedMoment B node985 node985Labels := by rfl

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

theorem canonical21660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21660 raw21660Labels = mixedMoment B node2293 node2293Labels := by
  calc
    mixedMoment B raw21660 raw21660Labels = mixedMoment B raw21660step0 raw21660step0Labels := by
      have hz : ∀ j, raw21660 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21660step0 = (fun i j => raw21660 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21660step0 raw21660; decide +kernel
      have hl : raw21660step0Labels = raw21660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21660 raw21660Labels permutation434 hz
    mixedMoment B raw21660step0 raw21660step0Labels = mixedMoment B raw21660step1 raw21660step1Labels := by
      have hz : ∀ j, raw21660step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21660step1 = (fun i j => raw21660step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21660step1 raw21660step0; decide +kernel
      have hl : raw21660step1Labels = raw21660step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21660step0 raw21660step0Labels permutation80 hz
    mixedMoment B raw21660step1 raw21660step1Labels = mixedMoment B raw21660step2 raw21660step2Labels := by
      have hz : ∀ j, raw21660step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21660step2 = (fun i j => raw21660step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21660step2 raw21660step1; decide +kernel
      have hl : raw21660step2Labels = raw21660step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21660step1 raw21660step1Labels permutation14 hz
    mixedMoment B raw21660step2 raw21660step2Labels = mixedMoment B raw21660step3 raw21660step3Labels := by
      have ha : raw21660step3 = (fun i j => raw21660step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21660step3 raw21660step2; decide +kernel
      have hl : raw21660step3Labels = raw21660step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21660step2 raw21660step2Labels permutation3 permutation7
    mixedMoment B raw21660step3 raw21660step3Labels = mixedMoment B raw21660step4 raw21660step4Labels := by
      have ha : raw21660step4 = -raw21660step3 := by apply Matrix.ext; change ∀ i j, raw21660step4 i j = -(raw21660step3 i j); unfold raw21660step4 raw21660step3; decide +kernel
      have hl : raw21660step4Labels = raw21660step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21660step4 raw21660step4Labels = mixedMoment B raw21660step5 raw21660step5Labels := by
      have ha : raw21660step5 = raw21660step4 := by apply Matrix.ext; unfold raw21660step5 raw21660step4; decide +kernel
      have hl : raw21660step4Labels = labelEmbedding1 ∘ raw21660step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21660step4 raw21660step4Labels raw21660step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2293 node2293Labels := by rfl

theorem canonical21665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21665 raw21665Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw21665 raw21665Labels = mixedMoment B raw21665step0 raw21665step0Labels := by
      have hz : ∀ j, raw21665 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21665step0 = (fun i j => raw21665 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21665step0 raw21665; decide +kernel
      have hl : raw21665step0Labels = raw21665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21665 raw21665Labels permutation434 hz
    mixedMoment B raw21665step0 raw21665step0Labels = mixedMoment B raw21665step1 raw21665step1Labels := by
      have hz : ∀ j, raw21665step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21665step1 = (fun i j => raw21665step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21665step1 raw21665step0; decide +kernel
      have hl : raw21665step1Labels = raw21665step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21665step0 raw21665step0Labels permutation80 hz
    mixedMoment B raw21665step1 raw21665step1Labels = mixedMoment B raw21665step2 raw21665step2Labels := by
      have ha : raw21665step2 = (fun i j => raw21665step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21665step2 raw21665step1; decide +kernel
      have hl : raw21665step2Labels = raw21665step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21665step1 raw21665step1Labels permutation9 permutation7
    mixedMoment B raw21665step2 raw21665step2Labels = mixedMoment B raw21665step3 raw21665step3Labels := by
      have ha : raw21665step3 = -raw21665step2 := by apply Matrix.ext; change ∀ i j, raw21665step3 i j = -(raw21665step2 i j); unfold raw21665step3 raw21665step2; decide +kernel
      have hl : raw21665step3Labels = raw21665step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21665step3 raw21665step3Labels = mixedMoment B raw21665step4 raw21665step4Labels := by
      have ha : raw21665step4 = raw21665step3 := by apply Matrix.ext; unfold raw21665step4 raw21665step3; decide +kernel
      have hl : raw21665step3Labels = labelEmbedding1 ∘ raw21665step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21665step3 raw21665step3Labels raw21665step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

theorem canonical21670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21670 raw21670Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw21670 raw21670Labels = mixedMoment B raw21670step0 raw21670step0Labels := by
      have hz : ∀ j, raw21670 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21670step0 = (fun i j => raw21670 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21670step0 raw21670; decide +kernel
      have hl : raw21670step0Labels = raw21670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21670 raw21670Labels permutation434 hz
    mixedMoment B raw21670step0 raw21670step0Labels = mixedMoment B raw21670step1 raw21670step1Labels := by
      have hz : ∀ j, raw21670step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21670step1 = (fun i j => raw21670step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21670step1 raw21670step0; decide +kernel
      have hl : raw21670step1Labels = raw21670step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21670step0 raw21670step0Labels permutation56 hz
    mixedMoment B raw21670step1 raw21670step1Labels = mixedMoment B raw21670step2 raw21670step2Labels := by
      have ha : raw21670step2 = (fun i j => raw21670step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21670step2 raw21670step1; decide +kernel
      have hl : raw21670step2Labels = raw21670step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21670step1 raw21670step1Labels permutation9 permutation7
    mixedMoment B raw21670step2 raw21670step2Labels = mixedMoment B raw21670step3 raw21670step3Labels := by
      have ha : raw21670step3 = -raw21670step2 := by apply Matrix.ext; change ∀ i j, raw21670step3 i j = -(raw21670step2 i j); unfold raw21670step3 raw21670step2; decide +kernel
      have hl : raw21670step3Labels = raw21670step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21670step3 raw21670step3Labels = mixedMoment B raw21670step4 raw21670step4Labels := by
      have ha : raw21670step4 = raw21670step3 := by apply Matrix.ext; unfold raw21670step4 raw21670step3; decide +kernel
      have hl : raw21670step3Labels = labelEmbedding1 ∘ raw21670step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21670step3 raw21670step3Labels raw21670step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

theorem canonical21675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21675 raw21675Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw21675 raw21675Labels = mixedMoment B raw21675step0 raw21675step0Labels := by
      have hz : ∀ j, raw21675 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21675step0 = (fun i j => raw21675 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21675step0 raw21675; decide +kernel
      have hl : raw21675step0Labels = raw21675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21675 raw21675Labels permutation346 hz
    mixedMoment B raw21675step0 raw21675step0Labels = mixedMoment B raw21675step1 raw21675step1Labels := by
      have hz : ∀ j, raw21675step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21675step1 = (fun i j => raw21675step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21675step1 raw21675step0; decide +kernel
      have hl : raw21675step1Labels = raw21675step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21675step0 raw21675step0Labels permutation56 hz
    mixedMoment B raw21675step1 raw21675step1Labels = mixedMoment B raw21675step2 raw21675step2Labels := by
      have ha : raw21675step2 = (fun i j => raw21675step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21675step2 raw21675step1; decide +kernel
      have hl : raw21675step2Labels = raw21675step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21675step1 raw21675step1Labels permutation9 permutation7
    mixedMoment B raw21675step2 raw21675step2Labels = mixedMoment B raw21675step3 raw21675step3Labels := by
      have ha : raw21675step3 = -raw21675step2 := by apply Matrix.ext; change ∀ i j, raw21675step3 i j = -(raw21675step2 i j); unfold raw21675step3 raw21675step2; decide +kernel
      have hl : raw21675step3Labels = raw21675step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21675step3 raw21675step3Labels = mixedMoment B raw21675step4 raw21675step4Labels := by
      have ha : raw21675step4 = raw21675step3 := by apply Matrix.ext; unfold raw21675step4 raw21675step3; decide +kernel
      have hl : raw21675step3Labels = labelEmbedding1 ∘ raw21675step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21675step3 raw21675step3Labels raw21675step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

theorem canonical21676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21676 raw21676Labels = mixedMoment B node1539 node1539Labels := by
  calc
    mixedMoment B raw21676 raw21676Labels = mixedMoment B raw21676step0 raw21676step0Labels := by
      have hz : ∀ j, raw21676 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21676step0 = (fun i j => raw21676 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21676step0 raw21676; decide +kernel
      have hl : raw21676step0Labels = raw21676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21676 raw21676Labels permutation434 hz
    mixedMoment B raw21676step0 raw21676step0Labels = mixedMoment B raw21676step1 raw21676step1Labels := by
      have hz : ∀ j, raw21676step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21676step1 = (fun i j => raw21676step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21676step1 raw21676step0; decide +kernel
      have hl : raw21676step1Labels = raw21676step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21676step0 raw21676step0Labels permutation80 hz
    mixedMoment B raw21676step1 raw21676step1Labels = mixedMoment B raw21676step2 raw21676step2Labels := by
      have hz : ∀ j, raw21676step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21676step2 = (fun i j => raw21676step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21676step2 raw21676step1; decide +kernel
      have hl : raw21676step2Labels = raw21676step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21676step1 raw21676step1Labels permutation14 hz
    mixedMoment B raw21676step2 raw21676step2Labels = mixedMoment B raw21676step3 raw21676step3Labels := by
      have ha : raw21676step3 = (fun i j => raw21676step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21676step3 raw21676step2; decide +kernel
      have hl : raw21676step3Labels = raw21676step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21676step2 raw21676step2Labels permutation3 permutation7
    mixedMoment B raw21676step3 raw21676step3Labels = mixedMoment B raw21676step4 raw21676step4Labels := by
      have ha : raw21676step4 = -raw21676step3 := by apply Matrix.ext; change ∀ i j, raw21676step4 i j = -(raw21676step3 i j); unfold raw21676step4 raw21676step3; decide +kernel
      have hl : raw21676step4Labels = raw21676step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21676step4 raw21676step4Labels = mixedMoment B raw21676step5 raw21676step5Labels := by
      have ha : raw21676step5 = raw21676step4 := by apply Matrix.ext; unfold raw21676step5 raw21676step4; decide +kernel
      have hl : raw21676step4Labels = labelEmbedding1 ∘ raw21676step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21676step4 raw21676step4Labels raw21676step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1539 node1539Labels := by rfl

theorem canonical21677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21677 raw21677Labels = mixedMoment B node1694 node1694Labels := by
  calc
    mixedMoment B raw21677 raw21677Labels = mixedMoment B raw21677step0 raw21677step0Labels := by
      have hz : ∀ j, raw21677 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21677step0 = (fun i j => raw21677 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21677step0 raw21677; decide +kernel
      have hl : raw21677step0Labels = raw21677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21677 raw21677Labels permutation434 hz
    mixedMoment B raw21677step0 raw21677step0Labels = mixedMoment B raw21677step1 raw21677step1Labels := by
      have hz : ∀ j, raw21677step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21677step1 = (fun i j => raw21677step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21677step1 raw21677step0; decide +kernel
      have hl : raw21677step1Labels = raw21677step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21677step0 raw21677step0Labels permutation80 hz
    mixedMoment B raw21677step1 raw21677step1Labels = mixedMoment B raw21677step2 raw21677step2Labels := by
      have ha : raw21677step2 = (fun i j => raw21677step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21677step2 raw21677step1; decide +kernel
      have hl : raw21677step2Labels = raw21677step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21677step1 raw21677step1Labels permutation9 permutation7
    mixedMoment B raw21677step2 raw21677step2Labels = mixedMoment B raw21677step3 raw21677step3Labels := by
      have ha : raw21677step3 = -raw21677step2 := by apply Matrix.ext; change ∀ i j, raw21677step3 i j = -(raw21677step2 i j); unfold raw21677step3 raw21677step2; decide +kernel
      have hl : raw21677step3Labels = raw21677step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21677step3 raw21677step3Labels = mixedMoment B raw21677step4 raw21677step4Labels := by
      have ha : raw21677step4 = raw21677step3 := by apply Matrix.ext; unfold raw21677step4 raw21677step3; decide +kernel
      have hl : raw21677step3Labels = labelEmbedding1 ∘ raw21677step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21677step3 raw21677step3Labels raw21677step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1694 node1694Labels := by rfl

theorem canonical21678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21678 raw21678Labels = mixedMoment B node1694 node1694Labels := by
  calc
    mixedMoment B raw21678 raw21678Labels = mixedMoment B raw21678step0 raw21678step0Labels := by
      have hz : ∀ j, raw21678 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21678step0 = (fun i j => raw21678 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21678step0 raw21678; decide +kernel
      have hl : raw21678step0Labels = raw21678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21678 raw21678Labels permutation434 hz
    mixedMoment B raw21678step0 raw21678step0Labels = mixedMoment B raw21678step1 raw21678step1Labels := by
      have hz : ∀ j, raw21678step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21678step1 = (fun i j => raw21678step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21678step1 raw21678step0; decide +kernel
      have hl : raw21678step1Labels = raw21678step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21678step0 raw21678step0Labels permutation56 hz
    mixedMoment B raw21678step1 raw21678step1Labels = mixedMoment B raw21678step2 raw21678step2Labels := by
      have ha : raw21678step2 = (fun i j => raw21678step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21678step2 raw21678step1; decide +kernel
      have hl : raw21678step2Labels = raw21678step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21678step1 raw21678step1Labels permutation9 permutation7
    mixedMoment B raw21678step2 raw21678step2Labels = mixedMoment B raw21678step3 raw21678step3Labels := by
      have ha : raw21678step3 = -raw21678step2 := by apply Matrix.ext; change ∀ i j, raw21678step3 i j = -(raw21678step2 i j); unfold raw21678step3 raw21678step2; decide +kernel
      have hl : raw21678step3Labels = raw21678step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21678step3 raw21678step3Labels = mixedMoment B raw21678step4 raw21678step4Labels := by
      have ha : raw21678step4 = raw21678step3 := by apply Matrix.ext; unfold raw21678step4 raw21678step3; decide +kernel
      have hl : raw21678step3Labels = labelEmbedding1 ∘ raw21678step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21678step3 raw21678step3Labels raw21678step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1694 node1694Labels := by rfl

theorem canonical21679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21679 raw21679Labels = mixedMoment B node1694 node1694Labels := by
  calc
    mixedMoment B raw21679 raw21679Labels = mixedMoment B raw21679step0 raw21679step0Labels := by
      have hz : ∀ j, raw21679 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21679step0 = (fun i j => raw21679 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21679step0 raw21679; decide +kernel
      have hl : raw21679step0Labels = raw21679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21679 raw21679Labels permutation346 hz
    mixedMoment B raw21679step0 raw21679step0Labels = mixedMoment B raw21679step1 raw21679step1Labels := by
      have hz : ∀ j, raw21679step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21679step1 = (fun i j => raw21679step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21679step1 raw21679step0; decide +kernel
      have hl : raw21679step1Labels = raw21679step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21679step0 raw21679step0Labels permutation56 hz
    mixedMoment B raw21679step1 raw21679step1Labels = mixedMoment B raw21679step2 raw21679step2Labels := by
      have ha : raw21679step2 = (fun i j => raw21679step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21679step2 raw21679step1; decide +kernel
      have hl : raw21679step2Labels = raw21679step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21679step1 raw21679step1Labels permutation9 permutation7
    mixedMoment B raw21679step2 raw21679step2Labels = mixedMoment B raw21679step3 raw21679step3Labels := by
      have ha : raw21679step3 = -raw21679step2 := by apply Matrix.ext; change ∀ i j, raw21679step3 i j = -(raw21679step2 i j); unfold raw21679step3 raw21679step2; decide +kernel
      have hl : raw21679step3Labels = raw21679step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21679step3 raw21679step3Labels = mixedMoment B raw21679step4 raw21679step4Labels := by
      have ha : raw21679step4 = raw21679step3 := by apply Matrix.ext; unfold raw21679step4 raw21679step3; decide +kernel
      have hl : raw21679step3Labels = labelEmbedding1 ∘ raw21679step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21679step3 raw21679step3Labels raw21679step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1694 node1694Labels := by rfl

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

theorem canonical21889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21889 raw21889Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw21889 raw21889Labels = mixedMoment B raw21889step0 raw21889step0Labels := by
      have hz : ∀ j, raw21889 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21889step0 = (fun i j => raw21889 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21889step0 raw21889; decide +kernel
      have hl : raw21889step0Labels = raw21889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21889 raw21889Labels permutation346 hz
    mixedMoment B raw21889step0 raw21889step0Labels = mixedMoment B raw21889step1 raw21889step1Labels := by
      have hz : ∀ j, raw21889step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21889step1 = (fun i j => raw21889step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21889step1 raw21889step0; decide +kernel
      have hl : raw21889step1Labels = raw21889step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21889step0 raw21889step0Labels permutation56 hz
    _ = mixedMoment B node2230 node2230Labels := by rfl

theorem canonical21890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21890 raw21890Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw21890 raw21890Labels = mixedMoment B raw21890step0 raw21890step0Labels := by
      have hz : ∀ j, raw21890 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21890step0 = (fun i j => raw21890 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21890step0 raw21890; decide +kernel
      have hl : raw21890step0Labels = raw21890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21890 raw21890Labels permutation346 hz
    mixedMoment B raw21890step0 raw21890step0Labels = mixedMoment B raw21890step1 raw21890step1Labels := by
      have hz : ∀ j, raw21890step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21890step1 = (fun i j => raw21890step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21890step1 raw21890step0; decide +kernel
      have hl : raw21890step1Labels = raw21890step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21890step0 raw21890step0Labels permutation56 hz
    mixedMoment B raw21890step1 raw21890step1Labels = mixedMoment B raw21890step2 raw21890step2Labels := by
      have ha : raw21890step2 = (fun i j => raw21890step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21890step2 raw21890step1; decide +kernel
      have hl : raw21890step2Labels = raw21890step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21890step1 raw21890step1Labels permutation9 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical21894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21894 raw21894Labels = mixedMoment B node1012 node1012Labels := by
  calc
    mixedMoment B raw21894 raw21894Labels = mixedMoment B raw21894step0 raw21894step0Labels := by
      have hz : ∀ j, raw21894 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21894step0 = (fun i j => raw21894 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21894step0 raw21894; decide +kernel
      have hl : raw21894step0Labels = raw21894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21894 raw21894Labels permutation346 hz
    mixedMoment B raw21894step0 raw21894step0Labels = mixedMoment B raw21894step1 raw21894step1Labels := by
      have hz : ∀ j, raw21894step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21894step1 = (fun i j => raw21894step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21894step1 raw21894step0; decide +kernel
      have hl : raw21894step1Labels = raw21894step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21894step0 raw21894step0Labels permutation56 hz
    mixedMoment B raw21894step1 raw21894step1Labels = mixedMoment B raw21894step2 raw21894step2Labels := by
      have ha : raw21894step2 = (fun i j => raw21894step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21894step2 raw21894step1; decide +kernel
      have hl : raw21894step2Labels = raw21894step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21894step1 raw21894step1Labels permutation9 permutation2
    _ = mixedMoment B node1012 node1012Labels := by rfl

theorem canonical21901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21901 raw21901Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw21901 raw21901Labels = mixedMoment B raw21901step0 raw21901step0Labels := by
      have hz : ∀ j, raw21901 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21901step0 = (fun i j => raw21901 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21901step0 raw21901; decide +kernel
      have hl : raw21901step0Labels = raw21901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21901 raw21901Labels permutation346 hz
    mixedMoment B raw21901step0 raw21901step0Labels = mixedMoment B raw21901step1 raw21901step1Labels := by
      have hz : ∀ j, raw21901step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21901step1 = (fun i j => raw21901step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21901step1 raw21901step0; decide +kernel
      have hl : raw21901step1Labels = raw21901step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21901step0 raw21901step0Labels permutation56 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical21906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21906 raw21906Labels = mixedMoment B node576 node576Labels := by
  calc
    mixedMoment B raw21906 raw21906Labels = mixedMoment B raw21906step0 raw21906step0Labels := by
      have hz : ∀ j, raw21906 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21906step0 = (fun i j => raw21906 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21906step0 raw21906; decide +kernel
      have hl : raw21906step0Labels = raw21906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21906 raw21906Labels permutation346 hz
    mixedMoment B raw21906step0 raw21906step0Labels = mixedMoment B raw21906step1 raw21906step1Labels := by
      have hz : ∀ j, raw21906step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21906step1 = (fun i j => raw21906step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21906step1 raw21906step0; decide +kernel
      have hl : raw21906step1Labels = raw21906step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21906step0 raw21906step0Labels permutation56 hz
    _ = mixedMoment B node576 node576Labels := by rfl

theorem canonical21909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21909 raw21909Labels = mixedMoment B node1013 node1013Labels := by
  calc
    mixedMoment B raw21909 raw21909Labels = mixedMoment B raw21909step0 raw21909step0Labels := by
      have hz : ∀ j, raw21909 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21909step0 = (fun i j => raw21909 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21909step0 raw21909; decide +kernel
      have hl : raw21909step0Labels = raw21909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21909 raw21909Labels permutation346 hz
    mixedMoment B raw21909step0 raw21909step0Labels = mixedMoment B raw21909step1 raw21909step1Labels := by
      have hz : ∀ j, raw21909step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21909step1 = (fun i j => raw21909step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21909step1 raw21909step0; decide +kernel
      have hl : raw21909step1Labels = raw21909step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21909step0 raw21909step0Labels permutation56 hz
    _ = mixedMoment B node1013 node1013Labels := by rfl

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

theorem canonical22329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22329 raw22329Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw22329 raw22329Labels = mixedMoment B raw22329step0 raw22329step0Labels := by
      have hz : ∀ j, raw22329 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22329step0 = (fun i j => raw22329 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22329step0 raw22329; decide +kernel
      have hl : raw22329step0Labels = raw22329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22329 raw22329Labels permutation434 hz
    mixedMoment B raw22329step0 raw22329step0Labels = mixedMoment B raw22329step1 raw22329step1Labels := by
      have hz : ∀ j, raw22329step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22329step1 = (fun i j => raw22329step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22329step1 raw22329step0; decide +kernel
      have hl : raw22329step1Labels = raw22329step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22329step0 raw22329step0Labels permutation80 hz
    mixedMoment B raw22329step1 raw22329step1Labels = mixedMoment B raw22329step2 raw22329step2Labels := by
      have hz : ∀ j, raw22329step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22329step2 = (fun i j => raw22329step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22329step2 raw22329step1; decide +kernel
      have hl : raw22329step2Labels = raw22329step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22329step1 raw22329step1Labels permutation14 hz
    mixedMoment B raw22329step2 raw22329step2Labels = mixedMoment B raw22329step3 raw22329step3Labels := by
      have ha : raw22329step3 = -raw22329step2 := by apply Matrix.ext; change ∀ i j, raw22329step3 i j = -(raw22329step2 i j); unfold raw22329step3 raw22329step2; decide +kernel
      have hl : raw22329step3Labels = raw22329step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4071 node4071Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical182
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23308 raw23308Labels = mixedMoment B node984 node984Labels := by
  calc
    mixedMoment B raw23308 raw23308Labels = mixedMoment B raw23308step0 raw23308step0Labels := by
      have hz : ∀ j, raw23308 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23308step0 = (fun i j => raw23308 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23308step0 raw23308; decide +kernel
      have hl : raw23308step0Labels = raw23308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23308 raw23308Labels permutation346 hz
    mixedMoment B raw23308step0 raw23308step0Labels = mixedMoment B raw23308step1 raw23308step1Labels := by
      have ha : raw23308step1 = (fun i j => raw23308step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23308step1 raw23308step0; decide +kernel
      have hl : raw23308step1Labels = raw23308step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23308step0 raw23308step0Labels permutation39 permutation2
    _ = mixedMoment B node984 node984Labels := by rfl

theorem canonical23309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23309 raw23309Labels = mixedMoment B node2081 node2081Labels := by
  calc
    mixedMoment B raw23309 raw23309Labels = mixedMoment B raw23309step0 raw23309step0Labels := by
      have hz : ∀ j, raw23309 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23309step0 = (fun i j => raw23309 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23309step0 raw23309; decide +kernel
      have hl : raw23309step0Labels = raw23309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23309 raw23309Labels permutation346 hz
    mixedMoment B raw23309step0 raw23309step0Labels = mixedMoment B raw23309step1 raw23309step1Labels := by
      have ha : raw23309step1 = (fun i j => raw23309step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23309step1 raw23309step0; decide +kernel
      have hl : raw23309step1Labels = raw23309step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23309step0 raw23309step0Labels permutation33 permutation2
    _ = mixedMoment B node2081 node2081Labels := by rfl

theorem canonical23310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23310 raw23310Labels = mixedMoment B node1989 node1989Labels := by
  calc
    mixedMoment B raw23310 raw23310Labels = mixedMoment B raw23310step0 raw23310step0Labels := by
      have ha : raw23310step0 = (fun i j => raw23310 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23310step0 raw23310; decide +kernel
      have hl : raw23310step0Labels = raw23310Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23310 raw23310Labels permutation183 permutation2
    _ = mixedMoment B node1989 node1989Labels := by rfl

theorem canonical23311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23311 raw23311Labels = mixedMoment B node1917 node1917Labels := by
  calc
    mixedMoment B raw23311 raw23311Labels = mixedMoment B raw23311step0 raw23311step0Labels := by
      have hz : ∀ j, raw23311 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23311step0 = (fun i j => raw23311 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23311step0 raw23311; decide +kernel
      have hl : raw23311step0Labels = raw23311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23311 raw23311Labels permutation346 hz
    mixedMoment B raw23311step0 raw23311step0Labels = mixedMoment B raw23311step1 raw23311step1Labels := by
      have ha : raw23311step1 = (fun i j => raw23311step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23311step1 raw23311step0; decide +kernel
      have hl : raw23311step1Labels = raw23311step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23311step0 raw23311step0Labels permutation39 permutation2
    _ = mixedMoment B node1917 node1917Labels := by rfl

theorem canonical23312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23312 raw23312Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw23312 raw23312Labels = mixedMoment B raw23312step0 raw23312step0Labels := by
      have hz : ∀ j, raw23312 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23312step0 = (fun i j => raw23312 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23312step0 raw23312; decide +kernel
      have hl : raw23312step0Labels = raw23312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23312 raw23312Labels permutation346 hz
    mixedMoment B raw23312step0 raw23312step0Labels = mixedMoment B raw23312step1 raw23312step1Labels := by
      have ha : raw23312step1 = (fun i j => raw23312step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23312step1 raw23312step0; decide +kernel
      have hl : raw23312step1Labels = raw23312step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23312step0 raw23312step0Labels permutation38 permutation2
    _ = mixedMoment B node2207 node2207Labels := by rfl

theorem canonical23313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23313 raw23313Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw23313 raw23313Labels = mixedMoment B raw23313step0 raw23313step0Labels := by
      have hz : ∀ j, raw23313 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23313step0 = (fun i j => raw23313 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23313step0 raw23313; decide +kernel
      have hl : raw23313step0Labels = raw23313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23313 raw23313Labels permutation346 hz
    mixedMoment B raw23313step0 raw23313step0Labels = mixedMoment B raw23313step1 raw23313step1Labels := by
      have ha : raw23313step1 = (fun i j => raw23313step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23313step1 raw23313step0; decide +kernel
      have hl : raw23313step1Labels = raw23313step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23313step0 raw23313step0Labels permutation39 permutation2
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical23314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23314 raw23314Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw23314 raw23314Labels = mixedMoment B raw23314step0 raw23314step0Labels := by
      have hz : ∀ j, raw23314 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw23314step0 = (fun i j => raw23314 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw23314step0 raw23314; decide +kernel
      have hl : raw23314step0Labels = raw23314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23314 raw23314Labels permutation590 hz
    mixedMoment B raw23314step0 raw23314step0Labels = mixedMoment B raw23314step1 raw23314step1Labels := by
      have hz : ∀ j, raw23314step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23314step1 = (fun i j => raw23314step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23314step1 raw23314step0; decide +kernel
      have hl : raw23314step1Labels = raw23314step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23314step0 raw23314step0Labels permutation80 hz
    mixedMoment B raw23314step1 raw23314step1Labels = mixedMoment B raw23314step2 raw23314step2Labels := by
      have ha : raw23314step2 = (fun i j => raw23314step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23314step2 raw23314step1; decide +kernel
      have hl : raw23314step2Labels = raw23314step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23314step1 raw23314step1Labels permutation10 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical23315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23315 raw23315Labels = mixedMoment B node2082 node2082Labels := by
  calc
    mixedMoment B raw23315 raw23315Labels = mixedMoment B raw23315step0 raw23315step0Labels := by
      have hz : ∀ j, raw23315 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23315step0 = (fun i j => raw23315 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23315step0 raw23315; decide +kernel
      have hl : raw23315step0Labels = raw23315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23315 raw23315Labels permutation346 hz
    mixedMoment B raw23315step0 raw23315step0Labels = mixedMoment B raw23315step1 raw23315step1Labels := by
      have ha : raw23315step1 = (fun i j => raw23315step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23315step1 raw23315step0; decide +kernel
      have hl : raw23315step1Labels = raw23315step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23315step0 raw23315step0Labels permutation33 permutation2
    _ = mixedMoment B node2082 node2082Labels := by rfl

theorem canonical23316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23316 raw23316Labels = mixedMoment B node1990 node1990Labels := by
  calc
    mixedMoment B raw23316 raw23316Labels = mixedMoment B raw23316step0 raw23316step0Labels := by
      have ha : raw23316step0 = (fun i j => raw23316 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23316step0 raw23316; decide +kernel
      have hl : raw23316step0Labels = raw23316Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23316 raw23316Labels permutation183 permutation2
    _ = mixedMoment B node1990 node1990Labels := by rfl

theorem canonical23317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23317 raw23317Labels = mixedMoment B node1918 node1918Labels := by
  calc
    mixedMoment B raw23317 raw23317Labels = mixedMoment B raw23317step0 raw23317step0Labels := by
      have hz : ∀ j, raw23317 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23317step0 = (fun i j => raw23317 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23317step0 raw23317; decide +kernel
      have hl : raw23317step0Labels = raw23317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23317 raw23317Labels permutation346 hz
    mixedMoment B raw23317step0 raw23317step0Labels = mixedMoment B raw23317step1 raw23317step1Labels := by
      have ha : raw23317step1 = (fun i j => raw23317step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23317step1 raw23317step0; decide +kernel
      have hl : raw23317step1Labels = raw23317step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23317step0 raw23317step0Labels permutation39 permutation2
    _ = mixedMoment B node1918 node1918Labels := by rfl

theorem canonical23318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23318 raw23318Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw23318 raw23318Labels = mixedMoment B raw23318step0 raw23318step0Labels := by
      have hz : ∀ j, raw23318 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23318step0 = (fun i j => raw23318 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23318step0 raw23318; decide +kernel
      have hl : raw23318step0Labels = raw23318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23318 raw23318Labels permutation346 hz
    mixedMoment B raw23318step0 raw23318step0Labels = mixedMoment B raw23318step1 raw23318step1Labels := by
      have ha : raw23318step1 = (fun i j => raw23318step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23318step1 raw23318step0; decide +kernel
      have hl : raw23318step1Labels = raw23318step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23318step0 raw23318step0Labels permutation39 permutation2
    _ = mixedMoment B node2205 node2205Labels := by rfl

theorem canonical23321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23321 raw23321Labels = mixedMoment B node889 node889Labels := by
  calc
    mixedMoment B raw23321 raw23321Labels = mixedMoment B raw23321step0 raw23321step0Labels := by
      have hz : ∀ j, raw23321 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23321step0 = (fun i j => raw23321 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23321step0 raw23321; decide +kernel
      have hl : raw23321step0Labels = raw23321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23321 raw23321Labels permutation346 hz
    mixedMoment B raw23321step0 raw23321step0Labels = mixedMoment B raw23321step1 raw23321step1Labels := by
      have ha : raw23321step1 = (fun i j => raw23321step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23321step1 raw23321step0; decide +kernel
      have hl : raw23321step1Labels = raw23321step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23321step0 raw23321step0Labels permutation39 permutation2
    _ = mixedMoment B node889 node889Labels := by rfl

theorem canonical23323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23323 raw23323Labels = mixedMoment B node866 node866Labels := by
  calc
    mixedMoment B raw23323 raw23323Labels = mixedMoment B raw23323step0 raw23323step0Labels := by
      have ha : raw23323step0 = (fun i j => raw23323 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23323step0 raw23323; decide +kernel
      have hl : raw23323step0Labels = raw23323Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23323 raw23323Labels permutation201 permutation2
    _ = mixedMoment B node866 node866Labels := by rfl

theorem canonical23324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23324 raw23324Labels = mixedMoment B node873 node873Labels := by
  calc
    mixedMoment B raw23324 raw23324Labels = mixedMoment B raw23324step0 raw23324step0Labels := by
      have hz : ∀ j, raw23324 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23324step0 = (fun i j => raw23324 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23324step0 raw23324; decide +kernel
      have hl : raw23324step0Labels = raw23324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23324 raw23324Labels permutation346 hz
    mixedMoment B raw23324step0 raw23324step0Labels = mixedMoment B raw23324step1 raw23324step1Labels := by
      have ha : raw23324step1 = (fun i j => raw23324step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23324step1 raw23324step0; decide +kernel
      have hl : raw23324step1Labels = raw23324step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23324step0 raw23324step0Labels permutation39 permutation2
    _ = mixedMoment B node873 node873Labels := by rfl

theorem canonical23325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23325 raw23325Labels = mixedMoment B node874 node874Labels := by
  calc
    mixedMoment B raw23325 raw23325Labels = mixedMoment B raw23325step0 raw23325step0Labels := by
      have hz : ∀ j, raw23325 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23325step0 = (fun i j => raw23325 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23325step0 raw23325; decide +kernel
      have hl : raw23325step0Labels = raw23325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23325 raw23325Labels permutation346 hz
    mixedMoment B raw23325step0 raw23325step0Labels = mixedMoment B raw23325step1 raw23325step1Labels := by
      have ha : raw23325step1 = (fun i j => raw23325step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23325step1 raw23325step0; decide +kernel
      have hl : raw23325step1Labels = raw23325step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23325step0 raw23325step0Labels permutation38 permutation2
    _ = mixedMoment B node874 node874Labels := by rfl

theorem canonical23326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23326 raw23326Labels = mixedMoment B node1618 node1618Labels := by
  calc
    mixedMoment B raw23326 raw23326Labels = mixedMoment B raw23326step0 raw23326step0Labels := by
      have hz : ∀ j, raw23326 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23326step0 = (fun i j => raw23326 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23326step0 raw23326; decide +kernel
      have hl : raw23326step0Labels = raw23326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23326 raw23326Labels permutation346 hz
    mixedMoment B raw23326step0 raw23326step0Labels = mixedMoment B raw23326step1 raw23326step1Labels := by
      have ha : raw23326step1 = (fun i j => raw23326step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23326step1 raw23326step0; decide +kernel
      have hl : raw23326step1Labels = raw23326step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23326step0 raw23326step0Labels permutation39 permutation4
    mixedMoment B raw23326step1 raw23326step1Labels = mixedMoment B raw23326step2 raw23326step2Labels := by
      have ha : raw23326step2 = -raw23326step1 := by apply Matrix.ext; change ∀ i j, raw23326step2 i j = -(raw23326step1 i j); unfold raw23326step2 raw23326step1; decide +kernel
      have hl : raw23326step2Labels = raw23326step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1618 node1618Labels := by rfl

theorem canonical23327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23327 raw23327Labels = mixedMoment B node724 node724Labels := by
  calc
    mixedMoment B raw23327 raw23327Labels = mixedMoment B raw23327step0 raw23327step0Labels := by
      have hz : ∀ j, raw23327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23327step0 = (fun i j => raw23327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23327step0 raw23327; decide +kernel
      have hl : raw23327step0Labels = raw23327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23327 raw23327Labels permutation346 hz
    mixedMoment B raw23327step0 raw23327step0Labels = mixedMoment B raw23327step1 raw23327step1Labels := by
      have ha : raw23327step1 = (fun i j => raw23327step0 (permutation42 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23327step1 raw23327step0; decide +kernel
      have hl : raw23327step1Labels = raw23327step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23327step0 raw23327step0Labels permutation42 permutation4
    mixedMoment B raw23327step1 raw23327step1Labels = mixedMoment B raw23327step2 raw23327step2Labels := by
      have ha : raw23327step2 = -raw23327step1 := by apply Matrix.ext; change ∀ i j, raw23327step2 i j = -(raw23327step1 i j); unfold raw23327step2 raw23327step1; decide +kernel
      have hl : raw23327step2Labels = raw23327step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node724 node724Labels := by rfl

theorem canonical23328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23328 raw23328Labels = mixedMoment B node710 node710Labels := by
  calc
    mixedMoment B raw23328 raw23328Labels = mixedMoment B raw23328step0 raw23328step0Labels := by
      have ha : raw23328step0 = (fun i j => raw23328 (permutation201 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23328step0 raw23328; decide +kernel
      have hl : raw23328step0Labels = raw23328Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23328 raw23328Labels permutation201 permutation4
    mixedMoment B raw23328step0 raw23328step0Labels = mixedMoment B raw23328step1 raw23328step1Labels := by
      have ha : raw23328step1 = -raw23328step0 := by apply Matrix.ext; change ∀ i j, raw23328step1 i j = -(raw23328step0 i j); unfold raw23328step1 raw23328step0; decide +kernel
      have hl : raw23328step1Labels = raw23328step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node710 node710Labels := by rfl

theorem canonical23329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23329 raw23329Labels = mixedMoment B node852 node852Labels := by
  calc
    mixedMoment B raw23329 raw23329Labels = mixedMoment B raw23329step0 raw23329step0Labels := by
      have hz : ∀ j, raw23329 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23329step0 = (fun i j => raw23329 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23329step0 raw23329; decide +kernel
      have hl : raw23329step0Labels = raw23329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23329 raw23329Labels permutation434 hz
    mixedMoment B raw23329step0 raw23329step0Labels = mixedMoment B raw23329step1 raw23329step1Labels := by
      have hz : ∀ j, raw23329step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23329step1 = (fun i j => raw23329step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23329step1 raw23329step0; decide +kernel
      have hl : raw23329step1Labels = raw23329step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23329step0 raw23329step0Labels permutation80 hz
    mixedMoment B raw23329step1 raw23329step1Labels = mixedMoment B raw23329step2 raw23329step2Labels := by
      have ha : raw23329step2 = (fun i j => raw23329step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23329step2 raw23329step1; decide +kernel
      have hl : raw23329step2Labels = raw23329step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23329step1 raw23329step1Labels permutation9 permutation4
    mixedMoment B raw23329step2 raw23329step2Labels = mixedMoment B raw23329step3 raw23329step3Labels := by
      have ha : raw23329step3 = -raw23329step2 := by apply Matrix.ext; change ∀ i j, raw23329step3 i j = -(raw23329step2 i j); unfold raw23329step3 raw23329step2; decide +kernel
      have hl : raw23329step3Labels = raw23329step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node852 node852Labels := by rfl

theorem canonical23330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23330 raw23330Labels = mixedMoment B node715 node715Labels := by
  calc
    mixedMoment B raw23330 raw23330Labels = mixedMoment B raw23330step0 raw23330step0Labels := by
      have hz : ∀ j, raw23330 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23330step0 = (fun i j => raw23330 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23330step0 raw23330; decide +kernel
      have hl : raw23330step0Labels = raw23330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23330 raw23330Labels permutation346 hz
    mixedMoment B raw23330step0 raw23330step0Labels = mixedMoment B raw23330step1 raw23330step1Labels := by
      have ha : raw23330step1 = (fun i j => raw23330step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23330step1 raw23330step0; decide +kernel
      have hl : raw23330step1Labels = raw23330step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23330step0 raw23330step0Labels permutation39 permutation4
    mixedMoment B raw23330step1 raw23330step1Labels = mixedMoment B raw23330step2 raw23330step2Labels := by
      have ha : raw23330step2 = -raw23330step1 := by apply Matrix.ext; change ∀ i j, raw23330step2 i j = -(raw23330step1 i j); unfold raw23330step2 raw23330step1; decide +kernel
      have hl : raw23330step2Labels = raw23330step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node715 node715Labels := by rfl

theorem canonical23331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23331 raw23331Labels = mixedMoment B node717 node717Labels := by
  calc
    mixedMoment B raw23331 raw23331Labels = mixedMoment B raw23331step0 raw23331step0Labels := by
      have hz : ∀ j, raw23331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23331step0 = (fun i j => raw23331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23331step0 raw23331; decide +kernel
      have hl : raw23331step0Labels = raw23331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23331 raw23331Labels permutation346 hz
    mixedMoment B raw23331step0 raw23331step0Labels = mixedMoment B raw23331step1 raw23331step1Labels := by
      have ha : raw23331step1 = (fun i j => raw23331step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23331step1 raw23331step0; decide +kernel
      have hl : raw23331step1Labels = raw23331step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23331step0 raw23331step0Labels permutation38 permutation4
    mixedMoment B raw23331step1 raw23331step1Labels = mixedMoment B raw23331step2 raw23331step2Labels := by
      have ha : raw23331step2 = -raw23331step1 := by apply Matrix.ext; change ∀ i j, raw23331step2 i j = -(raw23331step1 i j); unfold raw23331step2 raw23331step1; decide +kernel
      have hl : raw23331step2Labels = raw23331step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node717 node717Labels := by rfl

theorem canonical23333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23333 raw23333Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw23333 raw23333Labels = mixedMoment B raw23333step0 raw23333step0Labels := by
      have hz : ∀ j, raw23333 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23333step0 = (fun i j => raw23333 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23333step0 raw23333; decide +kernel
      have hl : raw23333step0Labels = raw23333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23333 raw23333Labels permutation434 hz
    mixedMoment B raw23333step0 raw23333step0Labels = mixedMoment B raw23333step1 raw23333step1Labels := by
      have hz : ∀ j, raw23333step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23333step1 = (fun i j => raw23333step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23333step1 raw23333step0; decide +kernel
      have hl : raw23333step1Labels = raw23333step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23333step0 raw23333step0Labels permutation80 hz
    mixedMoment B raw23333step1 raw23333step1Labels = mixedMoment B raw23333step2 raw23333step2Labels := by
      have ha : raw23333step2 = (fun i j => raw23333step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23333step2 raw23333step1; decide +kernel
      have hl : raw23333step2Labels = raw23333step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23333step1 raw23333step1Labels permutation9 permutation2
    _ = mixedMoment B node4845 node4845Labels := by rfl

theorem canonical23334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23334 raw23334Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw23334 raw23334Labels = mixedMoment B raw23334step0 raw23334step0Labels := by
      have hz : ∀ j, raw23334 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23334step0 = (fun i j => raw23334 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23334step0 raw23334; decide +kernel
      have hl : raw23334step0Labels = raw23334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23334 raw23334Labels permutation434 hz
    mixedMoment B raw23334step0 raw23334step0Labels = mixedMoment B raw23334step1 raw23334step1Labels := by
      have hz : ∀ j, raw23334step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23334step1 = (fun i j => raw23334step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23334step1 raw23334step0; decide +kernel
      have hl : raw23334step1Labels = raw23334step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23334step0 raw23334step0Labels permutation56 hz
    mixedMoment B raw23334step1 raw23334step1Labels = mixedMoment B raw23334step2 raw23334step2Labels := by
      have ha : raw23334step2 = (fun i j => raw23334step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23334step2 raw23334step1; decide +kernel
      have hl : raw23334step2Labels = raw23334step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23334step1 raw23334step1Labels permutation9 permutation2
    _ = mixedMoment B node4845 node4845Labels := by rfl

theorem canonical23335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23335 raw23335Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw23335 raw23335Labels = mixedMoment B raw23335step0 raw23335step0Labels := by
      have hz : ∀ j, raw23335 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23335step0 = (fun i j => raw23335 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23335step0 raw23335; decide +kernel
      have hl : raw23335step0Labels = raw23335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23335 raw23335Labels permutation346 hz
    mixedMoment B raw23335step0 raw23335step0Labels = mixedMoment B raw23335step1 raw23335step1Labels := by
      have hz : ∀ j, raw23335step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23335step1 = (fun i j => raw23335step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23335step1 raw23335step0; decide +kernel
      have hl : raw23335step1Labels = raw23335step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23335step0 raw23335step0Labels permutation56 hz
    mixedMoment B raw23335step1 raw23335step1Labels = mixedMoment B raw23335step2 raw23335step2Labels := by
      have ha : raw23335step2 = (fun i j => raw23335step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23335step2 raw23335step1; decide +kernel
      have hl : raw23335step2Labels = raw23335step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23335step1 raw23335step1Labels permutation9 permutation2
    _ = mixedMoment B node4845 node4845Labels := by rfl

theorem canonical23336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23336 raw23336Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw23336 raw23336Labels = mixedMoment B raw23336step0 raw23336step0Labels := by
      have hz : ∀ j, raw23336 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23336step0 = (fun i j => raw23336 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23336step0 raw23336; decide +kernel
      have hl : raw23336step0Labels = raw23336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23336 raw23336Labels permutation434 hz
    mixedMoment B raw23336step0 raw23336step0Labels = mixedMoment B raw23336step1 raw23336step1Labels := by
      have hz : ∀ j, raw23336step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23336step1 = (fun i j => raw23336step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23336step1 raw23336step0; decide +kernel
      have hl : raw23336step1Labels = raw23336step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23336step0 raw23336step0Labels permutation80 hz
    mixedMoment B raw23336step1 raw23336step1Labels = mixedMoment B raw23336step2 raw23336step2Labels := by
      have hz : ∀ j, raw23336step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23336step2 = (fun i j => raw23336step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23336step2 raw23336step1; decide +kernel
      have hl : raw23336step2Labels = raw23336step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23336step1 raw23336step1Labels permutation14 hz
    mixedMoment B raw23336step2 raw23336step2Labels = mixedMoment B raw23336step3 raw23336step3Labels := by
      have ha : raw23336step3 = (fun i j => raw23336step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23336step3 raw23336step2; decide +kernel
      have hl : raw23336step3Labels = raw23336step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23336step2 raw23336step2Labels permutation3 permutation7
    mixedMoment B raw23336step3 raw23336step3Labels = mixedMoment B raw23336step4 raw23336step4Labels := by
      have ha : raw23336step4 = -raw23336step3 := by apply Matrix.ext; change ∀ i j, raw23336step4 i j = -(raw23336step3 i j); unfold raw23336step4 raw23336step3; decide +kernel
      have hl : raw23336step4Labels = raw23336step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23336step4 raw23336step4Labels = mixedMoment B raw23336step5 raw23336step5Labels := by
      have ha : raw23336step5 = raw23336step4 := by apply Matrix.ext; unfold raw23336step5 raw23336step4; decide +kernel
      have hl : raw23336step4Labels = labelEmbedding10 ∘ raw23336step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23336step4 raw23336step4Labels raw23336step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

theorem canonical23337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23337 raw23337Labels = mixedMoment B node4179 node4179Labels := by
  calc
    mixedMoment B raw23337 raw23337Labels = mixedMoment B raw23337step0 raw23337step0Labels := by
      have hz : ∀ j, raw23337 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23337step0 = (fun i j => raw23337 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23337step0 raw23337; decide +kernel
      have hl : raw23337step0Labels = raw23337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23337 raw23337Labels permutation434 hz
    mixedMoment B raw23337step0 raw23337step0Labels = mixedMoment B raw23337step1 raw23337step1Labels := by
      have hz : ∀ j, raw23337step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23337step1 = (fun i j => raw23337step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23337step1 raw23337step0; decide +kernel
      have hl : raw23337step1Labels = raw23337step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23337step0 raw23337step0Labels permutation80 hz
    mixedMoment B raw23337step1 raw23337step1Labels = mixedMoment B raw23337step2 raw23337step2Labels := by
      have ha : raw23337step2 = (fun i j => raw23337step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23337step2 raw23337step1; decide +kernel
      have hl : raw23337step2Labels = raw23337step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23337step1 raw23337step1Labels permutation9 permutation2
    _ = mixedMoment B node4179 node4179Labels := by rfl

theorem canonical23338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23338 raw23338Labels = mixedMoment B node4348 node4348Labels := by
  calc
    mixedMoment B raw23338 raw23338Labels = mixedMoment B raw23338step0 raw23338step0Labels := by
      have hz : ∀ j, raw23338 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23338step0 = (fun i j => raw23338 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23338step0 raw23338; decide +kernel
      have hl : raw23338step0Labels = raw23338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23338 raw23338Labels permutation434 hz
    mixedMoment B raw23338step0 raw23338step0Labels = mixedMoment B raw23338step1 raw23338step1Labels := by
      have ha : raw23338step1 = (fun i j => raw23338step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23338step1 raw23338step0; decide +kernel
      have hl : raw23338step1Labels = raw23338step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23338step0 raw23338step0Labels permutation39 permutation2
    _ = mixedMoment B node4348 node4348Labels := by rfl

theorem canonical23339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23339 raw23339Labels = mixedMoment B node4348 node4348Labels := by
  calc
    mixedMoment B raw23339 raw23339Labels = mixedMoment B raw23339step0 raw23339step0Labels := by
      have hz : ∀ j, raw23339 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23339step0 = (fun i j => raw23339 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23339step0 raw23339; decide +kernel
      have hl : raw23339step0Labels = raw23339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23339 raw23339Labels permutation346 hz
    mixedMoment B raw23339step0 raw23339step0Labels = mixedMoment B raw23339step1 raw23339step1Labels := by
      have ha : raw23339step1 = (fun i j => raw23339step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23339step1 raw23339step0; decide +kernel
      have hl : raw23339step1Labels = raw23339step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23339step0 raw23339step0Labels permutation39 permutation2
    _ = mixedMoment B node4348 node4348Labels := by rfl

theorem canonical23340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23340 raw23340Labels = mixedMoment B node4500 node4500Labels := by
  calc
    mixedMoment B raw23340 raw23340Labels = mixedMoment B raw23340step0 raw23340step0Labels := by
      have hz : ∀ j, raw23340 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23340step0 = (fun i j => raw23340 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23340step0 raw23340; decide +kernel
      have hl : raw23340step0Labels = raw23340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23340 raw23340Labels permutation434 hz
    mixedMoment B raw23340step0 raw23340step0Labels = mixedMoment B raw23340step1 raw23340step1Labels := by
      have hz : ∀ j, raw23340step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23340step1 = (fun i j => raw23340step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23340step1 raw23340step0; decide +kernel
      have hl : raw23340step1Labels = raw23340step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23340step0 raw23340step0Labels permutation80 hz
    _ = mixedMoment B node4500 node4500Labels := by rfl

theorem canonical23341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23341 raw23341Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw23341 raw23341Labels = mixedMoment B raw23341step0 raw23341step0Labels := by
      have hz : ∀ j, raw23341 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23341step0 = (fun i j => raw23341 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23341step0 raw23341; decide +kernel
      have hl : raw23341step0Labels = raw23341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23341 raw23341Labels permutation434 hz
    mixedMoment B raw23341step0 raw23341step0Labels = mixedMoment B raw23341step1 raw23341step1Labels := by
      have hz : ∀ j, raw23341step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23341step1 = (fun i j => raw23341step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23341step1 raw23341step0; decide +kernel
      have hl : raw23341step1Labels = raw23341step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23341step0 raw23341step0Labels permutation80 hz
    mixedMoment B raw23341step1 raw23341step1Labels = mixedMoment B raw23341step2 raw23341step2Labels := by
      have ha : raw23341step2 = (fun i j => raw23341step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23341step2 raw23341step1; decide +kernel
      have hl : raw23341step2Labels = raw23341step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23341step1 raw23341step1Labels permutation9 permutation2
    _ = mixedMoment B node4496 node4496Labels := by rfl

theorem canonical23342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23342 raw23342Labels = mixedMoment B node4179 node4179Labels := by
  calc
    mixedMoment B raw23342 raw23342Labels = mixedMoment B raw23342step0 raw23342step0Labels := by
      have hz : ∀ j, raw23342 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23342step0 = (fun i j => raw23342 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23342step0 raw23342; decide +kernel
      have hl : raw23342step0Labels = raw23342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23342 raw23342Labels permutation434 hz
    mixedMoment B raw23342step0 raw23342step0Labels = mixedMoment B raw23342step1 raw23342step1Labels := by
      have hz : ∀ j, raw23342step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23342step1 = (fun i j => raw23342step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23342step1 raw23342step0; decide +kernel
      have hl : raw23342step1Labels = raw23342step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23342step0 raw23342step0Labels permutation56 hz
    mixedMoment B raw23342step1 raw23342step1Labels = mixedMoment B raw23342step2 raw23342step2Labels := by
      have ha : raw23342step2 = (fun i j => raw23342step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23342step2 raw23342step1; decide +kernel
      have hl : raw23342step2Labels = raw23342step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23342step1 raw23342step1Labels permutation9 permutation2
    _ = mixedMoment B node4179 node4179Labels := by rfl

theorem canonical23343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23343 raw23343Labels = mixedMoment B node4348 node4348Labels := by
  calc
    mixedMoment B raw23343 raw23343Labels = mixedMoment B raw23343step0 raw23343step0Labels := by
      have hz : ∀ j, raw23343 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23343step0 = (fun i j => raw23343 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23343step0 raw23343; decide +kernel
      have hl : raw23343step0Labels = raw23343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23343 raw23343Labels permutation434 hz
    mixedMoment B raw23343step0 raw23343step0Labels = mixedMoment B raw23343step1 raw23343step1Labels := by
      have ha : raw23343step1 = (fun i j => raw23343step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23343step1 raw23343step0; decide +kernel
      have hl : raw23343step1Labels = raw23343step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23343step0 raw23343step0Labels permutation33 permutation2
    _ = mixedMoment B node4348 node4348Labels := by rfl

theorem canonical23344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23344 raw23344Labels = mixedMoment B node4348 node4348Labels := by
  calc
    mixedMoment B raw23344 raw23344Labels = mixedMoment B raw23344step0 raw23344step0Labels := by
      have hz : ∀ j, raw23344 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23344step0 = (fun i j => raw23344 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23344step0 raw23344; decide +kernel
      have hl : raw23344step0Labels = raw23344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23344 raw23344Labels permutation265 hz
    mixedMoment B raw23344step0 raw23344step0Labels = mixedMoment B raw23344step1 raw23344step1Labels := by
      have ha : raw23344step1 = (fun i j => raw23344step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23344step1 raw23344step0; decide +kernel
      have hl : raw23344step1Labels = raw23344step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23344step0 raw23344step0Labels permutation39 permutation2
    _ = mixedMoment B node4348 node4348Labels := by rfl

theorem canonical23345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23345 raw23345Labels = mixedMoment B node4500 node4500Labels := by
  calc
    mixedMoment B raw23345 raw23345Labels = mixedMoment B raw23345step0 raw23345step0Labels := by
      have hz : ∀ j, raw23345 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23345step0 = (fun i j => raw23345 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23345step0 raw23345; decide +kernel
      have hl : raw23345step0Labels = raw23345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23345 raw23345Labels permutation434 hz
    mixedMoment B raw23345step0 raw23345step0Labels = mixedMoment B raw23345step1 raw23345step1Labels := by
      have hz : ∀ j, raw23345step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23345step1 = (fun i j => raw23345step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23345step1 raw23345step0; decide +kernel
      have hl : raw23345step1Labels = raw23345step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23345step0 raw23345step0Labels permutation56 hz
    _ = mixedMoment B node4500 node4500Labels := by rfl

theorem canonical23346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23346 raw23346Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw23346 raw23346Labels = mixedMoment B raw23346step0 raw23346step0Labels := by
      have hz : ∀ j, raw23346 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23346step0 = (fun i j => raw23346 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23346step0 raw23346; decide +kernel
      have hl : raw23346step0Labels = raw23346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23346 raw23346Labels permutation434 hz
    mixedMoment B raw23346step0 raw23346step0Labels = mixedMoment B raw23346step1 raw23346step1Labels := by
      have hz : ∀ j, raw23346step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23346step1 = (fun i j => raw23346step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23346step1 raw23346step0; decide +kernel
      have hl : raw23346step1Labels = raw23346step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23346step0 raw23346step0Labels permutation56 hz
    mixedMoment B raw23346step1 raw23346step1Labels = mixedMoment B raw23346step2 raw23346step2Labels := by
      have ha : raw23346step2 = (fun i j => raw23346step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23346step2 raw23346step1; decide +kernel
      have hl : raw23346step2Labels = raw23346step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23346step1 raw23346step1Labels permutation9 permutation2
    _ = mixedMoment B node4496 node4496Labels := by rfl

theorem canonical23347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23347 raw23347Labels = mixedMoment B node4179 node4179Labels := by
  calc
    mixedMoment B raw23347 raw23347Labels = mixedMoment B raw23347step0 raw23347step0Labels := by
      have hz : ∀ j, raw23347 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23347step0 = (fun i j => raw23347 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23347step0 raw23347; decide +kernel
      have hl : raw23347step0Labels = raw23347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23347 raw23347Labels permutation346 hz
    mixedMoment B raw23347step0 raw23347step0Labels = mixedMoment B raw23347step1 raw23347step1Labels := by
      have hz : ∀ j, raw23347step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23347step1 = (fun i j => raw23347step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23347step1 raw23347step0; decide +kernel
      have hl : raw23347step1Labels = raw23347step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23347step0 raw23347step0Labels permutation56 hz
    mixedMoment B raw23347step1 raw23347step1Labels = mixedMoment B raw23347step2 raw23347step2Labels := by
      have ha : raw23347step2 = (fun i j => raw23347step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23347step2 raw23347step1; decide +kernel
      have hl : raw23347step2Labels = raw23347step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23347step1 raw23347step1Labels permutation9 permutation2
    _ = mixedMoment B node4179 node4179Labels := by rfl

theorem canonical23348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23348 raw23348Labels = mixedMoment B node4348 node4348Labels := by
  calc
    mixedMoment B raw23348 raw23348Labels = mixedMoment B raw23348step0 raw23348step0Labels := by
      have hz : ∀ j, raw23348 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23348step0 = (fun i j => raw23348 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23348step0 raw23348; decide +kernel
      have hl : raw23348step0Labels = raw23348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23348 raw23348Labels permutation346 hz
    mixedMoment B raw23348step0 raw23348step0Labels = mixedMoment B raw23348step1 raw23348step1Labels := by
      have ha : raw23348step1 = (fun i j => raw23348step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23348step1 raw23348step0; decide +kernel
      have hl : raw23348step1Labels = raw23348step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23348step0 raw23348step0Labels permutation33 permutation2
    _ = mixedMoment B node4348 node4348Labels := by rfl

theorem canonical23349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23349 raw23349Labels = mixedMoment B node4348 node4348Labels := by
  calc
    mixedMoment B raw23349 raw23349Labels = mixedMoment B raw23349step0 raw23349step0Labels := by
      have hz : ∀ j, raw23349 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23349step0 = (fun i j => raw23349 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23349step0 raw23349; decide +kernel
      have hl : raw23349step0Labels = raw23349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23349 raw23349Labels permutation265 hz
    mixedMoment B raw23349step0 raw23349step0Labels = mixedMoment B raw23349step1 raw23349step1Labels := by
      have ha : raw23349step1 = (fun i j => raw23349step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23349step1 raw23349step0; decide +kernel
      have hl : raw23349step1Labels = raw23349step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23349step0 raw23349step0Labels permutation33 permutation2
    _ = mixedMoment B node4348 node4348Labels := by rfl

theorem canonical23350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23350 raw23350Labels = mixedMoment B node4500 node4500Labels := by
  calc
    mixedMoment B raw23350 raw23350Labels = mixedMoment B raw23350step0 raw23350step0Labels := by
      have hz : ∀ j, raw23350 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23350step0 = (fun i j => raw23350 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23350step0 raw23350; decide +kernel
      have hl : raw23350step0Labels = raw23350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23350 raw23350Labels permutation346 hz
    mixedMoment B raw23350step0 raw23350step0Labels = mixedMoment B raw23350step1 raw23350step1Labels := by
      have hz : ∀ j, raw23350step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23350step1 = (fun i j => raw23350step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23350step1 raw23350step0; decide +kernel
      have hl : raw23350step1Labels = raw23350step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23350step0 raw23350step0Labels permutation56 hz
    _ = mixedMoment B node4500 node4500Labels := by rfl

theorem canonical23351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23351 raw23351Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw23351 raw23351Labels = mixedMoment B raw23351step0 raw23351step0Labels := by
      have hz : ∀ j, raw23351 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23351step0 = (fun i j => raw23351 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23351step0 raw23351; decide +kernel
      have hl : raw23351step0Labels = raw23351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23351 raw23351Labels permutation346 hz
    mixedMoment B raw23351step0 raw23351step0Labels = mixedMoment B raw23351step1 raw23351step1Labels := by
      have hz : ∀ j, raw23351step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23351step1 = (fun i j => raw23351step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23351step1 raw23351step0; decide +kernel
      have hl : raw23351step1Labels = raw23351step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23351step0 raw23351step0Labels permutation56 hz
    mixedMoment B raw23351step1 raw23351step1Labels = mixedMoment B raw23351step2 raw23351step2Labels := by
      have ha : raw23351step2 = (fun i j => raw23351step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23351step2 raw23351step1; decide +kernel
      have hl : raw23351step2Labels = raw23351step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23351step1 raw23351step1Labels permutation9 permutation2
    _ = mixedMoment B node4496 node4496Labels := by rfl

theorem canonical23352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23352 raw23352Labels = mixedMoment B node4190 node4190Labels := by
  calc
    mixedMoment B raw23352 raw23352Labels = mixedMoment B raw23352step0 raw23352step0Labels := by
      have hz : ∀ j, raw23352 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23352step0 = (fun i j => raw23352 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23352step0 raw23352; decide +kernel
      have hl : raw23352step0Labels = raw23352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23352 raw23352Labels permutation434 hz
    mixedMoment B raw23352step0 raw23352step0Labels = mixedMoment B raw23352step1 raw23352step1Labels := by
      have hz : ∀ j, raw23352step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23352step1 = (fun i j => raw23352step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23352step1 raw23352step0; decide +kernel
      have hl : raw23352step1Labels = raw23352step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23352step0 raw23352step0Labels permutation80 hz
    mixedMoment B raw23352step1 raw23352step1Labels = mixedMoment B raw23352step2 raw23352step2Labels := by
      have hz : ∀ j, raw23352step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23352step2 = (fun i j => raw23352step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23352step2 raw23352step1; decide +kernel
      have hl : raw23352step2Labels = raw23352step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23352step1 raw23352step1Labels permutation14 hz
    mixedMoment B raw23352step2 raw23352step2Labels = mixedMoment B raw23352step3 raw23352step3Labels := by
      have ha : raw23352step3 = (fun i j => raw23352step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23352step3 raw23352step2; decide +kernel
      have hl : raw23352step3Labels = raw23352step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23352step2 raw23352step2Labels permutation3 permutation2
    _ = mixedMoment B node4190 node4190Labels := by rfl

theorem canonical23353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23353 raw23353Labels = mixedMoment B node4359 node4359Labels := by
  calc
    mixedMoment B raw23353 raw23353Labels = mixedMoment B raw23353step0 raw23353step0Labels := by
      have hz : ∀ j, raw23353 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23353step0 = (fun i j => raw23353 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23353step0 raw23353; decide +kernel
      have hl : raw23353step0Labels = raw23353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23353 raw23353Labels permutation434 hz
    mixedMoment B raw23353step0 raw23353step0Labels = mixedMoment B raw23353step1 raw23353step1Labels := by
      have hz : ∀ j, raw23353step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23353step1 = (fun i j => raw23353step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23353step1 raw23353step0; decide +kernel
      have hl : raw23353step1Labels = raw23353step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23353step0 raw23353step0Labels permutation80 hz
    mixedMoment B raw23353step1 raw23353step1Labels = mixedMoment B raw23353step2 raw23353step2Labels := by
      have ha : raw23353step2 = (fun i j => raw23353step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23353step2 raw23353step1; decide +kernel
      have hl : raw23353step2Labels = raw23353step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23353step1 raw23353step1Labels permutation9 permutation2
    _ = mixedMoment B node4359 node4359Labels := by rfl

theorem canonical23354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23354 raw23354Labels = mixedMoment B node4359 node4359Labels := by
  calc
    mixedMoment B raw23354 raw23354Labels = mixedMoment B raw23354step0 raw23354step0Labels := by
      have hz : ∀ j, raw23354 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23354step0 = (fun i j => raw23354 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23354step0 raw23354; decide +kernel
      have hl : raw23354step0Labels = raw23354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23354 raw23354Labels permutation434 hz
    mixedMoment B raw23354step0 raw23354step0Labels = mixedMoment B raw23354step1 raw23354step1Labels := by
      have hz : ∀ j, raw23354step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23354step1 = (fun i j => raw23354step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23354step1 raw23354step0; decide +kernel
      have hl : raw23354step1Labels = raw23354step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23354step0 raw23354step0Labels permutation56 hz
    mixedMoment B raw23354step1 raw23354step1Labels = mixedMoment B raw23354step2 raw23354step2Labels := by
      have ha : raw23354step2 = (fun i j => raw23354step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23354step2 raw23354step1; decide +kernel
      have hl : raw23354step2Labels = raw23354step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23354step1 raw23354step1Labels permutation9 permutation2
    _ = mixedMoment B node4359 node4359Labels := by rfl

theorem canonical23355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23355 raw23355Labels = mixedMoment B node4359 node4359Labels := by
  calc
    mixedMoment B raw23355 raw23355Labels = mixedMoment B raw23355step0 raw23355step0Labels := by
      have hz : ∀ j, raw23355 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23355step0 = (fun i j => raw23355 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23355step0 raw23355; decide +kernel
      have hl : raw23355step0Labels = raw23355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23355 raw23355Labels permutation346 hz
    mixedMoment B raw23355step0 raw23355step0Labels = mixedMoment B raw23355step1 raw23355step1Labels := by
      have hz : ∀ j, raw23355step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23355step1 = (fun i j => raw23355step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23355step1 raw23355step0; decide +kernel
      have hl : raw23355step1Labels = raw23355step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23355step0 raw23355step0Labels permutation56 hz
    mixedMoment B raw23355step1 raw23355step1Labels = mixedMoment B raw23355step2 raw23355step2Labels := by
      have ha : raw23355step2 = (fun i j => raw23355step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23355step2 raw23355step1; decide +kernel
      have hl : raw23355step2Labels = raw23355step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23355step1 raw23355step1Labels permutation9 permutation2
    _ = mixedMoment B node4359 node4359Labels := by rfl

theorem canonical23356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23356 raw23356Labels = mixedMoment B node4501 node4501Labels := by
  calc
    mixedMoment B raw23356 raw23356Labels = mixedMoment B raw23356step0 raw23356step0Labels := by
      have hz : ∀ j, raw23356 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23356step0 = (fun i j => raw23356 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23356step0 raw23356; decide +kernel
      have hl : raw23356step0Labels = raw23356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23356 raw23356Labels permutation434 hz
    mixedMoment B raw23356step0 raw23356step0Labels = mixedMoment B raw23356step1 raw23356step1Labels := by
      have hz : ∀ j, raw23356step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23356step1 = (fun i j => raw23356step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23356step1 raw23356step0; decide +kernel
      have hl : raw23356step1Labels = raw23356step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23356step0 raw23356step0Labels permutation80 hz
    mixedMoment B raw23356step1 raw23356step1Labels = mixedMoment B raw23356step2 raw23356step2Labels := by
      have hz : ∀ j, raw23356step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23356step2 = (fun i j => raw23356step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23356step2 raw23356step1; decide +kernel
      have hl : raw23356step2Labels = raw23356step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23356step1 raw23356step1Labels permutation14 hz
    mixedMoment B raw23356step2 raw23356step2Labels = mixedMoment B raw23356step3 raw23356step3Labels := by
      have ha : raw23356step3 = (fun i j => raw23356step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23356step3 raw23356step2; decide +kernel
      have hl : raw23356step3Labels = raw23356step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23356step2 raw23356step2Labels permutation3 permutation2
    _ = mixedMoment B node4501 node4501Labels := by rfl

theorem canonical23357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23357 raw23357Labels = mixedMoment B node4193 node4193Labels := by
  calc
    mixedMoment B raw23357 raw23357Labels = mixedMoment B raw23357step0 raw23357step0Labels := by
      have hz : ∀ j, raw23357 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23357step0 = (fun i j => raw23357 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23357step0 raw23357; decide +kernel
      have hl : raw23357step0Labels = raw23357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23357 raw23357Labels permutation434 hz
    mixedMoment B raw23357step0 raw23357step0Labels = mixedMoment B raw23357step1 raw23357step1Labels := by
      have hz : ∀ j, raw23357step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23357step1 = (fun i j => raw23357step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23357step1 raw23357step0; decide +kernel
      have hl : raw23357step1Labels = raw23357step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23357step0 raw23357step0Labels permutation80 hz
    mixedMoment B raw23357step1 raw23357step1Labels = mixedMoment B raw23357step2 raw23357step2Labels := by
      have hz : ∀ j, raw23357step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23357step2 = (fun i j => raw23357step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23357step2 raw23357step1; decide +kernel
      have hl : raw23357step2Labels = raw23357step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23357step1 raw23357step1Labels permutation14 hz
    _ = mixedMoment B node4193 node4193Labels := by rfl

theorem canonical23358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23358 raw23358Labels = mixedMoment B node4362 node4362Labels := by
  calc
    mixedMoment B raw23358 raw23358Labels = mixedMoment B raw23358step0 raw23358step0Labels := by
      have hz : ∀ j, raw23358 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23358step0 = (fun i j => raw23358 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23358step0 raw23358; decide +kernel
      have hl : raw23358step0Labels = raw23358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23358 raw23358Labels permutation434 hz
    mixedMoment B raw23358step0 raw23358step0Labels = mixedMoment B raw23358step1 raw23358step1Labels := by
      have hz : ∀ j, raw23358step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23358step1 = (fun i j => raw23358step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23358step1 raw23358step0; decide +kernel
      have hl : raw23358step1Labels = raw23358step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23358step0 raw23358step0Labels permutation80 hz
    _ = mixedMoment B node4362 node4362Labels := by rfl

theorem canonical23359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23359 raw23359Labels = mixedMoment B node4362 node4362Labels := by
  calc
    mixedMoment B raw23359 raw23359Labels = mixedMoment B raw23359step0 raw23359step0Labels := by
      have hz : ∀ j, raw23359 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23359step0 = (fun i j => raw23359 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23359step0 raw23359; decide +kernel
      have hl : raw23359step0Labels = raw23359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23359 raw23359Labels permutation434 hz
    mixedMoment B raw23359step0 raw23359step0Labels = mixedMoment B raw23359step1 raw23359step1Labels := by
      have hz : ∀ j, raw23359step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23359step1 = (fun i j => raw23359step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23359step1 raw23359step0; decide +kernel
      have hl : raw23359step1Labels = raw23359step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23359step0 raw23359step0Labels permutation56 hz
    _ = mixedMoment B node4362 node4362Labels := by rfl

theorem canonical23360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23360 raw23360Labels = mixedMoment B node4362 node4362Labels := by
  calc
    mixedMoment B raw23360 raw23360Labels = mixedMoment B raw23360step0 raw23360step0Labels := by
      have hz : ∀ j, raw23360 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23360step0 = (fun i j => raw23360 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23360step0 raw23360; decide +kernel
      have hl : raw23360step0Labels = raw23360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23360 raw23360Labels permutation346 hz
    mixedMoment B raw23360step0 raw23360step0Labels = mixedMoment B raw23360step1 raw23360step1Labels := by
      have hz : ∀ j, raw23360step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23360step1 = (fun i j => raw23360step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23360step1 raw23360step0; decide +kernel
      have hl : raw23360step1Labels = raw23360step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23360step0 raw23360step0Labels permutation56 hz
    _ = mixedMoment B node4362 node4362Labels := by rfl

theorem canonical23389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23389 raw23389Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw23389 raw23389Labels = mixedMoment B raw23389step0 raw23389step0Labels := by
      have hz : ∀ j, raw23389 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23389step0 = (fun i j => raw23389 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23389step0 raw23389; decide +kernel
      have hl : raw23389step0Labels = raw23389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23389 raw23389Labels permutation434 hz
    mixedMoment B raw23389step0 raw23389step0Labels = mixedMoment B raw23389step1 raw23389step1Labels := by
      have hz : ∀ j, raw23389step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23389step1 = (fun i j => raw23389step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23389step1 raw23389step0; decide +kernel
      have hl : raw23389step1Labels = raw23389step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23389step0 raw23389step0Labels permutation80 hz
    mixedMoment B raw23389step1 raw23389step1Labels = mixedMoment B raw23389step2 raw23389step2Labels := by
      have ha : raw23389step2 = (fun i j => raw23389step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23389step2 raw23389step1; decide +kernel
      have hl : raw23389step2Labels = raw23389step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23389step1 raw23389step1Labels permutation9 permutation7
    mixedMoment B raw23389step2 raw23389step2Labels = mixedMoment B raw23389step3 raw23389step3Labels := by
      have ha : raw23389step3 = -raw23389step2 := by apply Matrix.ext; change ∀ i j, raw23389step3 i j = -(raw23389step2 i j); unfold raw23389step3 raw23389step2; decide +kernel
      have hl : raw23389step3Labels = raw23389step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23389step3 raw23389step3Labels = mixedMoment B raw23389step4 raw23389step4Labels := by
      have ha : raw23389step4 = raw23389step3 := by apply Matrix.ext; unfold raw23389step4 raw23389step3; decide +kernel
      have hl : raw23389step3Labels = labelEmbedding1 ∘ raw23389step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23389step3 raw23389step3Labels raw23389step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2218 node2218Labels := by rfl

theorem canonical23390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23390 raw23390Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw23390 raw23390Labels = mixedMoment B raw23390step0 raw23390step0Labels := by
      have hz : ∀ j, raw23390 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23390step0 = (fun i j => raw23390 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23390step0 raw23390; decide +kernel
      have hl : raw23390step0Labels = raw23390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23390 raw23390Labels permutation434 hz
    mixedMoment B raw23390step0 raw23390step0Labels = mixedMoment B raw23390step1 raw23390step1Labels := by
      have hz : ∀ j, raw23390step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23390step1 = (fun i j => raw23390step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23390step1 raw23390step0; decide +kernel
      have hl : raw23390step1Labels = raw23390step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23390step0 raw23390step0Labels permutation56 hz
    mixedMoment B raw23390step1 raw23390step1Labels = mixedMoment B raw23390step2 raw23390step2Labels := by
      have ha : raw23390step2 = (fun i j => raw23390step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23390step2 raw23390step1; decide +kernel
      have hl : raw23390step2Labels = raw23390step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23390step1 raw23390step1Labels permutation9 permutation7
    mixedMoment B raw23390step2 raw23390step2Labels = mixedMoment B raw23390step3 raw23390step3Labels := by
      have ha : raw23390step3 = -raw23390step2 := by apply Matrix.ext; change ∀ i j, raw23390step3 i j = -(raw23390step2 i j); unfold raw23390step3 raw23390step2; decide +kernel
      have hl : raw23390step3Labels = raw23390step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23390step3 raw23390step3Labels = mixedMoment B raw23390step4 raw23390step4Labels := by
      have ha : raw23390step4 = raw23390step3 := by apply Matrix.ext; unfold raw23390step4 raw23390step3; decide +kernel
      have hl : raw23390step3Labels = labelEmbedding1 ∘ raw23390step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23390step3 raw23390step3Labels raw23390step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2218 node2218Labels := by rfl

theorem canonical23391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23391 raw23391Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw23391 raw23391Labels = mixedMoment B raw23391step0 raw23391step0Labels := by
      have hz : ∀ j, raw23391 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23391step0 = (fun i j => raw23391 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23391step0 raw23391; decide +kernel
      have hl : raw23391step0Labels = raw23391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23391 raw23391Labels permutation346 hz
    mixedMoment B raw23391step0 raw23391step0Labels = mixedMoment B raw23391step1 raw23391step1Labels := by
      have hz : ∀ j, raw23391step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23391step1 = (fun i j => raw23391step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23391step1 raw23391step0; decide +kernel
      have hl : raw23391step1Labels = raw23391step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23391step0 raw23391step0Labels permutation56 hz
    mixedMoment B raw23391step1 raw23391step1Labels = mixedMoment B raw23391step2 raw23391step2Labels := by
      have ha : raw23391step2 = (fun i j => raw23391step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23391step2 raw23391step1; decide +kernel
      have hl : raw23391step2Labels = raw23391step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23391step1 raw23391step1Labels permutation9 permutation7
    mixedMoment B raw23391step2 raw23391step2Labels = mixedMoment B raw23391step3 raw23391step3Labels := by
      have ha : raw23391step3 = -raw23391step2 := by apply Matrix.ext; change ∀ i j, raw23391step3 i j = -(raw23391step2 i j); unfold raw23391step3 raw23391step2; decide +kernel
      have hl : raw23391step3Labels = raw23391step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23391step3 raw23391step3Labels = mixedMoment B raw23391step4 raw23391step4Labels := by
      have ha : raw23391step4 = raw23391step3 := by apply Matrix.ext; unfold raw23391step4 raw23391step3; decide +kernel
      have hl : raw23391step3Labels = labelEmbedding1 ∘ raw23391step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23391step3 raw23391step3Labels raw23391step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2218 node2218Labels := by rfl

theorem canonical23392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23392 raw23392Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw23392 raw23392Labels = mixedMoment B raw23392step0 raw23392step0Labels := by
      have hz : ∀ j, raw23392 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23392step0 = (fun i j => raw23392 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23392step0 raw23392; decide +kernel
      have hl : raw23392step0Labels = raw23392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23392 raw23392Labels permutation434 hz
    mixedMoment B raw23392step0 raw23392step0Labels = mixedMoment B raw23392step1 raw23392step1Labels := by
      have hz : ∀ j, raw23392step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23392step1 = (fun i j => raw23392step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23392step1 raw23392step0; decide +kernel
      have hl : raw23392step1Labels = raw23392step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23392step0 raw23392step0Labels permutation80 hz
    mixedMoment B raw23392step1 raw23392step1Labels = mixedMoment B raw23392step2 raw23392step2Labels := by
      have hz : ∀ j, raw23392step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23392step2 = (fun i j => raw23392step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23392step2 raw23392step1; decide +kernel
      have hl : raw23392step2Labels = raw23392step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23392step1 raw23392step1Labels permutation14 hz
    mixedMoment B raw23392step2 raw23392step2Labels = mixedMoment B raw23392step3 raw23392step3Labels := by
      have ha : raw23392step3 = (fun i j => raw23392step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23392step3 raw23392step2; decide +kernel
      have hl : raw23392step3Labels = raw23392step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23392step2 raw23392step2Labels permutation3 permutation7
    mixedMoment B raw23392step3 raw23392step3Labels = mixedMoment B raw23392step4 raw23392step4Labels := by
      have ha : raw23392step4 = -raw23392step3 := by apply Matrix.ext; change ∀ i j, raw23392step4 i j = -(raw23392step3 i j); unfold raw23392step4 raw23392step3; decide +kernel
      have hl : raw23392step4Labels = raw23392step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23392step4 raw23392step4Labels = mixedMoment B raw23392step5 raw23392step5Labels := by
      have ha : raw23392step5 = raw23392step4 := by apply Matrix.ext; unfold raw23392step5 raw23392step4; decide +kernel
      have hl : raw23392step4Labels = labelEmbedding1 ∘ raw23392step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23392step4 raw23392step4Labels raw23392step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2281 node2281Labels := by rfl

theorem canonical23393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23393 raw23393Labels = mixedMoment B node2268 node2268Labels := by
  calc
    mixedMoment B raw23393 raw23393Labels = mixedMoment B raw23393step0 raw23393step0Labels := by
      have hz : ∀ j, raw23393 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23393step0 = (fun i j => raw23393 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23393step0 raw23393; decide +kernel
      have hl : raw23393step0Labels = raw23393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23393 raw23393Labels permutation434 hz
    mixedMoment B raw23393step0 raw23393step0Labels = mixedMoment B raw23393step1 raw23393step1Labels := by
      have hz : ∀ j, raw23393step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23393step1 = (fun i j => raw23393step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23393step1 raw23393step0; decide +kernel
      have hl : raw23393step1Labels = raw23393step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23393step0 raw23393step0Labels permutation80 hz
    mixedMoment B raw23393step1 raw23393step1Labels = mixedMoment B raw23393step2 raw23393step2Labels := by
      have hz : ∀ j, raw23393step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23393step2 = (fun i j => raw23393step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23393step2 raw23393step1; decide +kernel
      have hl : raw23393step2Labels = raw23393step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23393step1 raw23393step1Labels permutation14 hz
    mixedMoment B raw23393step2 raw23393step2Labels = mixedMoment B raw23393step3 raw23393step3Labels := by
      have ha : raw23393step3 = (fun i j => raw23393step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23393step3 raw23393step2; decide +kernel
      have hl : raw23393step3Labels = raw23393step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23393step2 raw23393step2Labels permutation3 permutation7
    mixedMoment B raw23393step3 raw23393step3Labels = mixedMoment B raw23393step4 raw23393step4Labels := by
      have ha : raw23393step4 = -raw23393step3 := by apply Matrix.ext; change ∀ i j, raw23393step4 i j = -(raw23393step3 i j); unfold raw23393step4 raw23393step3; decide +kernel
      have hl : raw23393step4Labels = raw23393step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23393step4 raw23393step4Labels = mixedMoment B raw23393step5 raw23393step5Labels := by
      have ha : raw23393step5 = raw23393step4 := by apply Matrix.ext; unfold raw23393step5 raw23393step4; decide +kernel
      have hl : raw23393step4Labels = labelEmbedding1 ∘ raw23393step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23393step4 raw23393step4Labels raw23393step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2268 node2268Labels := by rfl

theorem canonical23394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23394 raw23394Labels = mixedMoment B node1513 node1513Labels := by
  calc
    mixedMoment B raw23394 raw23394Labels = mixedMoment B raw23394step0 raw23394step0Labels := by
      have hz : ∀ j, raw23394 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23394step0 = (fun i j => raw23394 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23394step0 raw23394; decide +kernel
      have hl : raw23394step0Labels = raw23394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23394 raw23394Labels permutation434 hz
    mixedMoment B raw23394step0 raw23394step0Labels = mixedMoment B raw23394step1 raw23394step1Labels := by
      have hz : ∀ j, raw23394step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23394step1 = (fun i j => raw23394step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23394step1 raw23394step0; decide +kernel
      have hl : raw23394step1Labels = raw23394step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23394step0 raw23394step0Labels permutation80 hz
    mixedMoment B raw23394step1 raw23394step1Labels = mixedMoment B raw23394step2 raw23394step2Labels := by
      have ha : raw23394step2 = (fun i j => raw23394step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23394step2 raw23394step1; decide +kernel
      have hl : raw23394step2Labels = raw23394step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23394step1 raw23394step1Labels permutation9 permutation7
    mixedMoment B raw23394step2 raw23394step2Labels = mixedMoment B raw23394step3 raw23394step3Labels := by
      have ha : raw23394step3 = -raw23394step2 := by apply Matrix.ext; change ∀ i j, raw23394step3 i j = -(raw23394step2 i j); unfold raw23394step3 raw23394step2; decide +kernel
      have hl : raw23394step3Labels = raw23394step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23394step3 raw23394step3Labels = mixedMoment B raw23394step4 raw23394step4Labels := by
      have ha : raw23394step4 = raw23394step3 := by apply Matrix.ext; unfold raw23394step4 raw23394step3; decide +kernel
      have hl : raw23394step3Labels = labelEmbedding1 ∘ raw23394step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23394step3 raw23394step3Labels raw23394step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1513 node1513Labels := by rfl

theorem canonical23395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23395 raw23395Labels = mixedMoment B node1669 node1669Labels := by
  calc
    mixedMoment B raw23395 raw23395Labels = mixedMoment B raw23395step0 raw23395step0Labels := by
      have hz : ∀ j, raw23395 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23395step0 = (fun i j => raw23395 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23395step0 raw23395; decide +kernel
      have hl : raw23395step0Labels = raw23395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23395 raw23395Labels permutation434 hz
    mixedMoment B raw23395step0 raw23395step0Labels = mixedMoment B raw23395step1 raw23395step1Labels := by
      have ha : raw23395step1 = (fun i j => raw23395step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23395step1 raw23395step0; decide +kernel
      have hl : raw23395step1Labels = raw23395step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23395step0 raw23395step0Labels permutation39 permutation7
    mixedMoment B raw23395step1 raw23395step1Labels = mixedMoment B raw23395step2 raw23395step2Labels := by
      have ha : raw23395step2 = -raw23395step1 := by apply Matrix.ext; change ∀ i j, raw23395step2 i j = -(raw23395step1 i j); unfold raw23395step2 raw23395step1; decide +kernel
      have hl : raw23395step2Labels = raw23395step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23395step2 raw23395step2Labels = mixedMoment B raw23395step3 raw23395step3Labels := by
      have ha : raw23395step3 = raw23395step2 := by apply Matrix.ext; unfold raw23395step3 raw23395step2; decide +kernel
      have hl : raw23395step2Labels = labelEmbedding1 ∘ raw23395step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23395step2 raw23395step2Labels raw23395step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1669 node1669Labels := by rfl

theorem canonical23396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23396 raw23396Labels = mixedMoment B node1669 node1669Labels := by
  calc
    mixedMoment B raw23396 raw23396Labels = mixedMoment B raw23396step0 raw23396step0Labels := by
      have hz : ∀ j, raw23396 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23396step0 = (fun i j => raw23396 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23396step0 raw23396; decide +kernel
      have hl : raw23396step0Labels = raw23396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23396 raw23396Labels permutation346 hz
    mixedMoment B raw23396step0 raw23396step0Labels = mixedMoment B raw23396step1 raw23396step1Labels := by
      have ha : raw23396step1 = (fun i j => raw23396step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23396step1 raw23396step0; decide +kernel
      have hl : raw23396step1Labels = raw23396step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23396step0 raw23396step0Labels permutation39 permutation7
    mixedMoment B raw23396step1 raw23396step1Labels = mixedMoment B raw23396step2 raw23396step2Labels := by
      have ha : raw23396step2 = -raw23396step1 := by apply Matrix.ext; change ∀ i j, raw23396step2 i j = -(raw23396step1 i j); unfold raw23396step2 raw23396step1; decide +kernel
      have hl : raw23396step2Labels = raw23396step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23396step2 raw23396step2Labels = mixedMoment B raw23396step3 raw23396step3Labels := by
      have ha : raw23396step3 = raw23396step2 := by apply Matrix.ext; unfold raw23396step3 raw23396step2; decide +kernel
      have hl : raw23396step2Labels = labelEmbedding1 ∘ raw23396step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23396step2 raw23396step2Labels raw23396step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1669 node1669Labels := by rfl

theorem canonical23397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23397 raw23397Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw23397 raw23397Labels = mixedMoment B raw23397step0 raw23397step0Labels := by
      have hz : ∀ j, raw23397 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23397step0 = (fun i j => raw23397 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23397step0 raw23397; decide +kernel
      have hl : raw23397step0Labels = raw23397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23397 raw23397Labels permutation434 hz
    mixedMoment B raw23397step0 raw23397step0Labels = mixedMoment B raw23397step1 raw23397step1Labels := by
      have hz : ∀ j, raw23397step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23397step1 = (fun i j => raw23397step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23397step1 raw23397step0; decide +kernel
      have hl : raw23397step1Labels = raw23397step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23397step0 raw23397step0Labels permutation80 hz
    mixedMoment B raw23397step1 raw23397step1Labels = mixedMoment B raw23397step2 raw23397step2Labels := by
      have ha : raw23397step2 = (fun i j => raw23397step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23397step2 raw23397step1; decide +kernel
      have hl : raw23397step2Labels = raw23397step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23397step1 raw23397step1Labels permutation9 permutation7
    mixedMoment B raw23397step2 raw23397step2Labels = mixedMoment B raw23397step3 raw23397step3Labels := by
      have ha : raw23397step3 = -raw23397step2 := by apply Matrix.ext; change ∀ i j, raw23397step3 i j = -(raw23397step2 i j); unfold raw23397step3 raw23397step2; decide +kernel
      have hl : raw23397step3Labels = raw23397step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23397step3 raw23397step3Labels = mixedMoment B raw23397step4 raw23397step4Labels := by
      have ha : raw23397step4 = raw23397step3 := by apply Matrix.ext; unfold raw23397step4 raw23397step3; decide +kernel
      have hl : raw23397step3Labels = labelEmbedding1 ∘ raw23397step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23397step3 raw23397step3Labels raw23397step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1716 node1716Labels := by rfl

theorem canonical23398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23398 raw23398Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw23398 raw23398Labels = mixedMoment B raw23398step0 raw23398step0Labels := by
      have hz : ∀ j, raw23398 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23398step0 = (fun i j => raw23398 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23398step0 raw23398; decide +kernel
      have hl : raw23398step0Labels = raw23398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23398 raw23398Labels permutation434 hz
    mixedMoment B raw23398step0 raw23398step0Labels = mixedMoment B raw23398step1 raw23398step1Labels := by
      have hz : ∀ j, raw23398step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23398step1 = (fun i j => raw23398step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23398step1 raw23398step0; decide +kernel
      have hl : raw23398step1Labels = raw23398step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23398step0 raw23398step0Labels permutation80 hz
    mixedMoment B raw23398step1 raw23398step1Labels = mixedMoment B raw23398step2 raw23398step2Labels := by
      have ha : raw23398step2 = (fun i j => raw23398step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23398step2 raw23398step1; decide +kernel
      have hl : raw23398step2Labels = raw23398step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23398step1 raw23398step1Labels permutation9 permutation7
    mixedMoment B raw23398step2 raw23398step2Labels = mixedMoment B raw23398step3 raw23398step3Labels := by
      have ha : raw23398step3 = -raw23398step2 := by apply Matrix.ext; change ∀ i j, raw23398step3 i j = -(raw23398step2 i j); unfold raw23398step3 raw23398step2; decide +kernel
      have hl : raw23398step3Labels = raw23398step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23398step3 raw23398step3Labels = mixedMoment B raw23398step4 raw23398step4Labels := by
      have ha : raw23398step4 = raw23398step3 := by apply Matrix.ext; unfold raw23398step4 raw23398step3; decide +kernel
      have hl : raw23398step3Labels = labelEmbedding1 ∘ raw23398step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23398step3 raw23398step3Labels raw23398step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1710 node1710Labels := by rfl

theorem canonical23399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23399 raw23399Labels = mixedMoment B node1513 node1513Labels := by
  calc
    mixedMoment B raw23399 raw23399Labels = mixedMoment B raw23399step0 raw23399step0Labels := by
      have hz : ∀ j, raw23399 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23399step0 = (fun i j => raw23399 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23399step0 raw23399; decide +kernel
      have hl : raw23399step0Labels = raw23399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23399 raw23399Labels permutation434 hz
    mixedMoment B raw23399step0 raw23399step0Labels = mixedMoment B raw23399step1 raw23399step1Labels := by
      have hz : ∀ j, raw23399step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23399step1 = (fun i j => raw23399step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23399step1 raw23399step0; decide +kernel
      have hl : raw23399step1Labels = raw23399step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23399step0 raw23399step0Labels permutation56 hz
    mixedMoment B raw23399step1 raw23399step1Labels = mixedMoment B raw23399step2 raw23399step2Labels := by
      have ha : raw23399step2 = (fun i j => raw23399step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23399step2 raw23399step1; decide +kernel
      have hl : raw23399step2Labels = raw23399step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23399step1 raw23399step1Labels permutation9 permutation7
    mixedMoment B raw23399step2 raw23399step2Labels = mixedMoment B raw23399step3 raw23399step3Labels := by
      have ha : raw23399step3 = -raw23399step2 := by apply Matrix.ext; change ∀ i j, raw23399step3 i j = -(raw23399step2 i j); unfold raw23399step3 raw23399step2; decide +kernel
      have hl : raw23399step3Labels = raw23399step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23399step3 raw23399step3Labels = mixedMoment B raw23399step4 raw23399step4Labels := by
      have ha : raw23399step4 = raw23399step3 := by apply Matrix.ext; unfold raw23399step4 raw23399step3; decide +kernel
      have hl : raw23399step3Labels = labelEmbedding1 ∘ raw23399step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23399step3 raw23399step3Labels raw23399step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1513 node1513Labels := by rfl

theorem canonical23400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23400 raw23400Labels = mixedMoment B node1669 node1669Labels := by
  calc
    mixedMoment B raw23400 raw23400Labels = mixedMoment B raw23400step0 raw23400step0Labels := by
      have hz : ∀ j, raw23400 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23400step0 = (fun i j => raw23400 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23400step0 raw23400; decide +kernel
      have hl : raw23400step0Labels = raw23400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23400 raw23400Labels permutation434 hz
    mixedMoment B raw23400step0 raw23400step0Labels = mixedMoment B raw23400step1 raw23400step1Labels := by
      have ha : raw23400step1 = (fun i j => raw23400step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23400step1 raw23400step0; decide +kernel
      have hl : raw23400step1Labels = raw23400step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23400step0 raw23400step0Labels permutation33 permutation7
    mixedMoment B raw23400step1 raw23400step1Labels = mixedMoment B raw23400step2 raw23400step2Labels := by
      have ha : raw23400step2 = -raw23400step1 := by apply Matrix.ext; change ∀ i j, raw23400step2 i j = -(raw23400step1 i j); unfold raw23400step2 raw23400step1; decide +kernel
      have hl : raw23400step2Labels = raw23400step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23400step2 raw23400step2Labels = mixedMoment B raw23400step3 raw23400step3Labels := by
      have ha : raw23400step3 = raw23400step2 := by apply Matrix.ext; unfold raw23400step3 raw23400step2; decide +kernel
      have hl : raw23400step2Labels = labelEmbedding1 ∘ raw23400step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23400step2 raw23400step2Labels raw23400step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1669 node1669Labels := by rfl

theorem canonical23401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23401 raw23401Labels = mixedMoment B node1669 node1669Labels := by
  calc
    mixedMoment B raw23401 raw23401Labels = mixedMoment B raw23401step0 raw23401step0Labels := by
      have hz : ∀ j, raw23401 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23401step0 = (fun i j => raw23401 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23401step0 raw23401; decide +kernel
      have hl : raw23401step0Labels = raw23401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23401 raw23401Labels permutation265 hz
    mixedMoment B raw23401step0 raw23401step0Labels = mixedMoment B raw23401step1 raw23401step1Labels := by
      have ha : raw23401step1 = (fun i j => raw23401step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23401step1 raw23401step0; decide +kernel
      have hl : raw23401step1Labels = raw23401step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23401step0 raw23401step0Labels permutation39 permutation7
    mixedMoment B raw23401step1 raw23401step1Labels = mixedMoment B raw23401step2 raw23401step2Labels := by
      have ha : raw23401step2 = -raw23401step1 := by apply Matrix.ext; change ∀ i j, raw23401step2 i j = -(raw23401step1 i j); unfold raw23401step2 raw23401step1; decide +kernel
      have hl : raw23401step2Labels = raw23401step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23401step2 raw23401step2Labels = mixedMoment B raw23401step3 raw23401step3Labels := by
      have ha : raw23401step3 = raw23401step2 := by apply Matrix.ext; unfold raw23401step3 raw23401step2; decide +kernel
      have hl : raw23401step2Labels = labelEmbedding1 ∘ raw23401step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23401step2 raw23401step2Labels raw23401step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1669 node1669Labels := by rfl

theorem canonical23402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23402 raw23402Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw23402 raw23402Labels = mixedMoment B raw23402step0 raw23402step0Labels := by
      have hz : ∀ j, raw23402 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23402step0 = (fun i j => raw23402 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23402step0 raw23402; decide +kernel
      have hl : raw23402step0Labels = raw23402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23402 raw23402Labels permutation434 hz
    mixedMoment B raw23402step0 raw23402step0Labels = mixedMoment B raw23402step1 raw23402step1Labels := by
      have hz : ∀ j, raw23402step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23402step1 = (fun i j => raw23402step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23402step1 raw23402step0; decide +kernel
      have hl : raw23402step1Labels = raw23402step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23402step0 raw23402step0Labels permutation56 hz
    mixedMoment B raw23402step1 raw23402step1Labels = mixedMoment B raw23402step2 raw23402step2Labels := by
      have ha : raw23402step2 = (fun i j => raw23402step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23402step2 raw23402step1; decide +kernel
      have hl : raw23402step2Labels = raw23402step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23402step1 raw23402step1Labels permutation9 permutation7
    mixedMoment B raw23402step2 raw23402step2Labels = mixedMoment B raw23402step3 raw23402step3Labels := by
      have ha : raw23402step3 = -raw23402step2 := by apply Matrix.ext; change ∀ i j, raw23402step3 i j = -(raw23402step2 i j); unfold raw23402step3 raw23402step2; decide +kernel
      have hl : raw23402step3Labels = raw23402step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23402step3 raw23402step3Labels = mixedMoment B raw23402step4 raw23402step4Labels := by
      have ha : raw23402step4 = raw23402step3 := by apply Matrix.ext; unfold raw23402step4 raw23402step3; decide +kernel
      have hl : raw23402step3Labels = labelEmbedding1 ∘ raw23402step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23402step3 raw23402step3Labels raw23402step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1716 node1716Labels := by rfl

theorem canonical23403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23403 raw23403Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw23403 raw23403Labels = mixedMoment B raw23403step0 raw23403step0Labels := by
      have hz : ∀ j, raw23403 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23403step0 = (fun i j => raw23403 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23403step0 raw23403; decide +kernel
      have hl : raw23403step0Labels = raw23403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23403 raw23403Labels permutation434 hz
    mixedMoment B raw23403step0 raw23403step0Labels = mixedMoment B raw23403step1 raw23403step1Labels := by
      have hz : ∀ j, raw23403step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23403step1 = (fun i j => raw23403step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23403step1 raw23403step0; decide +kernel
      have hl : raw23403step1Labels = raw23403step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23403step0 raw23403step0Labels permutation56 hz
    mixedMoment B raw23403step1 raw23403step1Labels = mixedMoment B raw23403step2 raw23403step2Labels := by
      have ha : raw23403step2 = (fun i j => raw23403step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23403step2 raw23403step1; decide +kernel
      have hl : raw23403step2Labels = raw23403step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23403step1 raw23403step1Labels permutation9 permutation7
    mixedMoment B raw23403step2 raw23403step2Labels = mixedMoment B raw23403step3 raw23403step3Labels := by
      have ha : raw23403step3 = -raw23403step2 := by apply Matrix.ext; change ∀ i j, raw23403step3 i j = -(raw23403step2 i j); unfold raw23403step3 raw23403step2; decide +kernel
      have hl : raw23403step3Labels = raw23403step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23403step3 raw23403step3Labels = mixedMoment B raw23403step4 raw23403step4Labels := by
      have ha : raw23403step4 = raw23403step3 := by apply Matrix.ext; unfold raw23403step4 raw23403step3; decide +kernel
      have hl : raw23403step3Labels = labelEmbedding1 ∘ raw23403step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23403step3 raw23403step3Labels raw23403step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1710 node1710Labels := by rfl

theorem canonical23404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23404 raw23404Labels = mixedMoment B node1513 node1513Labels := by
  calc
    mixedMoment B raw23404 raw23404Labels = mixedMoment B raw23404step0 raw23404step0Labels := by
      have hz : ∀ j, raw23404 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23404step0 = (fun i j => raw23404 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23404step0 raw23404; decide +kernel
      have hl : raw23404step0Labels = raw23404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23404 raw23404Labels permutation346 hz
    mixedMoment B raw23404step0 raw23404step0Labels = mixedMoment B raw23404step1 raw23404step1Labels := by
      have hz : ∀ j, raw23404step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23404step1 = (fun i j => raw23404step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23404step1 raw23404step0; decide +kernel
      have hl : raw23404step1Labels = raw23404step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23404step0 raw23404step0Labels permutation56 hz
    mixedMoment B raw23404step1 raw23404step1Labels = mixedMoment B raw23404step2 raw23404step2Labels := by
      have ha : raw23404step2 = (fun i j => raw23404step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23404step2 raw23404step1; decide +kernel
      have hl : raw23404step2Labels = raw23404step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23404step1 raw23404step1Labels permutation9 permutation7
    mixedMoment B raw23404step2 raw23404step2Labels = mixedMoment B raw23404step3 raw23404step3Labels := by
      have ha : raw23404step3 = -raw23404step2 := by apply Matrix.ext; change ∀ i j, raw23404step3 i j = -(raw23404step2 i j); unfold raw23404step3 raw23404step2; decide +kernel
      have hl : raw23404step3Labels = raw23404step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23404step3 raw23404step3Labels = mixedMoment B raw23404step4 raw23404step4Labels := by
      have ha : raw23404step4 = raw23404step3 := by apply Matrix.ext; unfold raw23404step4 raw23404step3; decide +kernel
      have hl : raw23404step3Labels = labelEmbedding1 ∘ raw23404step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23404step3 raw23404step3Labels raw23404step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1513 node1513Labels := by rfl

theorem canonical23405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23405 raw23405Labels = mixedMoment B node1669 node1669Labels := by
  calc
    mixedMoment B raw23405 raw23405Labels = mixedMoment B raw23405step0 raw23405step0Labels := by
      have hz : ∀ j, raw23405 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23405step0 = (fun i j => raw23405 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23405step0 raw23405; decide +kernel
      have hl : raw23405step0Labels = raw23405Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23405 raw23405Labels permutation346 hz
    mixedMoment B raw23405step0 raw23405step0Labels = mixedMoment B raw23405step1 raw23405step1Labels := by
      have ha : raw23405step1 = (fun i j => raw23405step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23405step1 raw23405step0; decide +kernel
      have hl : raw23405step1Labels = raw23405step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23405step0 raw23405step0Labels permutation33 permutation7
    mixedMoment B raw23405step1 raw23405step1Labels = mixedMoment B raw23405step2 raw23405step2Labels := by
      have ha : raw23405step2 = -raw23405step1 := by apply Matrix.ext; change ∀ i j, raw23405step2 i j = -(raw23405step1 i j); unfold raw23405step2 raw23405step1; decide +kernel
      have hl : raw23405step2Labels = raw23405step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23405step2 raw23405step2Labels = mixedMoment B raw23405step3 raw23405step3Labels := by
      have ha : raw23405step3 = raw23405step2 := by apply Matrix.ext; unfold raw23405step3 raw23405step2; decide +kernel
      have hl : raw23405step2Labels = labelEmbedding1 ∘ raw23405step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23405step2 raw23405step2Labels raw23405step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1669 node1669Labels := by rfl

theorem canonical23406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23406 raw23406Labels = mixedMoment B node1669 node1669Labels := by
  calc
    mixedMoment B raw23406 raw23406Labels = mixedMoment B raw23406step0 raw23406step0Labels := by
      have hz : ∀ j, raw23406 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23406step0 = (fun i j => raw23406 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23406step0 raw23406; decide +kernel
      have hl : raw23406step0Labels = raw23406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23406 raw23406Labels permutation265 hz
    mixedMoment B raw23406step0 raw23406step0Labels = mixedMoment B raw23406step1 raw23406step1Labels := by
      have ha : raw23406step1 = (fun i j => raw23406step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23406step1 raw23406step0; decide +kernel
      have hl : raw23406step1Labels = raw23406step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23406step0 raw23406step0Labels permutation33 permutation7
    mixedMoment B raw23406step1 raw23406step1Labels = mixedMoment B raw23406step2 raw23406step2Labels := by
      have ha : raw23406step2 = -raw23406step1 := by apply Matrix.ext; change ∀ i j, raw23406step2 i j = -(raw23406step1 i j); unfold raw23406step2 raw23406step1; decide +kernel
      have hl : raw23406step2Labels = raw23406step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23406step2 raw23406step2Labels = mixedMoment B raw23406step3 raw23406step3Labels := by
      have ha : raw23406step3 = raw23406step2 := by apply Matrix.ext; unfold raw23406step3 raw23406step2; decide +kernel
      have hl : raw23406step2Labels = labelEmbedding1 ∘ raw23406step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23406step2 raw23406step2Labels raw23406step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1669 node1669Labels := by rfl

theorem canonical23407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23407 raw23407Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw23407 raw23407Labels = mixedMoment B raw23407step0 raw23407step0Labels := by
      have hz : ∀ j, raw23407 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23407step0 = (fun i j => raw23407 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23407step0 raw23407; decide +kernel
      have hl : raw23407step0Labels = raw23407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23407 raw23407Labels permutation346 hz
    mixedMoment B raw23407step0 raw23407step0Labels = mixedMoment B raw23407step1 raw23407step1Labels := by
      have hz : ∀ j, raw23407step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23407step1 = (fun i j => raw23407step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23407step1 raw23407step0; decide +kernel
      have hl : raw23407step1Labels = raw23407step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23407step0 raw23407step0Labels permutation56 hz
    mixedMoment B raw23407step1 raw23407step1Labels = mixedMoment B raw23407step2 raw23407step2Labels := by
      have ha : raw23407step2 = (fun i j => raw23407step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23407step2 raw23407step1; decide +kernel
      have hl : raw23407step2Labels = raw23407step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23407step1 raw23407step1Labels permutation9 permutation7
    mixedMoment B raw23407step2 raw23407step2Labels = mixedMoment B raw23407step3 raw23407step3Labels := by
      have ha : raw23407step3 = -raw23407step2 := by apply Matrix.ext; change ∀ i j, raw23407step3 i j = -(raw23407step2 i j); unfold raw23407step3 raw23407step2; decide +kernel
      have hl : raw23407step3Labels = raw23407step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23407step3 raw23407step3Labels = mixedMoment B raw23407step4 raw23407step4Labels := by
      have ha : raw23407step4 = raw23407step3 := by apply Matrix.ext; unfold raw23407step4 raw23407step3; decide +kernel
      have hl : raw23407step3Labels = labelEmbedding1 ∘ raw23407step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23407step3 raw23407step3Labels raw23407step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1716 node1716Labels := by rfl

theorem canonical23408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23408 raw23408Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw23408 raw23408Labels = mixedMoment B raw23408step0 raw23408step0Labels := by
      have hz : ∀ j, raw23408 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23408step0 = (fun i j => raw23408 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23408step0 raw23408; decide +kernel
      have hl : raw23408step0Labels = raw23408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23408 raw23408Labels permutation346 hz
    mixedMoment B raw23408step0 raw23408step0Labels = mixedMoment B raw23408step1 raw23408step1Labels := by
      have hz : ∀ j, raw23408step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23408step1 = (fun i j => raw23408step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23408step1 raw23408step0; decide +kernel
      have hl : raw23408step1Labels = raw23408step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23408step0 raw23408step0Labels permutation56 hz
    mixedMoment B raw23408step1 raw23408step1Labels = mixedMoment B raw23408step2 raw23408step2Labels := by
      have ha : raw23408step2 = (fun i j => raw23408step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23408step2 raw23408step1; decide +kernel
      have hl : raw23408step2Labels = raw23408step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23408step1 raw23408step1Labels permutation9 permutation7
    mixedMoment B raw23408step2 raw23408step2Labels = mixedMoment B raw23408step3 raw23408step3Labels := by
      have ha : raw23408step3 = -raw23408step2 := by apply Matrix.ext; change ∀ i j, raw23408step3 i j = -(raw23408step2 i j); unfold raw23408step3 raw23408step2; decide +kernel
      have hl : raw23408step3Labels = raw23408step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23408step3 raw23408step3Labels = mixedMoment B raw23408step4 raw23408step4Labels := by
      have ha : raw23408step4 = raw23408step3 := by apply Matrix.ext; unfold raw23408step4 raw23408step3; decide +kernel
      have hl : raw23408step3Labels = labelEmbedding1 ∘ raw23408step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23408step3 raw23408step3Labels raw23408step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1710 node1710Labels := by rfl

theorem canonical23409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23409 raw23409Labels = mixedMoment B node1527 node1527Labels := by
  calc
    mixedMoment B raw23409 raw23409Labels = mixedMoment B raw23409step0 raw23409step0Labels := by
      have hz : ∀ j, raw23409 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23409step0 = (fun i j => raw23409 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23409step0 raw23409; decide +kernel
      have hl : raw23409step0Labels = raw23409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23409 raw23409Labels permutation434 hz
    mixedMoment B raw23409step0 raw23409step0Labels = mixedMoment B raw23409step1 raw23409step1Labels := by
      have hz : ∀ j, raw23409step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23409step1 = (fun i j => raw23409step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23409step1 raw23409step0; decide +kernel
      have hl : raw23409step1Labels = raw23409step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23409step0 raw23409step0Labels permutation80 hz
    mixedMoment B raw23409step1 raw23409step1Labels = mixedMoment B raw23409step2 raw23409step2Labels := by
      have hz : ∀ j, raw23409step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23409step2 = (fun i j => raw23409step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23409step2 raw23409step1; decide +kernel
      have hl : raw23409step2Labels = raw23409step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23409step1 raw23409step1Labels permutation14 hz
    mixedMoment B raw23409step2 raw23409step2Labels = mixedMoment B raw23409step3 raw23409step3Labels := by
      have ha : raw23409step3 = (fun i j => raw23409step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23409step3 raw23409step2; decide +kernel
      have hl : raw23409step3Labels = raw23409step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23409step2 raw23409step2Labels permutation3 permutation7
    mixedMoment B raw23409step3 raw23409step3Labels = mixedMoment B raw23409step4 raw23409step4Labels := by
      have ha : raw23409step4 = -raw23409step3 := by apply Matrix.ext; change ∀ i j, raw23409step4 i j = -(raw23409step3 i j); unfold raw23409step4 raw23409step3; decide +kernel
      have hl : raw23409step4Labels = raw23409step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23409step4 raw23409step4Labels = mixedMoment B raw23409step5 raw23409step5Labels := by
      have ha : raw23409step5 = raw23409step4 := by apply Matrix.ext; unfold raw23409step5 raw23409step4; decide +kernel
      have hl : raw23409step4Labels = labelEmbedding1 ∘ raw23409step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23409step4 raw23409step4Labels raw23409step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1527 node1527Labels := by rfl

theorem canonical23410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23410 raw23410Labels = mixedMoment B node1683 node1683Labels := by
  calc
    mixedMoment B raw23410 raw23410Labels = mixedMoment B raw23410step0 raw23410step0Labels := by
      have hz : ∀ j, raw23410 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23410step0 = (fun i j => raw23410 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23410step0 raw23410; decide +kernel
      have hl : raw23410step0Labels = raw23410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23410 raw23410Labels permutation434 hz
    mixedMoment B raw23410step0 raw23410step0Labels = mixedMoment B raw23410step1 raw23410step1Labels := by
      have hz : ∀ j, raw23410step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23410step1 = (fun i j => raw23410step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23410step1 raw23410step0; decide +kernel
      have hl : raw23410step1Labels = raw23410step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23410step0 raw23410step0Labels permutation80 hz
    mixedMoment B raw23410step1 raw23410step1Labels = mixedMoment B raw23410step2 raw23410step2Labels := by
      have ha : raw23410step2 = (fun i j => raw23410step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23410step2 raw23410step1; decide +kernel
      have hl : raw23410step2Labels = raw23410step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23410step1 raw23410step1Labels permutation9 permutation7
    mixedMoment B raw23410step2 raw23410step2Labels = mixedMoment B raw23410step3 raw23410step3Labels := by
      have ha : raw23410step3 = -raw23410step2 := by apply Matrix.ext; change ∀ i j, raw23410step3 i j = -(raw23410step2 i j); unfold raw23410step3 raw23410step2; decide +kernel
      have hl : raw23410step3Labels = raw23410step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23410step3 raw23410step3Labels = mixedMoment B raw23410step4 raw23410step4Labels := by
      have ha : raw23410step4 = raw23410step3 := by apply Matrix.ext; unfold raw23410step4 raw23410step3; decide +kernel
      have hl : raw23410step3Labels = labelEmbedding1 ∘ raw23410step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23410step3 raw23410step3Labels raw23410step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1683 node1683Labels := by rfl

theorem canonical23411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23411 raw23411Labels = mixedMoment B node1683 node1683Labels := by
  calc
    mixedMoment B raw23411 raw23411Labels = mixedMoment B raw23411step0 raw23411step0Labels := by
      have hz : ∀ j, raw23411 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23411step0 = (fun i j => raw23411 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23411step0 raw23411; decide +kernel
      have hl : raw23411step0Labels = raw23411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23411 raw23411Labels permutation434 hz
    mixedMoment B raw23411step0 raw23411step0Labels = mixedMoment B raw23411step1 raw23411step1Labels := by
      have hz : ∀ j, raw23411step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23411step1 = (fun i j => raw23411step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23411step1 raw23411step0; decide +kernel
      have hl : raw23411step1Labels = raw23411step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23411step0 raw23411step0Labels permutation56 hz
    mixedMoment B raw23411step1 raw23411step1Labels = mixedMoment B raw23411step2 raw23411step2Labels := by
      have ha : raw23411step2 = (fun i j => raw23411step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23411step2 raw23411step1; decide +kernel
      have hl : raw23411step2Labels = raw23411step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23411step1 raw23411step1Labels permutation9 permutation7
    mixedMoment B raw23411step2 raw23411step2Labels = mixedMoment B raw23411step3 raw23411step3Labels := by
      have ha : raw23411step3 = -raw23411step2 := by apply Matrix.ext; change ∀ i j, raw23411step3 i j = -(raw23411step2 i j); unfold raw23411step3 raw23411step2; decide +kernel
      have hl : raw23411step3Labels = raw23411step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23411step3 raw23411step3Labels = mixedMoment B raw23411step4 raw23411step4Labels := by
      have ha : raw23411step4 = raw23411step3 := by apply Matrix.ext; unfold raw23411step4 raw23411step3; decide +kernel
      have hl : raw23411step3Labels = labelEmbedding1 ∘ raw23411step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23411step3 raw23411step3Labels raw23411step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1683 node1683Labels := by rfl

theorem canonical23412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23412 raw23412Labels = mixedMoment B node1683 node1683Labels := by
  calc
    mixedMoment B raw23412 raw23412Labels = mixedMoment B raw23412step0 raw23412step0Labels := by
      have hz : ∀ j, raw23412 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23412step0 = (fun i j => raw23412 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23412step0 raw23412; decide +kernel
      have hl : raw23412step0Labels = raw23412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23412 raw23412Labels permutation346 hz
    mixedMoment B raw23412step0 raw23412step0Labels = mixedMoment B raw23412step1 raw23412step1Labels := by
      have hz : ∀ j, raw23412step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23412step1 = (fun i j => raw23412step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23412step1 raw23412step0; decide +kernel
      have hl : raw23412step1Labels = raw23412step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23412step0 raw23412step0Labels permutation56 hz
    mixedMoment B raw23412step1 raw23412step1Labels = mixedMoment B raw23412step2 raw23412step2Labels := by
      have ha : raw23412step2 = (fun i j => raw23412step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23412step2 raw23412step1; decide +kernel
      have hl : raw23412step2Labels = raw23412step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23412step1 raw23412step1Labels permutation9 permutation7
    mixedMoment B raw23412step2 raw23412step2Labels = mixedMoment B raw23412step3 raw23412step3Labels := by
      have ha : raw23412step3 = -raw23412step2 := by apply Matrix.ext; change ∀ i j, raw23412step3 i j = -(raw23412step2 i j); unfold raw23412step3 raw23412step2; decide +kernel
      have hl : raw23412step3Labels = raw23412step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23412step3 raw23412step3Labels = mixedMoment B raw23412step4 raw23412step4Labels := by
      have ha : raw23412step4 = raw23412step3 := by apply Matrix.ext; unfold raw23412step4 raw23412step3; decide +kernel
      have hl : raw23412step3Labels = labelEmbedding1 ∘ raw23412step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23412step3 raw23412step3Labels raw23412step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1683 node1683Labels := by rfl

theorem canonical23413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23413 raw23413Labels = mixedMoment B node1730 node1730Labels := by
  calc
    mixedMoment B raw23413 raw23413Labels = mixedMoment B raw23413step0 raw23413step0Labels := by
      have hz : ∀ j, raw23413 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23413step0 = (fun i j => raw23413 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23413step0 raw23413; decide +kernel
      have hl : raw23413step0Labels = raw23413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23413 raw23413Labels permutation434 hz
    mixedMoment B raw23413step0 raw23413step0Labels = mixedMoment B raw23413step1 raw23413step1Labels := by
      have hz : ∀ j, raw23413step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23413step1 = (fun i j => raw23413step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23413step1 raw23413step0; decide +kernel
      have hl : raw23413step1Labels = raw23413step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23413step0 raw23413step0Labels permutation80 hz
    mixedMoment B raw23413step1 raw23413step1Labels = mixedMoment B raw23413step2 raw23413step2Labels := by
      have hz : ∀ j, raw23413step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23413step2 = (fun i j => raw23413step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23413step2 raw23413step1; decide +kernel
      have hl : raw23413step2Labels = raw23413step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23413step1 raw23413step1Labels permutation14 hz
    mixedMoment B raw23413step2 raw23413step2Labels = mixedMoment B raw23413step3 raw23413step3Labels := by
      have ha : raw23413step3 = (fun i j => raw23413step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23413step3 raw23413step2; decide +kernel
      have hl : raw23413step3Labels = raw23413step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23413step2 raw23413step2Labels permutation3 permutation7
    mixedMoment B raw23413step3 raw23413step3Labels = mixedMoment B raw23413step4 raw23413step4Labels := by
      have ha : raw23413step4 = -raw23413step3 := by apply Matrix.ext; change ∀ i j, raw23413step4 i j = -(raw23413step3 i j); unfold raw23413step4 raw23413step3; decide +kernel
      have hl : raw23413step4Labels = raw23413step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23413step4 raw23413step4Labels = mixedMoment B raw23413step5 raw23413step5Labels := by
      have ha : raw23413step5 = raw23413step4 := by apply Matrix.ext; unfold raw23413step5 raw23413step4; decide +kernel
      have hl : raw23413step4Labels = labelEmbedding1 ∘ raw23413step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23413step4 raw23413step4Labels raw23413step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1730 node1730Labels := by rfl

theorem canonical23414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23414 raw23414Labels = mixedMoment B node1531 node1531Labels := by
  calc
    mixedMoment B raw23414 raw23414Labels = mixedMoment B raw23414step0 raw23414step0Labels := by
      have hz : ∀ j, raw23414 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23414step0 = (fun i j => raw23414 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23414step0 raw23414; decide +kernel
      have hl : raw23414step0Labels = raw23414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23414 raw23414Labels permutation434 hz
    mixedMoment B raw23414step0 raw23414step0Labels = mixedMoment B raw23414step1 raw23414step1Labels := by
      have hz : ∀ j, raw23414step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23414step1 = (fun i j => raw23414step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23414step1 raw23414step0; decide +kernel
      have hl : raw23414step1Labels = raw23414step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23414step0 raw23414step0Labels permutation80 hz
    mixedMoment B raw23414step1 raw23414step1Labels = mixedMoment B raw23414step2 raw23414step2Labels := by
      have hz : ∀ j, raw23414step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23414step2 = (fun i j => raw23414step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23414step2 raw23414step1; decide +kernel
      have hl : raw23414step2Labels = raw23414step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23414step1 raw23414step1Labels permutation14 hz
    mixedMoment B raw23414step2 raw23414step2Labels = mixedMoment B raw23414step3 raw23414step3Labels := by
      have ha : raw23414step3 = (fun i j => raw23414step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23414step3 raw23414step2; decide +kernel
      have hl : raw23414step3Labels = raw23414step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23414step2 raw23414step2Labels permutation3 permutation7
    mixedMoment B raw23414step3 raw23414step3Labels = mixedMoment B raw23414step4 raw23414step4Labels := by
      have ha : raw23414step4 = -raw23414step3 := by apply Matrix.ext; change ∀ i j, raw23414step4 i j = -(raw23414step3 i j); unfold raw23414step4 raw23414step3; decide +kernel
      have hl : raw23414step4Labels = raw23414step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23414step4 raw23414step4Labels = mixedMoment B raw23414step5 raw23414step5Labels := by
      have ha : raw23414step5 = raw23414step4 := by apply Matrix.ext; unfold raw23414step5 raw23414step4; decide +kernel
      have hl : raw23414step4Labels = labelEmbedding1 ∘ raw23414step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23414step4 raw23414step4Labels raw23414step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1531 node1531Labels := by rfl

theorem canonical23415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23415 raw23415Labels = mixedMoment B node1687 node1687Labels := by
  calc
    mixedMoment B raw23415 raw23415Labels = mixedMoment B raw23415step0 raw23415step0Labels := by
      have hz : ∀ j, raw23415 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23415step0 = (fun i j => raw23415 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23415step0 raw23415; decide +kernel
      have hl : raw23415step0Labels = raw23415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23415 raw23415Labels permutation434 hz
    mixedMoment B raw23415step0 raw23415step0Labels = mixedMoment B raw23415step1 raw23415step1Labels := by
      have hz : ∀ j, raw23415step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23415step1 = (fun i j => raw23415step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23415step1 raw23415step0; decide +kernel
      have hl : raw23415step1Labels = raw23415step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23415step0 raw23415step0Labels permutation80 hz
    mixedMoment B raw23415step1 raw23415step1Labels = mixedMoment B raw23415step2 raw23415step2Labels := by
      have ha : raw23415step2 = (fun i j => raw23415step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23415step2 raw23415step1; decide +kernel
      have hl : raw23415step2Labels = raw23415step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23415step1 raw23415step1Labels permutation9 permutation7
    mixedMoment B raw23415step2 raw23415step2Labels = mixedMoment B raw23415step3 raw23415step3Labels := by
      have ha : raw23415step3 = -raw23415step2 := by apply Matrix.ext; change ∀ i j, raw23415step3 i j = -(raw23415step2 i j); unfold raw23415step3 raw23415step2; decide +kernel
      have hl : raw23415step3Labels = raw23415step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23415step3 raw23415step3Labels = mixedMoment B raw23415step4 raw23415step4Labels := by
      have ha : raw23415step4 = raw23415step3 := by apply Matrix.ext; unfold raw23415step4 raw23415step3; decide +kernel
      have hl : raw23415step3Labels = labelEmbedding1 ∘ raw23415step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23415step3 raw23415step3Labels raw23415step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1687 node1687Labels := by rfl

theorem canonical23416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23416 raw23416Labels = mixedMoment B node1687 node1687Labels := by
  calc
    mixedMoment B raw23416 raw23416Labels = mixedMoment B raw23416step0 raw23416step0Labels := by
      have hz : ∀ j, raw23416 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23416step0 = (fun i j => raw23416 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23416step0 raw23416; decide +kernel
      have hl : raw23416step0Labels = raw23416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23416 raw23416Labels permutation434 hz
    mixedMoment B raw23416step0 raw23416step0Labels = mixedMoment B raw23416step1 raw23416step1Labels := by
      have hz : ∀ j, raw23416step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23416step1 = (fun i j => raw23416step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23416step1 raw23416step0; decide +kernel
      have hl : raw23416step1Labels = raw23416step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23416step0 raw23416step0Labels permutation56 hz
    mixedMoment B raw23416step1 raw23416step1Labels = mixedMoment B raw23416step2 raw23416step2Labels := by
      have ha : raw23416step2 = (fun i j => raw23416step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23416step2 raw23416step1; decide +kernel
      have hl : raw23416step2Labels = raw23416step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23416step1 raw23416step1Labels permutation9 permutation7
    mixedMoment B raw23416step2 raw23416step2Labels = mixedMoment B raw23416step3 raw23416step3Labels := by
      have ha : raw23416step3 = -raw23416step2 := by apply Matrix.ext; change ∀ i j, raw23416step3 i j = -(raw23416step2 i j); unfold raw23416step3 raw23416step2; decide +kernel
      have hl : raw23416step3Labels = raw23416step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23416step3 raw23416step3Labels = mixedMoment B raw23416step4 raw23416step4Labels := by
      have ha : raw23416step4 = raw23416step3 := by apply Matrix.ext; unfold raw23416step4 raw23416step3; decide +kernel
      have hl : raw23416step3Labels = labelEmbedding1 ∘ raw23416step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23416step3 raw23416step3Labels raw23416step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1687 node1687Labels := by rfl

theorem canonical23417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23417 raw23417Labels = mixedMoment B node1687 node1687Labels := by
  calc
    mixedMoment B raw23417 raw23417Labels = mixedMoment B raw23417step0 raw23417step0Labels := by
      have hz : ∀ j, raw23417 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23417step0 = (fun i j => raw23417 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23417step0 raw23417; decide +kernel
      have hl : raw23417step0Labels = raw23417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23417 raw23417Labels permutation346 hz
    mixedMoment B raw23417step0 raw23417step0Labels = mixedMoment B raw23417step1 raw23417step1Labels := by
      have hz : ∀ j, raw23417step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23417step1 = (fun i j => raw23417step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23417step1 raw23417step0; decide +kernel
      have hl : raw23417step1Labels = raw23417step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23417step0 raw23417step0Labels permutation56 hz
    mixedMoment B raw23417step1 raw23417step1Labels = mixedMoment B raw23417step2 raw23417step2Labels := by
      have ha : raw23417step2 = (fun i j => raw23417step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23417step2 raw23417step1; decide +kernel
      have hl : raw23417step2Labels = raw23417step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23417step1 raw23417step1Labels permutation9 permutation7
    mixedMoment B raw23417step2 raw23417step2Labels = mixedMoment B raw23417step3 raw23417step3Labels := by
      have ha : raw23417step3 = -raw23417step2 := by apply Matrix.ext; change ∀ i j, raw23417step3 i j = -(raw23417step2 i j); unfold raw23417step3 raw23417step2; decide +kernel
      have hl : raw23417step3Labels = raw23417step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23417step3 raw23417step3Labels = mixedMoment B raw23417step4 raw23417step4Labels := by
      have ha : raw23417step4 = raw23417step3 := by apply Matrix.ext; unfold raw23417step4 raw23417step3; decide +kernel
      have hl : raw23417step3Labels = labelEmbedding1 ∘ raw23417step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23417step3 raw23417step3Labels raw23417step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1687 node1687Labels := by rfl

theorem canonical23418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23418 raw23418Labels = mixedMoment B node1747 node1747Labels := by
  calc
    mixedMoment B raw23418 raw23418Labels = mixedMoment B raw23418step0 raw23418step0Labels := by
      have hz : ∀ j, raw23418 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23418step0 = (fun i j => raw23418 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23418step0 raw23418; decide +kernel
      have hl : raw23418step0Labels = raw23418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23418 raw23418Labels permutation434 hz
    mixedMoment B raw23418step0 raw23418step0Labels = mixedMoment B raw23418step1 raw23418step1Labels := by
      have hz : ∀ j, raw23418step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23418step1 = (fun i j => raw23418step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23418step1 raw23418step0; decide +kernel
      have hl : raw23418step1Labels = raw23418step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23418step0 raw23418step0Labels permutation80 hz
    mixedMoment B raw23418step1 raw23418step1Labels = mixedMoment B raw23418step2 raw23418step2Labels := by
      have hz : ∀ j, raw23418step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23418step2 = (fun i j => raw23418step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23418step2 raw23418step1; decide +kernel
      have hl : raw23418step2Labels = raw23418step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23418step1 raw23418step1Labels permutation14 hz
    mixedMoment B raw23418step2 raw23418step2Labels = mixedMoment B raw23418step3 raw23418step3Labels := by
      have ha : raw23418step3 = (fun i j => raw23418step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23418step3 raw23418step2; decide +kernel
      have hl : raw23418step3Labels = raw23418step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23418step2 raw23418step2Labels permutation3 permutation7
    mixedMoment B raw23418step3 raw23418step3Labels = mixedMoment B raw23418step4 raw23418step4Labels := by
      have ha : raw23418step4 = -raw23418step3 := by apply Matrix.ext; change ∀ i j, raw23418step4 i j = -(raw23418step3 i j); unfold raw23418step4 raw23418step3; decide +kernel
      have hl : raw23418step4Labels = raw23418step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23418step4 raw23418step4Labels = mixedMoment B raw23418step5 raw23418step5Labels := by
      have ha : raw23418step5 = raw23418step4 := by apply Matrix.ext; unfold raw23418step5 raw23418step4; decide +kernel
      have hl : raw23418step4Labels = labelEmbedding1 ∘ raw23418step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23418step4 raw23418step4Labels raw23418step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1747 node1747Labels := by rfl

theorem canonical23419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23419 raw23419Labels = mixedMoment B node607 node607Labels := by
  calc
    mixedMoment B raw23419 raw23419Labels = mixedMoment B raw23419step0 raw23419step0Labels := by
      have hz : ∀ j, raw23419 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23419step0 = (fun i j => raw23419 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23419step0 raw23419; decide +kernel
      have hl : raw23419step0Labels = raw23419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23419 raw23419Labels permutation434 hz
    mixedMoment B raw23419step0 raw23419step0Labels = mixedMoment B raw23419step1 raw23419step1Labels := by
      have hz : ∀ j, raw23419step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23419step1 = (fun i j => raw23419step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23419step1 raw23419step0; decide +kernel
      have hl : raw23419step1Labels = raw23419step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23419step0 raw23419step0Labels permutation80 hz
    mixedMoment B raw23419step1 raw23419step1Labels = mixedMoment B raw23419step2 raw23419step2Labels := by
      have ha : raw23419step2 = (fun i j => raw23419step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23419step2 raw23419step1; decide +kernel
      have hl : raw23419step2Labels = raw23419step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23419step1 raw23419step1Labels permutation9 permutation2
    _ = mixedMoment B node607 node607Labels := by rfl

theorem canonical23420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23420 raw23420Labels = mixedMoment B node607 node607Labels := by
  calc
    mixedMoment B raw23420 raw23420Labels = mixedMoment B raw23420step0 raw23420step0Labels := by
      have hz : ∀ j, raw23420 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23420step0 = (fun i j => raw23420 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23420step0 raw23420; decide +kernel
      have hl : raw23420step0Labels = raw23420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23420 raw23420Labels permutation434 hz
    mixedMoment B raw23420step0 raw23420step0Labels = mixedMoment B raw23420step1 raw23420step1Labels := by
      have hz : ∀ j, raw23420step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23420step1 = (fun i j => raw23420step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23420step1 raw23420step0; decide +kernel
      have hl : raw23420step1Labels = raw23420step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23420step0 raw23420step0Labels permutation56 hz
    mixedMoment B raw23420step1 raw23420step1Labels = mixedMoment B raw23420step2 raw23420step2Labels := by
      have ha : raw23420step2 = (fun i j => raw23420step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23420step2 raw23420step1; decide +kernel
      have hl : raw23420step2Labels = raw23420step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23420step1 raw23420step1Labels permutation9 permutation2
    _ = mixedMoment B node607 node607Labels := by rfl

theorem canonical23421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23421 raw23421Labels = mixedMoment B node607 node607Labels := by
  calc
    mixedMoment B raw23421 raw23421Labels = mixedMoment B raw23421step0 raw23421step0Labels := by
      have hz : ∀ j, raw23421 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23421step0 = (fun i j => raw23421 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23421step0 raw23421; decide +kernel
      have hl : raw23421step0Labels = raw23421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23421 raw23421Labels permutation346 hz
    mixedMoment B raw23421step0 raw23421step0Labels = mixedMoment B raw23421step1 raw23421step1Labels := by
      have hz : ∀ j, raw23421step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23421step1 = (fun i j => raw23421step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23421step1 raw23421step0; decide +kernel
      have hl : raw23421step1Labels = raw23421step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23421step0 raw23421step0Labels permutation56 hz
    mixedMoment B raw23421step1 raw23421step1Labels = mixedMoment B raw23421step2 raw23421step2Labels := by
      have ha : raw23421step2 = (fun i j => raw23421step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23421step2 raw23421step1; decide +kernel
      have hl : raw23421step2Labels = raw23421step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23421step1 raw23421step1Labels permutation9 permutation2
    _ = mixedMoment B node607 node607Labels := by rfl

theorem canonical23422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23422 raw23422Labels = mixedMoment B node618 node618Labels := by
  calc
    mixedMoment B raw23422 raw23422Labels = mixedMoment B raw23422step0 raw23422step0Labels := by
      have hz : ∀ j, raw23422 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23422step0 = (fun i j => raw23422 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23422step0 raw23422; decide +kernel
      have hl : raw23422step0Labels = raw23422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23422 raw23422Labels permutation434 hz
    mixedMoment B raw23422step0 raw23422step0Labels = mixedMoment B raw23422step1 raw23422step1Labels := by
      have hz : ∀ j, raw23422step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23422step1 = (fun i j => raw23422step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23422step1 raw23422step0; decide +kernel
      have hl : raw23422step1Labels = raw23422step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23422step0 raw23422step0Labels permutation80 hz
    mixedMoment B raw23422step1 raw23422step1Labels = mixedMoment B raw23422step2 raw23422step2Labels := by
      have hz : ∀ j, raw23422step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23422step2 = (fun i j => raw23422step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23422step2 raw23422step1; decide +kernel
      have hl : raw23422step2Labels = raw23422step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23422step1 raw23422step1Labels permutation14 hz
    mixedMoment B raw23422step2 raw23422step2Labels = mixedMoment B raw23422step3 raw23422step3Labels := by
      have ha : raw23422step3 = (fun i j => raw23422step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23422step3 raw23422step2; decide +kernel
      have hl : raw23422step3Labels = raw23422step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23422step2 raw23422step2Labels permutation3 permutation2
    _ = mixedMoment B node618 node618Labels := by rfl

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

theorem canonical23535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23535 raw23535Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw23535 raw23535Labels = mixedMoment B raw23535step0 raw23535step0Labels := by
      have hz : ∀ j, raw23535 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23535step0 = (fun i j => raw23535 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23535step0 raw23535; decide +kernel
      have hl : raw23535step0Labels = raw23535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23535 raw23535Labels permutation434 hz
    mixedMoment B raw23535step0 raw23535step0Labels = mixedMoment B raw23535step1 raw23535step1Labels := by
      have hz : ∀ j, raw23535step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23535step1 = (fun i j => raw23535step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23535step1 raw23535step0; decide +kernel
      have hl : raw23535step1Labels = raw23535step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23535step0 raw23535step0Labels permutation80 hz
    mixedMoment B raw23535step1 raw23535step1Labels = mixedMoment B raw23535step2 raw23535step2Labels := by
      have ha : raw23535step2 = (fun i j => raw23535step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23535step2 raw23535step1; decide +kernel
      have hl : raw23535step2Labels = raw23535step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23535step1 raw23535step1Labels permutation9 permutation7
    mixedMoment B raw23535step2 raw23535step2Labels = mixedMoment B raw23535step3 raw23535step3Labels := by
      have ha : raw23535step3 = -raw23535step2 := by apply Matrix.ext; change ∀ i j, raw23535step3 i j = -(raw23535step2 i j); unfold raw23535step3 raw23535step2; decide +kernel
      have hl : raw23535step3Labels = raw23535step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23535step3 raw23535step3Labels = mixedMoment B raw23535step4 raw23535step4Labels := by
      have ha : raw23535step4 = raw23535step3 := by apply Matrix.ext; unfold raw23535step4 raw23535step3; decide +kernel
      have hl : raw23535step3Labels = labelEmbedding1 ∘ raw23535step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23535step3 raw23535step3Labels raw23535step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2229 node2229Labels := by rfl

theorem canonical23536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23536 raw23536Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw23536 raw23536Labels = mixedMoment B raw23536step0 raw23536step0Labels := by
      have hz : ∀ j, raw23536 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23536step0 = (fun i j => raw23536 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23536step0 raw23536; decide +kernel
      have hl : raw23536step0Labels = raw23536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23536 raw23536Labels permutation434 hz
    mixedMoment B raw23536step0 raw23536step0Labels = mixedMoment B raw23536step1 raw23536step1Labels := by
      have hz : ∀ j, raw23536step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23536step1 = (fun i j => raw23536step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23536step1 raw23536step0; decide +kernel
      have hl : raw23536step1Labels = raw23536step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23536step0 raw23536step0Labels permutation56 hz
    mixedMoment B raw23536step1 raw23536step1Labels = mixedMoment B raw23536step2 raw23536step2Labels := by
      have ha : raw23536step2 = (fun i j => raw23536step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23536step2 raw23536step1; decide +kernel
      have hl : raw23536step2Labels = raw23536step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23536step1 raw23536step1Labels permutation9 permutation7
    mixedMoment B raw23536step2 raw23536step2Labels = mixedMoment B raw23536step3 raw23536step3Labels := by
      have ha : raw23536step3 = -raw23536step2 := by apply Matrix.ext; change ∀ i j, raw23536step3 i j = -(raw23536step2 i j); unfold raw23536step3 raw23536step2; decide +kernel
      have hl : raw23536step3Labels = raw23536step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23536step3 raw23536step3Labels = mixedMoment B raw23536step4 raw23536step4Labels := by
      have ha : raw23536step4 = raw23536step3 := by apply Matrix.ext; unfold raw23536step4 raw23536step3; decide +kernel
      have hl : raw23536step3Labels = labelEmbedding1 ∘ raw23536step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23536step3 raw23536step3Labels raw23536step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2229 node2229Labels := by rfl

theorem canonical23537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23537 raw23537Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw23537 raw23537Labels = mixedMoment B raw23537step0 raw23537step0Labels := by
      have hz : ∀ j, raw23537 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23537step0 = (fun i j => raw23537 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23537step0 raw23537; decide +kernel
      have hl : raw23537step0Labels = raw23537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23537 raw23537Labels permutation346 hz
    mixedMoment B raw23537step0 raw23537step0Labels = mixedMoment B raw23537step1 raw23537step1Labels := by
      have hz : ∀ j, raw23537step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23537step1 = (fun i j => raw23537step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23537step1 raw23537step0; decide +kernel
      have hl : raw23537step1Labels = raw23537step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23537step0 raw23537step0Labels permutation56 hz
    mixedMoment B raw23537step1 raw23537step1Labels = mixedMoment B raw23537step2 raw23537step2Labels := by
      have ha : raw23537step2 = (fun i j => raw23537step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23537step2 raw23537step1; decide +kernel
      have hl : raw23537step2Labels = raw23537step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23537step1 raw23537step1Labels permutation9 permutation7
    mixedMoment B raw23537step2 raw23537step2Labels = mixedMoment B raw23537step3 raw23537step3Labels := by
      have ha : raw23537step3 = -raw23537step2 := by apply Matrix.ext; change ∀ i j, raw23537step3 i j = -(raw23537step2 i j); unfold raw23537step3 raw23537step2; decide +kernel
      have hl : raw23537step3Labels = raw23537step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23537step3 raw23537step3Labels = mixedMoment B raw23537step4 raw23537step4Labels := by
      have ha : raw23537step4 = raw23537step3 := by apply Matrix.ext; unfold raw23537step4 raw23537step3; decide +kernel
      have hl : raw23537step3Labels = labelEmbedding1 ∘ raw23537step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23537step3 raw23537step3Labels raw23537step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2229 node2229Labels := by rfl

theorem canonical23538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23538 raw23538Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw23538 raw23538Labels = mixedMoment B raw23538step0 raw23538step0Labels := by
      have hz : ∀ j, raw23538 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23538step0 = (fun i j => raw23538 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23538step0 raw23538; decide +kernel
      have hl : raw23538step0Labels = raw23538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23538 raw23538Labels permutation434 hz
    mixedMoment B raw23538step0 raw23538step0Labels = mixedMoment B raw23538step1 raw23538step1Labels := by
      have hz : ∀ j, raw23538step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23538step1 = (fun i j => raw23538step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23538step1 raw23538step0; decide +kernel
      have hl : raw23538step1Labels = raw23538step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23538step0 raw23538step0Labels permutation80 hz
    mixedMoment B raw23538step1 raw23538step1Labels = mixedMoment B raw23538step2 raw23538step2Labels := by
      have hz : ∀ j, raw23538step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23538step2 = (fun i j => raw23538step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23538step2 raw23538step1; decide +kernel
      have hl : raw23538step2Labels = raw23538step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23538step1 raw23538step1Labels permutation14 hz
    mixedMoment B raw23538step2 raw23538step2Labels = mixedMoment B raw23538step3 raw23538step3Labels := by
      have hz : ∀ i, raw23538step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw23538step3 = (fun i j => raw23538step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw23538step3 raw23538step2; decide +kernel
      have hl : raw23538step3Labels = (fun j => raw23538step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23538step2 raw23538step2Labels permutation4 hz
    mixedMoment B raw23538step3 raw23538step3Labels = mixedMoment B raw23538step4 raw23538step4Labels := by
      have ha : raw23538step4 = (fun i j => raw23538step3 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23538step4 raw23538step3; decide +kernel
      have hl : raw23538step4Labels = raw23538step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23538step3 raw23538step3Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical23539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23539 raw23539Labels = mixedMoment B node1519 node1519Labels := by
  calc
    mixedMoment B raw23539 raw23539Labels = mixedMoment B raw23539step0 raw23539step0Labels := by
      have hz : ∀ j, raw23539 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23539step0 = (fun i j => raw23539 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23539step0 raw23539; decide +kernel
      have hl : raw23539step0Labels = raw23539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23539 raw23539Labels permutation434 hz
    mixedMoment B raw23539step0 raw23539step0Labels = mixedMoment B raw23539step1 raw23539step1Labels := by
      have hz : ∀ j, raw23539step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23539step1 = (fun i j => raw23539step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23539step1 raw23539step0; decide +kernel
      have hl : raw23539step1Labels = raw23539step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23539step0 raw23539step0Labels permutation80 hz
    mixedMoment B raw23539step1 raw23539step1Labels = mixedMoment B raw23539step2 raw23539step2Labels := by
      have ha : raw23539step2 = (fun i j => raw23539step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23539step2 raw23539step1; decide +kernel
      have hl : raw23539step2Labels = raw23539step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23539step1 raw23539step1Labels permutation9 permutation7
    mixedMoment B raw23539step2 raw23539step2Labels = mixedMoment B raw23539step3 raw23539step3Labels := by
      have ha : raw23539step3 = -raw23539step2 := by apply Matrix.ext; change ∀ i j, raw23539step3 i j = -(raw23539step2 i j); unfold raw23539step3 raw23539step2; decide +kernel
      have hl : raw23539step3Labels = raw23539step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23539step3 raw23539step3Labels = mixedMoment B raw23539step4 raw23539step4Labels := by
      have ha : raw23539step4 = raw23539step3 := by apply Matrix.ext; unfold raw23539step4 raw23539step3; decide +kernel
      have hl : raw23539step3Labels = labelEmbedding1 ∘ raw23539step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23539step3 raw23539step3Labels raw23539step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1519 node1519Labels := by rfl

theorem canonical23540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23540 raw23540Labels = mixedMoment B node1675 node1675Labels := by
  calc
    mixedMoment B raw23540 raw23540Labels = mixedMoment B raw23540step0 raw23540step0Labels := by
      have hz : ∀ j, raw23540 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23540step0 = (fun i j => raw23540 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23540step0 raw23540; decide +kernel
      have hl : raw23540step0Labels = raw23540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23540 raw23540Labels permutation434 hz
    mixedMoment B raw23540step0 raw23540step0Labels = mixedMoment B raw23540step1 raw23540step1Labels := by
      have ha : raw23540step1 = (fun i j => raw23540step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23540step1 raw23540step0; decide +kernel
      have hl : raw23540step1Labels = raw23540step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23540step0 raw23540step0Labels permutation39 permutation7
    mixedMoment B raw23540step1 raw23540step1Labels = mixedMoment B raw23540step2 raw23540step2Labels := by
      have ha : raw23540step2 = -raw23540step1 := by apply Matrix.ext; change ∀ i j, raw23540step2 i j = -(raw23540step1 i j); unfold raw23540step2 raw23540step1; decide +kernel
      have hl : raw23540step2Labels = raw23540step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23540step2 raw23540step2Labels = mixedMoment B raw23540step3 raw23540step3Labels := by
      have ha : raw23540step3 = raw23540step2 := by apply Matrix.ext; unfold raw23540step3 raw23540step2; decide +kernel
      have hl : raw23540step2Labels = labelEmbedding1 ∘ raw23540step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23540step2 raw23540step2Labels raw23540step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1675 node1675Labels := by rfl

theorem canonical23541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23541 raw23541Labels = mixedMoment B node1675 node1675Labels := by
  calc
    mixedMoment B raw23541 raw23541Labels = mixedMoment B raw23541step0 raw23541step0Labels := by
      have hz : ∀ j, raw23541 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23541step0 = (fun i j => raw23541 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23541step0 raw23541; decide +kernel
      have hl : raw23541step0Labels = raw23541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23541 raw23541Labels permutation346 hz
    mixedMoment B raw23541step0 raw23541step0Labels = mixedMoment B raw23541step1 raw23541step1Labels := by
      have ha : raw23541step1 = (fun i j => raw23541step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23541step1 raw23541step0; decide +kernel
      have hl : raw23541step1Labels = raw23541step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23541step0 raw23541step0Labels permutation39 permutation7
    mixedMoment B raw23541step1 raw23541step1Labels = mixedMoment B raw23541step2 raw23541step2Labels := by
      have ha : raw23541step2 = -raw23541step1 := by apply Matrix.ext; change ∀ i j, raw23541step2 i j = -(raw23541step1 i j); unfold raw23541step2 raw23541step1; decide +kernel
      have hl : raw23541step2Labels = raw23541step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23541step2 raw23541step2Labels = mixedMoment B raw23541step3 raw23541step3Labels := by
      have ha : raw23541step3 = raw23541step2 := by apply Matrix.ext; unfold raw23541step3 raw23541step2; decide +kernel
      have hl : raw23541step2Labels = labelEmbedding1 ∘ raw23541step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23541step2 raw23541step2Labels raw23541step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1675 node1675Labels := by rfl

theorem canonical23542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23542 raw23542Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw23542 raw23542Labels = mixedMoment B raw23542step0 raw23542step0Labels := by
      have hz : ∀ j, raw23542 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23542step0 = (fun i j => raw23542 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23542step0 raw23542; decide +kernel
      have hl : raw23542step0Labels = raw23542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23542 raw23542Labels permutation434 hz
    mixedMoment B raw23542step0 raw23542step0Labels = mixedMoment B raw23542step1 raw23542step1Labels := by
      have hz : ∀ j, raw23542step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23542step1 = (fun i j => raw23542step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23542step1 raw23542step0; decide +kernel
      have hl : raw23542step1Labels = raw23542step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23542step0 raw23542step0Labels permutation80 hz
    mixedMoment B raw23542step1 raw23542step1Labels = mixedMoment B raw23542step2 raw23542step2Labels := by
      have ha : raw23542step2 = (fun i j => raw23542step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23542step2 raw23542step1; decide +kernel
      have hl : raw23542step2Labels = raw23542step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23542step1 raw23542step1Labels permutation9 permutation7
    mixedMoment B raw23542step2 raw23542step2Labels = mixedMoment B raw23542step3 raw23542step3Labels := by
      have ha : raw23542step3 = -raw23542step2 := by apply Matrix.ext; change ∀ i j, raw23542step3 i j = -(raw23542step2 i j); unfold raw23542step3 raw23542step2; decide +kernel
      have hl : raw23542step3Labels = raw23542step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23542step3 raw23542step3Labels = mixedMoment B raw23542step4 raw23542step4Labels := by
      have ha : raw23542step4 = raw23542step3 := by apply Matrix.ext; unfold raw23542step4 raw23542step3; decide +kernel
      have hl : raw23542step3Labels = labelEmbedding1 ∘ raw23542step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23542step3 raw23542step3Labels raw23542step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

theorem canonical23543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23543 raw23543Labels = mixedMoment B node1519 node1519Labels := by
  calc
    mixedMoment B raw23543 raw23543Labels = mixedMoment B raw23543step0 raw23543step0Labels := by
      have hz : ∀ j, raw23543 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23543step0 = (fun i j => raw23543 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23543step0 raw23543; decide +kernel
      have hl : raw23543step0Labels = raw23543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23543 raw23543Labels permutation434 hz
    mixedMoment B raw23543step0 raw23543step0Labels = mixedMoment B raw23543step1 raw23543step1Labels := by
      have hz : ∀ j, raw23543step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23543step1 = (fun i j => raw23543step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23543step1 raw23543step0; decide +kernel
      have hl : raw23543step1Labels = raw23543step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23543step0 raw23543step0Labels permutation56 hz
    mixedMoment B raw23543step1 raw23543step1Labels = mixedMoment B raw23543step2 raw23543step2Labels := by
      have ha : raw23543step2 = (fun i j => raw23543step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23543step2 raw23543step1; decide +kernel
      have hl : raw23543step2Labels = raw23543step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23543step1 raw23543step1Labels permutation9 permutation7
    mixedMoment B raw23543step2 raw23543step2Labels = mixedMoment B raw23543step3 raw23543step3Labels := by
      have ha : raw23543step3 = -raw23543step2 := by apply Matrix.ext; change ∀ i j, raw23543step3 i j = -(raw23543step2 i j); unfold raw23543step3 raw23543step2; decide +kernel
      have hl : raw23543step3Labels = raw23543step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23543step3 raw23543step3Labels = mixedMoment B raw23543step4 raw23543step4Labels := by
      have ha : raw23543step4 = raw23543step3 := by apply Matrix.ext; unfold raw23543step4 raw23543step3; decide +kernel
      have hl : raw23543step3Labels = labelEmbedding1 ∘ raw23543step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23543step3 raw23543step3Labels raw23543step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1519 node1519Labels := by rfl

theorem canonical23544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23544 raw23544Labels = mixedMoment B node1675 node1675Labels := by
  calc
    mixedMoment B raw23544 raw23544Labels = mixedMoment B raw23544step0 raw23544step0Labels := by
      have hz : ∀ j, raw23544 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23544step0 = (fun i j => raw23544 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23544step0 raw23544; decide +kernel
      have hl : raw23544step0Labels = raw23544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23544 raw23544Labels permutation434 hz
    mixedMoment B raw23544step0 raw23544step0Labels = mixedMoment B raw23544step1 raw23544step1Labels := by
      have ha : raw23544step1 = (fun i j => raw23544step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23544step1 raw23544step0; decide +kernel
      have hl : raw23544step1Labels = raw23544step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23544step0 raw23544step0Labels permutation33 permutation7
    mixedMoment B raw23544step1 raw23544step1Labels = mixedMoment B raw23544step2 raw23544step2Labels := by
      have ha : raw23544step2 = -raw23544step1 := by apply Matrix.ext; change ∀ i j, raw23544step2 i j = -(raw23544step1 i j); unfold raw23544step2 raw23544step1; decide +kernel
      have hl : raw23544step2Labels = raw23544step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23544step2 raw23544step2Labels = mixedMoment B raw23544step3 raw23544step3Labels := by
      have ha : raw23544step3 = raw23544step2 := by apply Matrix.ext; unfold raw23544step3 raw23544step2; decide +kernel
      have hl : raw23544step2Labels = labelEmbedding1 ∘ raw23544step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23544step2 raw23544step2Labels raw23544step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1675 node1675Labels := by rfl

theorem canonical23545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23545 raw23545Labels = mixedMoment B node1675 node1675Labels := by
  calc
    mixedMoment B raw23545 raw23545Labels = mixedMoment B raw23545step0 raw23545step0Labels := by
      have hz : ∀ j, raw23545 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23545step0 = (fun i j => raw23545 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23545step0 raw23545; decide +kernel
      have hl : raw23545step0Labels = raw23545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23545 raw23545Labels permutation265 hz
    mixedMoment B raw23545step0 raw23545step0Labels = mixedMoment B raw23545step1 raw23545step1Labels := by
      have ha : raw23545step1 = (fun i j => raw23545step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23545step1 raw23545step0; decide +kernel
      have hl : raw23545step1Labels = raw23545step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23545step0 raw23545step0Labels permutation39 permutation7
    mixedMoment B raw23545step1 raw23545step1Labels = mixedMoment B raw23545step2 raw23545step2Labels := by
      have ha : raw23545step2 = -raw23545step1 := by apply Matrix.ext; change ∀ i j, raw23545step2 i j = -(raw23545step1 i j); unfold raw23545step2 raw23545step1; decide +kernel
      have hl : raw23545step2Labels = raw23545step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23545step2 raw23545step2Labels = mixedMoment B raw23545step3 raw23545step3Labels := by
      have ha : raw23545step3 = raw23545step2 := by apply Matrix.ext; unfold raw23545step3 raw23545step2; decide +kernel
      have hl : raw23545step2Labels = labelEmbedding1 ∘ raw23545step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23545step2 raw23545step2Labels raw23545step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1675 node1675Labels := by rfl

theorem canonical23546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23546 raw23546Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw23546 raw23546Labels = mixedMoment B raw23546step0 raw23546step0Labels := by
      have hz : ∀ j, raw23546 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23546step0 = (fun i j => raw23546 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23546step0 raw23546; decide +kernel
      have hl : raw23546step0Labels = raw23546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23546 raw23546Labels permutation434 hz
    mixedMoment B raw23546step0 raw23546step0Labels = mixedMoment B raw23546step1 raw23546step1Labels := by
      have hz : ∀ j, raw23546step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23546step1 = (fun i j => raw23546step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23546step1 raw23546step0; decide +kernel
      have hl : raw23546step1Labels = raw23546step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23546step0 raw23546step0Labels permutation56 hz
    mixedMoment B raw23546step1 raw23546step1Labels = mixedMoment B raw23546step2 raw23546step2Labels := by
      have ha : raw23546step2 = (fun i j => raw23546step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23546step2 raw23546step1; decide +kernel
      have hl : raw23546step2Labels = raw23546step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23546step1 raw23546step1Labels permutation9 permutation7
    mixedMoment B raw23546step2 raw23546step2Labels = mixedMoment B raw23546step3 raw23546step3Labels := by
      have ha : raw23546step3 = -raw23546step2 := by apply Matrix.ext; change ∀ i j, raw23546step3 i j = -(raw23546step2 i j); unfold raw23546step3 raw23546step2; decide +kernel
      have hl : raw23546step3Labels = raw23546step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23546step3 raw23546step3Labels = mixedMoment B raw23546step4 raw23546step4Labels := by
      have ha : raw23546step4 = raw23546step3 := by apply Matrix.ext; unfold raw23546step4 raw23546step3; decide +kernel
      have hl : raw23546step3Labels = labelEmbedding1 ∘ raw23546step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23546step3 raw23546step3Labels raw23546step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

theorem canonical23547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23547 raw23547Labels = mixedMoment B node1519 node1519Labels := by
  calc
    mixedMoment B raw23547 raw23547Labels = mixedMoment B raw23547step0 raw23547step0Labels := by
      have hz : ∀ j, raw23547 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23547step0 = (fun i j => raw23547 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23547step0 raw23547; decide +kernel
      have hl : raw23547step0Labels = raw23547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23547 raw23547Labels permutation346 hz
    mixedMoment B raw23547step0 raw23547step0Labels = mixedMoment B raw23547step1 raw23547step1Labels := by
      have hz : ∀ j, raw23547step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23547step1 = (fun i j => raw23547step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23547step1 raw23547step0; decide +kernel
      have hl : raw23547step1Labels = raw23547step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23547step0 raw23547step0Labels permutation56 hz
    mixedMoment B raw23547step1 raw23547step1Labels = mixedMoment B raw23547step2 raw23547step2Labels := by
      have ha : raw23547step2 = (fun i j => raw23547step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23547step2 raw23547step1; decide +kernel
      have hl : raw23547step2Labels = raw23547step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23547step1 raw23547step1Labels permutation9 permutation7
    mixedMoment B raw23547step2 raw23547step2Labels = mixedMoment B raw23547step3 raw23547step3Labels := by
      have ha : raw23547step3 = -raw23547step2 := by apply Matrix.ext; change ∀ i j, raw23547step3 i j = -(raw23547step2 i j); unfold raw23547step3 raw23547step2; decide +kernel
      have hl : raw23547step3Labels = raw23547step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23547step3 raw23547step3Labels = mixedMoment B raw23547step4 raw23547step4Labels := by
      have ha : raw23547step4 = raw23547step3 := by apply Matrix.ext; unfold raw23547step4 raw23547step3; decide +kernel
      have hl : raw23547step3Labels = labelEmbedding1 ∘ raw23547step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23547step3 raw23547step3Labels raw23547step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1519 node1519Labels := by rfl

theorem canonical23548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23548 raw23548Labels = mixedMoment B node1675 node1675Labels := by
  calc
    mixedMoment B raw23548 raw23548Labels = mixedMoment B raw23548step0 raw23548step0Labels := by
      have hz : ∀ j, raw23548 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23548step0 = (fun i j => raw23548 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23548step0 raw23548; decide +kernel
      have hl : raw23548step0Labels = raw23548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23548 raw23548Labels permutation346 hz
    mixedMoment B raw23548step0 raw23548step0Labels = mixedMoment B raw23548step1 raw23548step1Labels := by
      have ha : raw23548step1 = (fun i j => raw23548step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23548step1 raw23548step0; decide +kernel
      have hl : raw23548step1Labels = raw23548step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23548step0 raw23548step0Labels permutation33 permutation7
    mixedMoment B raw23548step1 raw23548step1Labels = mixedMoment B raw23548step2 raw23548step2Labels := by
      have ha : raw23548step2 = -raw23548step1 := by apply Matrix.ext; change ∀ i j, raw23548step2 i j = -(raw23548step1 i j); unfold raw23548step2 raw23548step1; decide +kernel
      have hl : raw23548step2Labels = raw23548step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23548step2 raw23548step2Labels = mixedMoment B raw23548step3 raw23548step3Labels := by
      have ha : raw23548step3 = raw23548step2 := by apply Matrix.ext; unfold raw23548step3 raw23548step2; decide +kernel
      have hl : raw23548step2Labels = labelEmbedding1 ∘ raw23548step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23548step2 raw23548step2Labels raw23548step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1675 node1675Labels := by rfl

theorem canonical23549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23549 raw23549Labels = mixedMoment B node1675 node1675Labels := by
  calc
    mixedMoment B raw23549 raw23549Labels = mixedMoment B raw23549step0 raw23549step0Labels := by
      have hz : ∀ j, raw23549 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23549step0 = (fun i j => raw23549 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23549step0 raw23549; decide +kernel
      have hl : raw23549step0Labels = raw23549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23549 raw23549Labels permutation265 hz
    mixedMoment B raw23549step0 raw23549step0Labels = mixedMoment B raw23549step1 raw23549step1Labels := by
      have ha : raw23549step1 = (fun i j => raw23549step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23549step1 raw23549step0; decide +kernel
      have hl : raw23549step1Labels = raw23549step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23549step0 raw23549step0Labels permutation33 permutation7
    mixedMoment B raw23549step1 raw23549step1Labels = mixedMoment B raw23549step2 raw23549step2Labels := by
      have ha : raw23549step2 = -raw23549step1 := by apply Matrix.ext; change ∀ i j, raw23549step2 i j = -(raw23549step1 i j); unfold raw23549step2 raw23549step1; decide +kernel
      have hl : raw23549step2Labels = raw23549step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23549step2 raw23549step2Labels = mixedMoment B raw23549step3 raw23549step3Labels := by
      have ha : raw23549step3 = raw23549step2 := by apply Matrix.ext; unfold raw23549step3 raw23549step2; decide +kernel
      have hl : raw23549step2Labels = labelEmbedding1 ∘ raw23549step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23549step2 raw23549step2Labels raw23549step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1675 node1675Labels := by rfl

theorem canonical23550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23550 raw23550Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw23550 raw23550Labels = mixedMoment B raw23550step0 raw23550step0Labels := by
      have hz : ∀ j, raw23550 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23550step0 = (fun i j => raw23550 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23550step0 raw23550; decide +kernel
      have hl : raw23550step0Labels = raw23550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23550 raw23550Labels permutation346 hz
    mixedMoment B raw23550step0 raw23550step0Labels = mixedMoment B raw23550step1 raw23550step1Labels := by
      have hz : ∀ j, raw23550step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23550step1 = (fun i j => raw23550step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23550step1 raw23550step0; decide +kernel
      have hl : raw23550step1Labels = raw23550step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23550step0 raw23550step0Labels permutation56 hz
    mixedMoment B raw23550step1 raw23550step1Labels = mixedMoment B raw23550step2 raw23550step2Labels := by
      have ha : raw23550step2 = (fun i j => raw23550step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23550step2 raw23550step1; decide +kernel
      have hl : raw23550step2Labels = raw23550step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23550step1 raw23550step1Labels permutation9 permutation7
    mixedMoment B raw23550step2 raw23550step2Labels = mixedMoment B raw23550step3 raw23550step3Labels := by
      have ha : raw23550step3 = -raw23550step2 := by apply Matrix.ext; change ∀ i j, raw23550step3 i j = -(raw23550step2 i j); unfold raw23550step3 raw23550step2; decide +kernel
      have hl : raw23550step3Labels = raw23550step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23550step3 raw23550step3Labels = mixedMoment B raw23550step4 raw23550step4Labels := by
      have ha : raw23550step4 = raw23550step3 := by apply Matrix.ext; unfold raw23550step4 raw23550step3; decide +kernel
      have hl : raw23550step3Labels = labelEmbedding1 ∘ raw23550step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23550step3 raw23550step3Labels raw23550step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

theorem canonical23551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23551 raw23551Labels = mixedMoment B node1538 node1538Labels := by
  calc
    mixedMoment B raw23551 raw23551Labels = mixedMoment B raw23551step0 raw23551step0Labels := by
      have hz : ∀ j, raw23551 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23551step0 = (fun i j => raw23551 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23551step0 raw23551; decide +kernel
      have hl : raw23551step0Labels = raw23551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23551 raw23551Labels permutation434 hz
    mixedMoment B raw23551step0 raw23551step0Labels = mixedMoment B raw23551step1 raw23551step1Labels := by
      have hz : ∀ j, raw23551step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23551step1 = (fun i j => raw23551step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23551step1 raw23551step0; decide +kernel
      have hl : raw23551step1Labels = raw23551step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23551step0 raw23551step0Labels permutation80 hz
    mixedMoment B raw23551step1 raw23551step1Labels = mixedMoment B raw23551step2 raw23551step2Labels := by
      have hz : ∀ j, raw23551step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23551step2 = (fun i j => raw23551step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23551step2 raw23551step1; decide +kernel
      have hl : raw23551step2Labels = raw23551step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23551step1 raw23551step1Labels permutation14 hz
    mixedMoment B raw23551step2 raw23551step2Labels = mixedMoment B raw23551step3 raw23551step3Labels := by
      have ha : raw23551step3 = (fun i j => raw23551step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23551step3 raw23551step2; decide +kernel
      have hl : raw23551step3Labels = raw23551step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23551step2 raw23551step2Labels permutation3 permutation7
    mixedMoment B raw23551step3 raw23551step3Labels = mixedMoment B raw23551step4 raw23551step4Labels := by
      have ha : raw23551step4 = -raw23551step3 := by apply Matrix.ext; change ∀ i j, raw23551step4 i j = -(raw23551step3 i j); unfold raw23551step4 raw23551step3; decide +kernel
      have hl : raw23551step4Labels = raw23551step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23551step4 raw23551step4Labels = mixedMoment B raw23551step5 raw23551step5Labels := by
      have ha : raw23551step5 = raw23551step4 := by apply Matrix.ext; unfold raw23551step5 raw23551step4; decide +kernel
      have hl : raw23551step4Labels = labelEmbedding1 ∘ raw23551step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23551step4 raw23551step4Labels raw23551step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1538 node1538Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical184
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23552 raw23552Labels = mixedMoment B node1693 node1693Labels := by
  calc
    mixedMoment B raw23552 raw23552Labels = mixedMoment B raw23552step0 raw23552step0Labels := by
      have hz : ∀ j, raw23552 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23552step0 = (fun i j => raw23552 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23552step0 raw23552; decide +kernel
      have hl : raw23552step0Labels = raw23552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23552 raw23552Labels permutation434 hz
    mixedMoment B raw23552step0 raw23552step0Labels = mixedMoment B raw23552step1 raw23552step1Labels := by
      have hz : ∀ j, raw23552step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23552step1 = (fun i j => raw23552step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23552step1 raw23552step0; decide +kernel
      have hl : raw23552step1Labels = raw23552step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23552step0 raw23552step0Labels permutation80 hz
    mixedMoment B raw23552step1 raw23552step1Labels = mixedMoment B raw23552step2 raw23552step2Labels := by
      have ha : raw23552step2 = (fun i j => raw23552step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23552step2 raw23552step1; decide +kernel
      have hl : raw23552step2Labels = raw23552step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23552step1 raw23552step1Labels permutation9 permutation7
    mixedMoment B raw23552step2 raw23552step2Labels = mixedMoment B raw23552step3 raw23552step3Labels := by
      have ha : raw23552step3 = -raw23552step2 := by apply Matrix.ext; change ∀ i j, raw23552step3 i j = -(raw23552step2 i j); unfold raw23552step3 raw23552step2; decide +kernel
      have hl : raw23552step3Labels = raw23552step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23552step3 raw23552step3Labels = mixedMoment B raw23552step4 raw23552step4Labels := by
      have ha : raw23552step4 = raw23552step3 := by apply Matrix.ext; unfold raw23552step4 raw23552step3; decide +kernel
      have hl : raw23552step3Labels = labelEmbedding1 ∘ raw23552step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23552step3 raw23552step3Labels raw23552step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1693 node1693Labels := by rfl

theorem canonical23553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23553 raw23553Labels = mixedMoment B node1693 node1693Labels := by
  calc
    mixedMoment B raw23553 raw23553Labels = mixedMoment B raw23553step0 raw23553step0Labels := by
      have hz : ∀ j, raw23553 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23553step0 = (fun i j => raw23553 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23553step0 raw23553; decide +kernel
      have hl : raw23553step0Labels = raw23553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23553 raw23553Labels permutation434 hz
    mixedMoment B raw23553step0 raw23553step0Labels = mixedMoment B raw23553step1 raw23553step1Labels := by
      have hz : ∀ j, raw23553step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23553step1 = (fun i j => raw23553step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23553step1 raw23553step0; decide +kernel
      have hl : raw23553step1Labels = raw23553step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23553step0 raw23553step0Labels permutation56 hz
    mixedMoment B raw23553step1 raw23553step1Labels = mixedMoment B raw23553step2 raw23553step2Labels := by
      have ha : raw23553step2 = (fun i j => raw23553step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23553step2 raw23553step1; decide +kernel
      have hl : raw23553step2Labels = raw23553step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23553step1 raw23553step1Labels permutation9 permutation7
    mixedMoment B raw23553step2 raw23553step2Labels = mixedMoment B raw23553step3 raw23553step3Labels := by
      have ha : raw23553step3 = -raw23553step2 := by apply Matrix.ext; change ∀ i j, raw23553step3 i j = -(raw23553step2 i j); unfold raw23553step3 raw23553step2; decide +kernel
      have hl : raw23553step3Labels = raw23553step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23553step3 raw23553step3Labels = mixedMoment B raw23553step4 raw23553step4Labels := by
      have ha : raw23553step4 = raw23553step3 := by apply Matrix.ext; unfold raw23553step4 raw23553step3; decide +kernel
      have hl : raw23553step3Labels = labelEmbedding1 ∘ raw23553step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23553step3 raw23553step3Labels raw23553step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1693 node1693Labels := by rfl

theorem canonical23554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23554 raw23554Labels = mixedMoment B node1693 node1693Labels := by
  calc
    mixedMoment B raw23554 raw23554Labels = mixedMoment B raw23554step0 raw23554step0Labels := by
      have hz : ∀ j, raw23554 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23554step0 = (fun i j => raw23554 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23554step0 raw23554; decide +kernel
      have hl : raw23554step0Labels = raw23554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23554 raw23554Labels permutation346 hz
    mixedMoment B raw23554step0 raw23554step0Labels = mixedMoment B raw23554step1 raw23554step1Labels := by
      have hz : ∀ j, raw23554step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23554step1 = (fun i j => raw23554step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23554step1 raw23554step0; decide +kernel
      have hl : raw23554step1Labels = raw23554step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23554step0 raw23554step0Labels permutation56 hz
    mixedMoment B raw23554step1 raw23554step1Labels = mixedMoment B raw23554step2 raw23554step2Labels := by
      have ha : raw23554step2 = (fun i j => raw23554step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23554step2 raw23554step1; decide +kernel
      have hl : raw23554step2Labels = raw23554step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23554step1 raw23554step1Labels permutation9 permutation7
    mixedMoment B raw23554step2 raw23554step2Labels = mixedMoment B raw23554step3 raw23554step3Labels := by
      have ha : raw23554step3 = -raw23554step2 := by apply Matrix.ext; change ∀ i j, raw23554step3 i j = -(raw23554step2 i j); unfold raw23554step3 raw23554step2; decide +kernel
      have hl : raw23554step3Labels = raw23554step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23554step3 raw23554step3Labels = mixedMoment B raw23554step4 raw23554step4Labels := by
      have ha : raw23554step4 = raw23554step3 := by apply Matrix.ext; unfold raw23554step4 raw23554step3; decide +kernel
      have hl : raw23554step3Labels = labelEmbedding1 ∘ raw23554step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23554step3 raw23554step3Labels raw23554step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1693 node1693Labels := by rfl

theorem canonical23555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23555 raw23555Labels = mixedMoment B node1754 node1754Labels := by
  calc
    mixedMoment B raw23555 raw23555Labels = mixedMoment B raw23555step0 raw23555step0Labels := by
      have hz : ∀ j, raw23555 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23555step0 = (fun i j => raw23555 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23555step0 raw23555; decide +kernel
      have hl : raw23555step0Labels = raw23555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23555 raw23555Labels permutation434 hz
    mixedMoment B raw23555step0 raw23555step0Labels = mixedMoment B raw23555step1 raw23555step1Labels := by
      have hz : ∀ j, raw23555step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23555step1 = (fun i j => raw23555step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23555step1 raw23555step0; decide +kernel
      have hl : raw23555step1Labels = raw23555step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23555step0 raw23555step0Labels permutation80 hz
    mixedMoment B raw23555step1 raw23555step1Labels = mixedMoment B raw23555step2 raw23555step2Labels := by
      have hz : ∀ j, raw23555step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23555step2 = (fun i j => raw23555step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23555step2 raw23555step1; decide +kernel
      have hl : raw23555step2Labels = raw23555step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23555step1 raw23555step1Labels permutation14 hz
    mixedMoment B raw23555step2 raw23555step2Labels = mixedMoment B raw23555step3 raw23555step3Labels := by
      have ha : raw23555step3 = (fun i j => raw23555step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23555step3 raw23555step2; decide +kernel
      have hl : raw23555step3Labels = raw23555step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23555step2 raw23555step2Labels permutation3 permutation7
    mixedMoment B raw23555step3 raw23555step3Labels = mixedMoment B raw23555step4 raw23555step4Labels := by
      have ha : raw23555step4 = -raw23555step3 := by apply Matrix.ext; change ∀ i j, raw23555step4 i j = -(raw23555step3 i j); unfold raw23555step4 raw23555step3; decide +kernel
      have hl : raw23555step4Labels = raw23555step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23555step4 raw23555step4Labels = mixedMoment B raw23555step5 raw23555step5Labels := by
      have ha : raw23555step5 = raw23555step4 := by apply Matrix.ext; unfold raw23555step5 raw23555step4; decide +kernel
      have hl : raw23555step4Labels = labelEmbedding1 ∘ raw23555step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23555step4 raw23555step4Labels raw23555step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1754 node1754Labels := by rfl

theorem canonical23556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23556 raw23556Labels = mixedMoment B node1756 node1756Labels := by
  calc
    mixedMoment B raw23556 raw23556Labels = mixedMoment B raw23556step0 raw23556step0Labels := by
      have hz : ∀ j, raw23556 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23556step0 = (fun i j => raw23556 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23556step0 raw23556; decide +kernel
      have hl : raw23556step0Labels = raw23556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23556 raw23556Labels permutation434 hz
    mixedMoment B raw23556step0 raw23556step0Labels = mixedMoment B raw23556step1 raw23556step1Labels := by
      have hz : ∀ j, raw23556step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23556step1 = (fun i j => raw23556step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23556step1 raw23556step0; decide +kernel
      have hl : raw23556step1Labels = raw23556step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23556step0 raw23556step0Labels permutation80 hz
    mixedMoment B raw23556step1 raw23556step1Labels = mixedMoment B raw23556step2 raw23556step2Labels := by
      have hz : ∀ j, raw23556step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23556step2 = (fun i j => raw23556step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23556step2 raw23556step1; decide +kernel
      have hl : raw23556step2Labels = raw23556step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23556step1 raw23556step1Labels permutation14 hz
    mixedMoment B raw23556step2 raw23556step2Labels = mixedMoment B raw23556step3 raw23556step3Labels := by
      have ha : raw23556step3 = (fun i j => raw23556step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23556step3 raw23556step2; decide +kernel
      have hl : raw23556step3Labels = raw23556step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23556step2 raw23556step2Labels permutation3 permutation7
    mixedMoment B raw23556step3 raw23556step3Labels = mixedMoment B raw23556step4 raw23556step4Labels := by
      have ha : raw23556step4 = -raw23556step3 := by apply Matrix.ext; change ∀ i j, raw23556step4 i j = -(raw23556step3 i j); unfold raw23556step4 raw23556step3; decide +kernel
      have hl : raw23556step4Labels = raw23556step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23556step4 raw23556step4Labels = mixedMoment B raw23556step5 raw23556step5Labels := by
      have ha : raw23556step5 = raw23556step4 := by apply Matrix.ext; unfold raw23556step5 raw23556step4; decide +kernel
      have hl : raw23556step4Labels = labelEmbedding1 ∘ raw23556step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23556step4 raw23556step4Labels raw23556step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1756 node1756Labels := by rfl

theorem canonical23557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23557 raw23557Labels = mixedMoment B node1095 node1095Labels := by
  calc
    mixedMoment B raw23557 raw23557Labels = mixedMoment B raw23557step0 raw23557step0Labels := by
      have hz : ∀ j, raw23557 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23557step0 = (fun i j => raw23557 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23557step0 raw23557; decide +kernel
      have hl : raw23557step0Labels = raw23557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23557 raw23557Labels permutation434 hz
    mixedMoment B raw23557step0 raw23557step0Labels = mixedMoment B raw23557step1 raw23557step1Labels := by
      have hz : ∀ j, raw23557step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23557step1 = (fun i j => raw23557step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23557step1 raw23557step0; decide +kernel
      have hl : raw23557step1Labels = raw23557step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23557step0 raw23557step0Labels permutation80 hz
    mixedMoment B raw23557step1 raw23557step1Labels = mixedMoment B raw23557step2 raw23557step2Labels := by
      have hz : ∀ j, raw23557step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23557step2 = (fun i j => raw23557step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23557step2 raw23557step1; decide +kernel
      have hl : raw23557step2Labels = raw23557step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23557step1 raw23557step1Labels permutation14 hz
    mixedMoment B raw23557step2 raw23557step2Labels = mixedMoment B raw23557step3 raw23557step3Labels := by
      have ha : raw23557step3 = (fun i j => raw23557step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23557step3 raw23557step2; decide +kernel
      have hl : raw23557step3Labels = raw23557step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23557step2 raw23557step2Labels permutation3 permutation2
    _ = mixedMoment B node1095 node1095Labels := by rfl

theorem canonical23558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23558 raw23558Labels = mixedMoment B node608 node608Labels := by
  calc
    mixedMoment B raw23558 raw23558Labels = mixedMoment B raw23558step0 raw23558step0Labels := by
      have hz : ∀ j, raw23558 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23558step0 = (fun i j => raw23558 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23558step0 raw23558; decide +kernel
      have hl : raw23558step0Labels = raw23558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23558 raw23558Labels permutation434 hz
    mixedMoment B raw23558step0 raw23558step0Labels = mixedMoment B raw23558step1 raw23558step1Labels := by
      have hz : ∀ j, raw23558step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23558step1 = (fun i j => raw23558step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23558step1 raw23558step0; decide +kernel
      have hl : raw23558step1Labels = raw23558step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23558step0 raw23558step0Labels permutation80 hz
    mixedMoment B raw23558step1 raw23558step1Labels = mixedMoment B raw23558step2 raw23558step2Labels := by
      have ha : raw23558step2 = (fun i j => raw23558step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23558step2 raw23558step1; decide +kernel
      have hl : raw23558step2Labels = raw23558step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23558step1 raw23558step1Labels permutation9 permutation2
    _ = mixedMoment B node608 node608Labels := by rfl

theorem canonical23559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23559 raw23559Labels = mixedMoment B node608 node608Labels := by
  calc
    mixedMoment B raw23559 raw23559Labels = mixedMoment B raw23559step0 raw23559step0Labels := by
      have hz : ∀ j, raw23559 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23559step0 = (fun i j => raw23559 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23559step0 raw23559; decide +kernel
      have hl : raw23559step0Labels = raw23559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23559 raw23559Labels permutation434 hz
    mixedMoment B raw23559step0 raw23559step0Labels = mixedMoment B raw23559step1 raw23559step1Labels := by
      have hz : ∀ j, raw23559step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23559step1 = (fun i j => raw23559step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23559step1 raw23559step0; decide +kernel
      have hl : raw23559step1Labels = raw23559step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23559step0 raw23559step0Labels permutation56 hz
    mixedMoment B raw23559step1 raw23559step1Labels = mixedMoment B raw23559step2 raw23559step2Labels := by
      have ha : raw23559step2 = (fun i j => raw23559step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23559step2 raw23559step1; decide +kernel
      have hl : raw23559step2Labels = raw23559step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23559step1 raw23559step1Labels permutation9 permutation2
    _ = mixedMoment B node608 node608Labels := by rfl

theorem canonical23560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23560 raw23560Labels = mixedMoment B node608 node608Labels := by
  calc
    mixedMoment B raw23560 raw23560Labels = mixedMoment B raw23560step0 raw23560step0Labels := by
      have hz : ∀ j, raw23560 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23560step0 = (fun i j => raw23560 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23560step0 raw23560; decide +kernel
      have hl : raw23560step0Labels = raw23560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23560 raw23560Labels permutation346 hz
    mixedMoment B raw23560step0 raw23560step0Labels = mixedMoment B raw23560step1 raw23560step1Labels := by
      have hz : ∀ j, raw23560step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23560step1 = (fun i j => raw23560step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23560step1 raw23560step0; decide +kernel
      have hl : raw23560step1Labels = raw23560step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23560step0 raw23560step0Labels permutation56 hz
    mixedMoment B raw23560step1 raw23560step1Labels = mixedMoment B raw23560step2 raw23560step2Labels := by
      have ha : raw23560step2 = (fun i j => raw23560step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23560step2 raw23560step1; decide +kernel
      have hl : raw23560step2Labels = raw23560step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23560step1 raw23560step1Labels permutation9 permutation2
    _ = mixedMoment B node608 node608Labels := by rfl

theorem canonical23561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23561 raw23561Labels = mixedMoment B node619 node619Labels := by
  calc
    mixedMoment B raw23561 raw23561Labels = mixedMoment B raw23561step0 raw23561step0Labels := by
      have hz : ∀ j, raw23561 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23561step0 = (fun i j => raw23561 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23561step0 raw23561; decide +kernel
      have hl : raw23561step0Labels = raw23561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23561 raw23561Labels permutation434 hz
    mixedMoment B raw23561step0 raw23561step0Labels = mixedMoment B raw23561step1 raw23561step1Labels := by
      have hz : ∀ j, raw23561step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23561step1 = (fun i j => raw23561step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23561step1 raw23561step0; decide +kernel
      have hl : raw23561step1Labels = raw23561step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23561step0 raw23561step0Labels permutation80 hz
    mixedMoment B raw23561step1 raw23561step1Labels = mixedMoment B raw23561step2 raw23561step2Labels := by
      have hz : ∀ j, raw23561step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23561step2 = (fun i j => raw23561step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23561step2 raw23561step1; decide +kernel
      have hl : raw23561step2Labels = raw23561step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23561step1 raw23561step1Labels permutation14 hz
    mixedMoment B raw23561step2 raw23561step2Labels = mixedMoment B raw23561step3 raw23561step3Labels := by
      have ha : raw23561step3 = (fun i j => raw23561step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23561step3 raw23561step2; decide +kernel
      have hl : raw23561step3Labels = raw23561step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23561step2 raw23561step2Labels permutation3 permutation2
    _ = mixedMoment B node619 node619Labels := by rfl

theorem canonical23562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23562 raw23562Labels = mixedMoment B node620 node620Labels := by
  calc
    mixedMoment B raw23562 raw23562Labels = mixedMoment B raw23562step0 raw23562step0Labels := by
      have hz : ∀ j, raw23562 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23562step0 = (fun i j => raw23562 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23562step0 raw23562; decide +kernel
      have hl : raw23562step0Labels = raw23562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23562 raw23562Labels permutation434 hz
    mixedMoment B raw23562step0 raw23562step0Labels = mixedMoment B raw23562step1 raw23562step1Labels := by
      have hz : ∀ j, raw23562step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23562step1 = (fun i j => raw23562step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23562step1 raw23562step0; decide +kernel
      have hl : raw23562step1Labels = raw23562step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23562step0 raw23562step0Labels permutation80 hz
    mixedMoment B raw23562step1 raw23562step1Labels = mixedMoment B raw23562step2 raw23562step2Labels := by
      have hz : ∀ j, raw23562step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23562step2 = (fun i j => raw23562step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23562step2 raw23562step1; decide +kernel
      have hl : raw23562step2Labels = raw23562step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23562step1 raw23562step1Labels permutation14 hz
    _ = mixedMoment B node620 node620Labels := by rfl

theorem canonical23571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23571 raw23571Labels = mixedMoment B node2006 node2006Labels := by
  calc
    mixedMoment B raw23571 raw23571Labels = mixedMoment B raw23571step0 raw23571step0Labels := by
      have hz : ∀ j, raw23571 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23571step0 = (fun i j => raw23571 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23571step0 raw23571; decide +kernel
      have hl : raw23571step0Labels = raw23571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23571 raw23571Labels permutation346 hz
    mixedMoment B raw23571step0 raw23571step0Labels = mixedMoment B raw23571step1 raw23571step1Labels := by
      have ha : raw23571step1 = (fun i j => raw23571step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23571step1 raw23571step0; decide +kernel
      have hl : raw23571step1Labels = raw23571step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23571step0 raw23571step0Labels permutation33 permutation2
    _ = mixedMoment B node2006 node2006Labels := by rfl

theorem canonical23572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23572 raw23572Labels = mixedMoment B node2006 node2006Labels := by
  calc
    mixedMoment B raw23572 raw23572Labels = mixedMoment B raw23572step0 raw23572step0Labels := by
      have hz : ∀ j, raw23572 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23572step0 = (fun i j => raw23572 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23572step0 raw23572; decide +kernel
      have hl : raw23572step0Labels = raw23572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23572 raw23572Labels permutation265 hz
    mixedMoment B raw23572step0 raw23572step0Labels = mixedMoment B raw23572step1 raw23572step1Labels := by
      have ha : raw23572step1 = (fun i j => raw23572step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23572step1 raw23572step0; decide +kernel
      have hl : raw23572step1Labels = raw23572step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23572step0 raw23572step0Labels permutation33 permutation2
    _ = mixedMoment B node2006 node2006Labels := by rfl

theorem canonical23573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23573 raw23573Labels = mixedMoment B node1953 node1953Labels := by
  calc
    mixedMoment B raw23573 raw23573Labels = mixedMoment B raw23573step0 raw23573step0Labels := by
      have hz : ∀ j, raw23573 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23573step0 = (fun i j => raw23573 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23573step0 raw23573; decide +kernel
      have hl : raw23573step0Labels = raw23573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23573 raw23573Labels permutation346 hz
    mixedMoment B raw23573step0 raw23573step0Labels = mixedMoment B raw23573step1 raw23573step1Labels := by
      have hz : ∀ j, raw23573step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23573step1 = (fun i j => raw23573step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23573step1 raw23573step0; decide +kernel
      have hl : raw23573step1Labels = raw23573step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23573step0 raw23573step0Labels permutation56 hz
    mixedMoment B raw23573step1 raw23573step1Labels = mixedMoment B raw23573step2 raw23573step2Labels := by
      have ha : raw23573step2 = (fun i j => raw23573step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23573step2 raw23573step1; decide +kernel
      have hl : raw23573step2Labels = raw23573step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23573step1 raw23573step1Labels permutation9 permutation2
    _ = mixedMoment B node1953 node1953Labels := by rfl

theorem canonical23574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23574 raw23574Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw23574 raw23574Labels = mixedMoment B raw23574step0 raw23574step0Labels := by
      have hz : ∀ j, raw23574 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23574step0 = (fun i j => raw23574 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23574step0 raw23574; decide +kernel
      have hl : raw23574step0Labels = raw23574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23574 raw23574Labels permutation346 hz
    mixedMoment B raw23574step0 raw23574step0Labels = mixedMoment B raw23574step1 raw23574step1Labels := by
      have hz : ∀ j, raw23574step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23574step1 = (fun i j => raw23574step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23574step1 raw23574step0; decide +kernel
      have hl : raw23574step1Labels = raw23574step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23574step0 raw23574step0Labels permutation56 hz
    mixedMoment B raw23574step1 raw23574step1Labels = mixedMoment B raw23574step2 raw23574step2Labels := by
      have ha : raw23574step2 = (fun i j => raw23574step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23574step2 raw23574step1; decide +kernel
      have hl : raw23574step2Labels = raw23574step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23574step1 raw23574step1Labels permutation9 permutation2
    _ = mixedMoment B node2228 node2228Labels := by rfl

theorem canonical23639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23639 raw23639Labels = mixedMoment B node569 node569Labels := by
  calc
    mixedMoment B raw23639 raw23639Labels = mixedMoment B raw23639step0 raw23639step0Labels := by
      have hz : ∀ j, raw23639 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23639step0 = (fun i j => raw23639 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23639step0 raw23639; decide +kernel
      have hl : raw23639step0Labels = raw23639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23639 raw23639Labels permutation346 hz
    mixedMoment B raw23639step0 raw23639step0Labels = mixedMoment B raw23639step1 raw23639step1Labels := by
      have ha : raw23639step1 = (fun i j => raw23639step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23639step1 raw23639step0; decide +kernel
      have hl : raw23639step1Labels = raw23639step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23639step0 raw23639step0Labels permutation38 permutation2
    _ = mixedMoment B node569 node569Labels := by rfl

theorem canonical23640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23640 raw23640Labels = mixedMoment B node569 node569Labels := by
  calc
    mixedMoment B raw23640 raw23640Labels = mixedMoment B raw23640step0 raw23640step0Labels := by
      have hz : ∀ j, raw23640 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23640step0 = (fun i j => raw23640 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23640step0 raw23640; decide +kernel
      have hl : raw23640step0Labels = raw23640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23640 raw23640Labels permutation265 hz
    mixedMoment B raw23640step0 raw23640step0Labels = mixedMoment B raw23640step1 raw23640step1Labels := by
      have ha : raw23640step1 = (fun i j => raw23640step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23640step1 raw23640step0; decide +kernel
      have hl : raw23640step1Labels = raw23640step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23640step0 raw23640step0Labels permutation38 permutation2
    _ = mixedMoment B node569 node569Labels := by rfl

theorem canonical23641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23641 raw23641Labels = mixedMoment B node595 node595Labels := by
  calc
    mixedMoment B raw23641 raw23641Labels = mixedMoment B raw23641step0 raw23641step0Labels := by
      have hz : ∀ j, raw23641 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23641step0 = (fun i j => raw23641 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23641step0 raw23641; decide +kernel
      have hl : raw23641step0Labels = raw23641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23641 raw23641Labels permutation346 hz
    mixedMoment B raw23641step0 raw23641step0Labels = mixedMoment B raw23641step1 raw23641step1Labels := by
      have hz : ∀ j, raw23641step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23641step1 = (fun i j => raw23641step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23641step1 raw23641step0; decide +kernel
      have hl : raw23641step1Labels = raw23641step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23641step0 raw23641step0Labels permutation56 hz
    _ = mixedMoment B node595 node595Labels := by rfl

theorem canonical23642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23642 raw23642Labels = mixedMoment B node576 node576Labels := by
  calc
    mixedMoment B raw23642 raw23642Labels = mixedMoment B raw23642step0 raw23642step0Labels := by
      have hz : ∀ j, raw23642 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23642step0 = (fun i j => raw23642 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23642step0 raw23642; decide +kernel
      have hl : raw23642step0Labels = raw23642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23642 raw23642Labels permutation346 hz
    mixedMoment B raw23642step0 raw23642step0Labels = mixedMoment B raw23642step1 raw23642step1Labels := by
      have hz : ∀ j, raw23642step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23642step1 = (fun i j => raw23642step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23642step1 raw23642step0; decide +kernel
      have hl : raw23642step1Labels = raw23642step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23642step0 raw23642step0Labels permutation56 hz
    mixedMoment B raw23642step1 raw23642step1Labels = mixedMoment B raw23642step2 raw23642step2Labels := by
      have ha : raw23642step2 = (fun i j => raw23642step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23642step2 raw23642step1; decide +kernel
      have hl : raw23642step2Labels = raw23642step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23642step1 raw23642step1Labels permutation9 permutation2
    _ = mixedMoment B node576 node576Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3471 raw3471Labels = mixedMoment B node4508 node4508Labels := by
  calc
    mixedMoment B raw3471 raw3471Labels = mixedMoment B raw3471step0 raw3471step0Labels := by
      have hz : ∀ j, raw3471 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3471step0 = (fun i j => raw3471 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3471step0 raw3471; decide +kernel
      have hl : raw3471step0Labels = raw3471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3471 raw3471Labels permutation434 hz
    mixedMoment B raw3471step0 raw3471step0Labels = mixedMoment B raw3471step1 raw3471step1Labels := by
      have hz : ∀ j, raw3471step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3471step1 = (fun i j => raw3471step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3471step1 raw3471step0; decide +kernel
      have hl : raw3471step1Labels = raw3471step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3471step0 raw3471step0Labels permutation80 hz
    mixedMoment B raw3471step1 raw3471step1Labels = mixedMoment B raw3471step2 raw3471step2Labels := by
      have hz : ∀ j, raw3471step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3471step2 = (fun i j => raw3471step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3471step2 raw3471step1; decide +kernel
      have hl : raw3471step2Labels = raw3471step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3471step1 raw3471step1Labels permutation14 hz
    _ = mixedMoment B node4508 node4508Labels := by rfl

theorem canonical3475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3475 raw3475Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw3475 raw3475Labels = mixedMoment B raw3475step0 raw3475step0Labels := by
      have hz : ∀ j, raw3475 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3475step0 = (fun i j => raw3475 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3475step0 raw3475; decide +kernel
      have hl : raw3475step0Labels = raw3475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3475 raw3475Labels permutation434 hz
    mixedMoment B raw3475step0 raw3475step0Labels = mixedMoment B raw3475step1 raw3475step1Labels := by
      have hz : ∀ j, raw3475step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3475step1 = (fun i j => raw3475step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3475step1 raw3475step0; decide +kernel
      have hl : raw3475step1Labels = raw3475step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3475step0 raw3475step0Labels permutation80 hz
    mixedMoment B raw3475step1 raw3475step1Labels = mixedMoment B raw3475step2 raw3475step2Labels := by
      have hz : ∀ j, raw3475step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3475step2 = (fun i j => raw3475step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3475step2 raw3475step1; decide +kernel
      have hl : raw3475step2Labels = raw3475step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3475step1 raw3475step1Labels permutation14 hz
    mixedMoment B raw3475step2 raw3475step2Labels = mixedMoment B raw3475step3 raw3475step3Labels := by
      have ha : raw3475step3 = (fun i j => raw3475step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3475step3 raw3475step2; decide +kernel
      have hl : raw3475step3Labels = raw3475step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3475step2 raw3475step2Labels permutation3 permutation7
    mixedMoment B raw3475step3 raw3475step3Labels = mixedMoment B raw3475step4 raw3475step4Labels := by
      have ha : raw3475step4 = -raw3475step3 := by apply Matrix.ext; change ∀ i j, raw3475step4 i j = -(raw3475step3 i j); unfold raw3475step4 raw3475step3; decide +kernel
      have hl : raw3475step4Labels = raw3475step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3475step4 raw3475step4Labels = mixedMoment B raw3475step5 raw3475step5Labels := by
      have ha : raw3475step5 = raw3475step4 := by apply Matrix.ext; unfold raw3475step5 raw3475step4; decide +kernel
      have hl : raw3475step4Labels = labelEmbedding10 ∘ raw3475step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3475step4 raw3475step4Labels raw3475step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

theorem canonical3517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3517 raw3517Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw3517 raw3517Labels = mixedMoment B raw3517step0 raw3517step0Labels := by
      have hz : ∀ j, raw3517 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3517step0 = (fun i j => raw3517 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3517step0 raw3517; decide +kernel
      have hl : raw3517step0Labels = raw3517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3517 raw3517Labels permutation590 hz
    mixedMoment B raw3517step0 raw3517step0Labels = mixedMoment B raw3517step1 raw3517step1Labels := by
      have hz : ∀ j, raw3517step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3517step1 = (fun i j => raw3517step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3517step1 raw3517step0; decide +kernel
      have hl : raw3517step1Labels = raw3517step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3517step0 raw3517step0Labels permutation104 hz
    mixedMoment B raw3517step1 raw3517step1Labels = mixedMoment B raw3517step2 raw3517step2Labels := by
      have hz : ∀ j, raw3517step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3517step2 = (fun i j => raw3517step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3517step2 raw3517step1; decide +kernel
      have hl : raw3517step2Labels = raw3517step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3517step1 raw3517step1Labels permutation20 hz
    mixedMoment B raw3517step2 raw3517step2Labels = mixedMoment B raw3517step3 raw3517step3Labels := by
      have hz : ∀ j, raw3517step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw3517step3 = (fun i j => raw3517step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw3517step3 raw3517step2; decide +kernel
      have hl : raw3517step3Labels = raw3517step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3517step2 raw3517step2Labels permutation4 hz
    _ = mixedMoment B node4085 node4085Labels := by rfl

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

theorem canonical837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw837 raw837Labels = mixedMoment B node4190 node4190Labels := by
  calc
    mixedMoment B raw837 raw837Labels = mixedMoment B raw837step0 raw837step0Labels := by
      have ha : raw837step0 = (fun i j => raw837 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw837step0 raw837; decide +kernel
      have hl : raw837step0Labels = raw837Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw837 raw837Labels permutation2 permutation4
    mixedMoment B raw837step0 raw837step0Labels = mixedMoment B raw837step1 raw837step1Labels := by
      have ha : raw837step1 = raw837step0 := by apply Matrix.ext; unfold raw837step1 raw837step0; decide +kernel
      have hl : raw837step0Labels = labelEmbedding7 ∘ raw837step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw837step0 raw837step0Labels raw837step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4190 node4190Labels := by rfl

theorem canonical838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw838 raw838Labels = mixedMoment B node618 node618Labels := by
  calc
    mixedMoment B raw838 raw838Labels = mixedMoment B raw838step0 raw838step0Labels := by
      have ha : raw838step0 = (fun i j => raw838 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw838step0 raw838; decide +kernel
      have hl : raw838step0Labels = raw838Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw838 raw838Labels permutation2 permutation4
    _ = mixedMoment B node618 node618Labels := by rfl

theorem canonical839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw839 raw839Labels = mixedMoment B node1527 node1527Labels := by
  calc
    mixedMoment B raw839 raw839Labels = mixedMoment B raw839step0 raw839step0Labels := by
      have ha : raw839step0 = (fun i j => raw839 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw839step0 raw839; decide +kernel
      have hl : raw839step0Labels = raw839Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw839 raw839Labels permutation2 permutation6
    mixedMoment B raw839step0 raw839step0Labels = mixedMoment B raw839step1 raw839step1Labels := by
      have ha : raw839step1 = -raw839step0 := by apply Matrix.ext; change ∀ i j, raw839step1 i j = -(raw839step0 i j); unfold raw839step1 raw839step0; decide +kernel
      have hl : raw839step1Labels = raw839step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw839step1 raw839step1Labels = mixedMoment B raw839step2 raw839step2Labels := by
      have ha : raw839step2 = raw839step1 := by apply Matrix.ext; unfold raw839step2 raw839step1; decide +kernel
      have hl : raw839step1Labels = labelEmbedding1 ∘ raw839step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw839step1 raw839step1Labels raw839step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1527 node1527Labels := by rfl

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

theorem canonical1155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1155 raw1155Labels = mixedMoment B node4359 node4359Labels := by
  calc
    mixedMoment B raw1155 raw1155Labels = mixedMoment B raw1155step0 raw1155step0Labels := by
      have ha : raw1155step0 = (fun i j => raw1155 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1155step0 raw1155; decide +kernel
      have hl : raw1155step0Labels = raw1155Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1155 raw1155Labels permutation8 permutation4
    mixedMoment B raw1155step0 raw1155step0Labels = mixedMoment B raw1155step1 raw1155step1Labels := by
      have ha : raw1155step1 = raw1155step0 := by apply Matrix.ext; unfold raw1155step1 raw1155step0; decide +kernel
      have hl : raw1155step0Labels = labelEmbedding7 ∘ raw1155step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1155step0 raw1155step0Labels raw1155step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4359 node4359Labels := by rfl

theorem canonical1156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1156 raw1156Labels = mixedMoment B node937 node937Labels := by
  calc
    mixedMoment B raw1156 raw1156Labels = mixedMoment B raw1156step0 raw1156step0Labels := by
      have ha : raw1156step0 = (fun i j => raw1156 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1156step0 raw1156; decide +kernel
      have hl : raw1156step0Labels = raw1156Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1156 raw1156Labels permutation8 permutation4
    _ = mixedMoment B node937 node937Labels := by rfl

theorem canonical1157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1157 raw1157Labels = mixedMoment B node1683 node1683Labels := by
  calc
    mixedMoment B raw1157 raw1157Labels = mixedMoment B raw1157step0 raw1157step0Labels := by
      have ha : raw1157step0 = (fun i j => raw1157 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1157step0 raw1157; decide +kernel
      have hl : raw1157step0Labels = raw1157Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1157 raw1157Labels permutation8 permutation6
    mixedMoment B raw1157step0 raw1157step0Labels = mixedMoment B raw1157step1 raw1157step1Labels := by
      have ha : raw1157step1 = -raw1157step0 := by apply Matrix.ext; change ∀ i j, raw1157step1 i j = -(raw1157step0 i j); unfold raw1157step1 raw1157step0; decide +kernel
      have hl : raw1157step1Labels = raw1157step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1157step1 raw1157step1Labels = mixedMoment B raw1157step2 raw1157step2Labels := by
      have ha : raw1157step2 = raw1157step1 := by apply Matrix.ext; unfold raw1157step2 raw1157step1; decide +kernel
      have hl : raw1157step1Labels = labelEmbedding1 ∘ raw1157step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1157step1 raw1157step1Labels raw1157step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1683 node1683Labels := by rfl

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

theorem sum_fin_six {R : Type*} [AddCommMonoid R] (f : Fin 6 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) = _
  ac_rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4190 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4190 node4190Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node618 node618Labels + mixedMoment B node1527 node1527Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw837 singletonSmall4190
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4190) = raw837Labels := by decide +kernel
  rw [hl, canonical837 B hB] at h
  have hc0 : mixedMoment B raw837 (Fin.cases (0 : Fin 2) singletonSmall4190) =
      mixedMoment B node618 node618Labels := by
    have ha : raw837 = raw838 := by apply Matrix.ext; unfold raw837 raw838; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4190 = raw838Labels := by decide +kernel
    rw [ha, hj, canonical838 B hB]
  have hc1 : mixedMoment B raw837 (Fin.cases (1 : Fin 2) singletonSmall4190) =
      mixedMoment B node1527 node1527Labels := by
    have ha : raw837 = raw839 := by apply Matrix.ext; unfold raw837 raw839; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4190 = raw839Labels := by decide +kernel
    rw [ha, hj, canonical839 B hB]
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

theorem singleton4359 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4359 node4359Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node937 node937Labels + mixedMoment B node1683 node1683Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1155 singletonSmall4359
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4359) = raw1155Labels := by decide +kernel
  rw [hl, canonical1155 B hB] at h
  have hc0 : mixedMoment B raw1155 (Fin.cases (0 : Fin 2) singletonSmall4359) =
      mixedMoment B node937 node937Labels := by
    have ha : raw1155 = raw1156 := by apply Matrix.ext; unfold raw1155 raw1156; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4359 = raw1156Labels := by decide +kernel
    rw [ha, hj, canonical1156 B hB]
  have hc1 : mixedMoment B raw1155 (Fin.cases (1 : Fin 2) singletonSmall4359) =
      mixedMoment B node1683 node1683Labels := by
    have ha : raw1155 = raw1157 := by apply Matrix.ext; unfold raw1155 raw1157; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4359 = raw1157Labels := by decide +kernel
    rw [ha, hj, canonical1157 B hB]
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

theorem singleton4496 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4496 node4496Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1080 node1080Labels + mixedMoment B node1710 node1710Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1296 singletonSmall4496
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4496) = raw1296Labels := by decide +kernel
  rw [hl, canonical1296 B hB] at h
  have hc0 : mixedMoment B raw1296 (Fin.cases (0 : Fin 2) singletonSmall4496) =
      mixedMoment B node1080 node1080Labels := by
    have ha : raw1296 = raw1297 := by apply Matrix.ext; unfold raw1296 raw1297; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4496 = raw1297Labels := by decide +kernel
    rw [ha, hj, canonical1297 B hB]
  have hc1 : mixedMoment B raw1296 (Fin.cases (1 : Fin 2) singletonSmall4496) =
      mixedMoment B node1710 node1710Labels := by
    have ha : raw1296 = raw1298 := by apply Matrix.ext; unfold raw1296 raw1298; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4496 = raw1298Labels := by decide +kernel
    rw [ha, hj, canonical1298 B hB]
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

theorem singleton4845 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4845 node4845Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2065 node2065Labels + mixedMoment B node2218 node2218Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1776 singletonSmall4845
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4845) = raw1776Labels := by decide +kernel
  rw [hl, canonical1776 B hB] at h
  have hc0 : mixedMoment B raw1776 (Fin.cases (0 : Fin 2) singletonSmall4845) =
      mixedMoment B node2065 node2065Labels := by
    have ha : raw1776 = raw1777 := by apply Matrix.ext; unfold raw1776 raw1777; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4845 = raw1777Labels := by decide +kernel
    rw [ha, hj, canonical1777 B hB]
  have hc1 : mixedMoment B raw1776 (Fin.cases (1 : Fin 2) singletonSmall4845) =
      mixedMoment B node2218 node2218Labels := by
    have ha : raw1776 = raw1778 := by apply Matrix.ext; unfold raw1776 raw1778; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4845 = raw1778Labels := by decide +kernel
    rw [ha, hj, canonical1778 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero717 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node717 node717Labels = 0 := by
  exact mixedMoment_order_one B hB node717 node717Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node710 node710Labels = Sparse.eval nodeValue710 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 710) = mixedMoment B node710 node710Labels := rfl
  simpa [nodeValue710, Sparse.eval] using hc.symm

theorem sound715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node715 node715Labels = Sparse.eval nodeValue715 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 715) = mixedMoment B node715 node715Labels := rfl
  simpa [nodeValue715, Sparse.eval] using hc.symm

theorem sound717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node717 node717Labels = Sparse.eval nodeValue717 (mixedVector B) := by
  simpa only [nodeValue717, Sparse.eval_nil] using zero717 B _hB _hF

theorem sound724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node724 node724Labels = Sparse.eval nodeValue724 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 724) = mixedMoment B node724 node724Labels := rfl
  simpa [nodeValue724, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero852 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node852 node852Labels = 0 := by
  exact mixedMoment_order_one B hB node852 node852Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero889 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node889 node889Labels = 0 := by
  exact mixedMoment_order_one B hB node889 node889Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node852 node852Labels = Sparse.eval nodeValue852 (mixedVector B) := by
  simpa only [nodeValue852, Sparse.eval_nil] using zero852 B _hB _hF

theorem sound866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node866 node866Labels = Sparse.eval nodeValue866 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 866) = mixedMoment B node866 node866Labels := rfl
  simpa [nodeValue866, Sparse.eval] using hc.symm

theorem sound873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node873 node873Labels = Sparse.eval nodeValue873 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 873) = mixedMoment B node873 node873Labels := rfl
  simpa [nodeValue873, Sparse.eval] using hc.symm

theorem sound874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node874 node874Labels = Sparse.eval nodeValue874 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 874) = mixedMoment B node874 node874Labels := rfl
  simpa [nodeValue874, Sparse.eval] using hc.symm

theorem sound889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node889 node889Labels = Sparse.eval nodeValue889 (mixedVector B) := by
  simpa only [nodeValue889, Sparse.eval_nil] using zero889 B _hB _hF

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

theorem sound937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node937 node937Labels = Sparse.eval nodeValue937 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 937) = mixedMoment B node937 node937Labels := rfl
  simpa [nodeValue937, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1013 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1013 node1013Labels = 0 := by
  exact mixedMoment_order_one B hB node1013 node1013Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node984 node984Labels = Sparse.eval nodeValue984 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 984) = mixedMoment B node984 node984Labels := rfl
  simpa [nodeValue984, Sparse.eval] using hc.symm

theorem sound985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node985 node985Labels = Sparse.eval nodeValue985 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 985) = mixedMoment B node985 node985Labels := rfl
  simpa [nodeValue985, Sparse.eval] using hc.symm

theorem sound1012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1012 node1012Labels = Sparse.eval nodeValue1012 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1012) = mixedMoment B node1012 node1012Labels := rfl
  simpa [nodeValue1012, Sparse.eval] using hc.symm

theorem sound1013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1013 node1013Labels = Sparse.eval nodeValue1013 (mixedVector B) := by
  simpa only [nodeValue1013, Sparse.eval_nil] using zero1013 B _hB _hF

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

theorem sound1080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1080 node1080Labels = Sparse.eval nodeValue1080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1080) = mixedMoment B node1080 node1080Labels := rfl
  simpa [nodeValue1080, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1095 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1095 node1095Labels = 0 := by
  exact mixedMoment_order_one B hB node1095 node1095Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1094 node1094Labels = Sparse.eval nodeValue1094 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1094) = mixedMoment B node1094 node1094Labels := rfl
  simpa [nodeValue1094, Sparse.eval] using hc.symm

theorem sound1095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1095 node1095Labels = Sparse.eval nodeValue1095 (mixedVector B) := by
  simpa only [nodeValue1095, Sparse.eval_nil] using zero1095 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1513 node1513Labels = Sparse.eval nodeValue1513 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1513) = mixedMoment B node1513 node1513Labels := rfl
  simpa [nodeValue1513, Sparse.eval] using hc.symm

theorem sound1519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1519 node1519Labels = Sparse.eval nodeValue1519 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1519) = mixedMoment B node1519 node1519Labels := rfl
  simpa [nodeValue1519, Sparse.eval] using hc.symm

theorem sound1527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1527 node1527Labels = Sparse.eval nodeValue1527 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1527) = mixedMoment B node1527 node1527Labels := rfl
  simpa [nodeValue1527, Sparse.eval] using hc.symm

theorem sound1531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1531 node1531Labels = Sparse.eval nodeValue1531 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1531) = mixedMoment B node1531 node1531Labels := rfl
  simpa [nodeValue1531, Sparse.eval] using hc.symm

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

theorem sound1538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1538 node1538Labels = Sparse.eval nodeValue1538 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1538) = mixedMoment B node1538 node1538Labels := rfl
  simpa [nodeValue1538, Sparse.eval] using hc.symm

theorem sound1539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1539 node1539Labels = Sparse.eval nodeValue1539 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1539) = mixedMoment B node1539 node1539Labels := rfl
  simpa [nodeValue1539, Sparse.eval] using hc.symm

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

theorem sound1618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1618 node1618Labels = Sparse.eval nodeValue1618 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1618) = mixedMoment B node1618 node1618Labels := rfl
  simpa [nodeValue1618, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1727 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1727 node1727Labels = 0 := by
  exact mixedMoment_order_one B hB node1727 node1727Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1669 node1669Labels = Sparse.eval nodeValue1669 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1669) = mixedMoment B node1669 node1669Labels := rfl
  simpa [nodeValue1669, Sparse.eval] using hc.symm

theorem sound1675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1675 node1675Labels = Sparse.eval nodeValue1675 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1675) = mixedMoment B node1675 node1675Labels := rfl
  simpa [nodeValue1675, Sparse.eval] using hc.symm

theorem sound1683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1683 node1683Labels = Sparse.eval nodeValue1683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1683) = mixedMoment B node1683 node1683Labels := rfl
  simpa [nodeValue1683, Sparse.eval] using hc.symm

theorem sound1687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1687 node1687Labels = Sparse.eval nodeValue1687 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1687) = mixedMoment B node1687 node1687Labels := rfl
  simpa [nodeValue1687, Sparse.eval] using hc.symm

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

theorem sound1710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1710 node1710Labels = Sparse.eval nodeValue1710 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1710) = mixedMoment B node1710 node1710Labels := rfl
  simpa [nodeValue1710, Sparse.eval] using hc.symm

theorem sound1716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1716 node1716Labels = Sparse.eval nodeValue1716 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1716) = mixedMoment B node1716 node1716Labels := rfl
  simpa [nodeValue1716, Sparse.eval] using hc.symm

theorem sound1727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1727 node1727Labels = Sparse.eval nodeValue1727 (mixedVector B) := by
  simpa only [nodeValue1727, Sparse.eval_nil] using zero1727 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1730 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1730 node1730Labels = 0 := by
  exact mixedMoment_order_one B hB node1730 node1730Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1754 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1754 node1754Labels = 0 := by
  exact mixedMoment_order_one B hB node1754 node1754Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1728 node1728Labels = Sparse.eval nodeValue1728 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1728) = mixedMoment B node1728 node1728Labels := rfl
  simpa [nodeValue1728, Sparse.eval] using hc.symm

theorem sound1730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1730 node1730Labels = Sparse.eval nodeValue1730 (mixedVector B) := by
  simpa only [nodeValue1730, Sparse.eval_nil] using zero1730 B _hB _hF

theorem sound1747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1747 node1747Labels = Sparse.eval nodeValue1747 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1747) = mixedMoment B node1747 node1747Labels := rfl
  simpa [nodeValue1747, Sparse.eval] using hc.symm

theorem sound1754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1754 node1754Labels = Sparse.eval nodeValue1754 (mixedVector B) := by
  simpa only [nodeValue1754, Sparse.eval_nil] using zero1754 B _hB _hF

theorem sound1756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1756 node1756Labels = Sparse.eval nodeValue1756 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1756) = mixedMoment B node1756 node1756Labels := rfl
  simpa [nodeValue1756, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1918 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1918 node1918Labels = 0 := by
  exact mixedMoment_order_one B hB node1918 node1918Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1917 node1917Labels = Sparse.eval nodeValue1917 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1917) = mixedMoment B node1917 node1917Labels := rfl
  simpa [nodeValue1917, Sparse.eval] using hc.symm

theorem sound1918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1918 node1918Labels = Sparse.eval nodeValue1918 (mixedVector B) := by
  simpa only [nodeValue1918, Sparse.eval_nil] using zero1918 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1953 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1953 node1953Labels = 0 := by
  exact mixedMoment_order_one B hB node1953 node1953Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1953 node1953Labels = Sparse.eval nodeValue1953 (mixedVector B) := by
  simpa only [nodeValue1953, Sparse.eval_nil] using zero1953 B _hB _hF

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

theorem sound1989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1989 node1989Labels = Sparse.eval nodeValue1989 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1989) = mixedMoment B node1989 node1989Labels := rfl
  simpa [nodeValue1989, Sparse.eval] using hc.symm

theorem sound1990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1990 node1990Labels = Sparse.eval nodeValue1990 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1990) = mixedMoment B node1990 node1990Labels := rfl
  simpa [nodeValue1990, Sparse.eval] using hc.symm

theorem sound2006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2006 node2006Labels = Sparse.eval nodeValue2006 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2006) = mixedMoment B node2006 node2006Labels := rfl
  simpa [nodeValue2006, Sparse.eval] using hc.symm

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

theorem sound2065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2065 node2065Labels = Sparse.eval nodeValue2065 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2065) = mixedMoment B node2065 node2065Labels := rfl
  simpa [nodeValue2065, Sparse.eval] using hc.symm

theorem sound2081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2081 node2081Labels = Sparse.eval nodeValue2081 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2081) = mixedMoment B node2081 node2081Labels := rfl
  simpa [nodeValue2081, Sparse.eval] using hc.symm

theorem sound2082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2082 node2082Labels = Sparse.eval nodeValue2082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2082) = mixedMoment B node2082 node2082Labels := rfl
  simpa [nodeValue2082, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2205 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2205 node2205Labels = 0 := by
  exact mixedMoment_order_one B hB node2205 node2205Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2228 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2228 node2228Labels = 0 := by
  exact mixedMoment_order_one B hB node2228 node2228Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2229 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2229 node2229Labels = 0 := by
  exact mixedMoment_order_one B hB node2229 node2229Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2203 node2203Labels = Sparse.eval nodeValue2203 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2203) = mixedMoment B node2203 node2203Labels := rfl
  simpa [nodeValue2203, Sparse.eval] using hc.symm

theorem sound2205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2205 node2205Labels = Sparse.eval nodeValue2205 (mixedVector B) := by
  simpa only [nodeValue2205, Sparse.eval_nil] using zero2205 B _hB _hF

theorem sound2206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2206 node2206Labels = Sparse.eval nodeValue2206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2206) = mixedMoment B node2206 node2206Labels := rfl
  simpa [nodeValue2206, Sparse.eval] using hc.symm

theorem sound2207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2207 node2207Labels = Sparse.eval nodeValue2207 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2207) = mixedMoment B node2207 node2207Labels := rfl
  simpa [nodeValue2207, Sparse.eval] using hc.symm

theorem sound2218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2218 node2218Labels = Sparse.eval nodeValue2218 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2218) = mixedMoment B node2218 node2218Labels := rfl
  simpa [nodeValue2218, Sparse.eval] using hc.symm

theorem sound2228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2228 node2228Labels = Sparse.eval nodeValue2228 (mixedVector B) := by
  simpa only [nodeValue2228, Sparse.eval_nil] using zero2228 B _hB _hF

theorem sound2229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2229 node2229Labels = Sparse.eval nodeValue2229 (mixedVector B) := by
  simpa only [nodeValue2229, Sparse.eval_nil] using zero2229 B _hB _hF

theorem sound2230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2230 node2230Labels = Sparse.eval nodeValue2230 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2230) = mixedMoment B node2230 node2230Labels := rfl
  simpa [nodeValue2230, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2268 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2268 node2268Labels = 0 := by
  exact mixedMoment_order_one B hB node2268 node2268Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2293 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2293 node2293Labels = 0 := by
  exact mixedMoment_order_one B hB node2293 node2293Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2268 node2268Labels = Sparse.eval nodeValue2268 (mixedVector B) := by
  simpa only [nodeValue2268, Sparse.eval_nil] using zero2268 B _hB _hF

theorem sound2293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2293 node2293Labels = Sparse.eval nodeValue2293 (mixedVector B) := by
  simpa only [nodeValue2293, Sparse.eval_nil] using zero2293 B _hB _hF

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

theorem sound569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node569 node569Labels = Sparse.eval nodeValue569 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 569) = mixedMoment B node569 node569Labels := rfl
  simpa [nodeValue569, Sparse.eval] using hc.symm

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

theorem sound4071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4071 node4071Labels = Sparse.eval nodeValue4071 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4071) = mixedMoment B node4071 node4071Labels := rfl
  simpa [nodeValue4071, Sparse.eval] using hc.symm

theorem sound4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4080 node4080Labels = Sparse.eval nodeValue4080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4080) = mixedMoment B node4080 node4080Labels := rfl
  simpa [nodeValue4080, Sparse.eval] using hc.symm

theorem sound4081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4081 node4081Labels = Sparse.eval nodeValue4081 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4081) = mixedMoment B node4081 node4081Labels := rfl
  simpa [nodeValue4081, Sparse.eval] using hc.symm

theorem sound4082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4082 node4082Labels = Sparse.eval nodeValue4082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4082) = mixedMoment B node4082 node4082Labels := rfl
  simpa [nodeValue4082, Sparse.eval] using hc.symm

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

theorem sound4085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4085 node4085Labels = Sparse.eval nodeValue4085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4085) = mixedMoment B node4085 node4085Labels := rfl
  simpa [nodeValue4085, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node576 node576Labels = Sparse.eval nodeValue576 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 576) = mixedMoment B node576 node576Labels := rfl
  simpa [nodeValue576, Sparse.eval] using hc.symm

theorem sound595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node595 node595Labels = Sparse.eval nodeValue595 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 595) = mixedMoment B node595 node595Labels := rfl
  simpa [nodeValue595, Sparse.eval] using hc.symm

theorem sound607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node607 node607Labels = Sparse.eval nodeValue607 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 607) = mixedMoment B node607 node607Labels := rfl
  simpa [nodeValue607, Sparse.eval] using hc.symm

theorem sound608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node608 node608Labels = Sparse.eval nodeValue608 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 608) = mixedMoment B node608 node608Labels := rfl
  simpa [nodeValue608, Sparse.eval] using hc.symm

theorem sound618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node618 node618Labels = Sparse.eval nodeValue618 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 618) = mixedMoment B node618 node618Labels := rfl
  simpa [nodeValue618, Sparse.eval] using hc.symm

theorem sound619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node619 node619Labels = Sparse.eval nodeValue619 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 619) = mixedMoment B node619 node619Labels := rfl
  simpa [nodeValue619, Sparse.eval] using hc.symm

theorem sound620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node620 node620Labels = Sparse.eval nodeValue620 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 620) = mixedMoment B node620 node620Labels := rfl
  simpa [nodeValue620, Sparse.eval] using hc.symm

theorem sound621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node621 node621Labels = Sparse.eval nodeValue621 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 621) = mixedMoment B node621 node621Labels := rfl
  simpa [nodeValue621, Sparse.eval] using hc.symm

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

theorem sound4179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4179 node4179Labels = Sparse.eval nodeValue4179 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4179) = mixedMoment B node4179 node4179Labels := rfl
  simpa [nodeValue4179, Sparse.eval] using hc.symm

theorem sound4190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4190 node4190Labels = Sparse.eval nodeValue4190 (mixedVector B) := by
  have h := singleton4190 B _hB
  rw [sound618 B _hB _hF, sound1527 B _hB _hF] at h
  norm_num [nodeValue4190, nodeValue618, nodeValue1527, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4193 node4193Labels = Sparse.eval nodeValue4193 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4193) = mixedMoment B node4193 node4193Labels := rfl
  simpa [nodeValue4193, Sparse.eval] using hc.symm

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

theorem sound4359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4359 node4359Labels = Sparse.eval nodeValue4359 (mixedVector B) := by
  have h := singleton4359 B _hB
  rw [sound937 B _hB _hF, sound1683 B _hB _hF] at h
  norm_num [nodeValue4359, nodeValue937, nodeValue1683, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4362 node4362Labels = Sparse.eval nodeValue4362 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4362) = mixedMoment B node4362 node4362Labels := rfl
  simpa [nodeValue4362, Sparse.eval] using hc.symm

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

theorem zero4501 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4501 node4501Labels = 0 := by
  exact mixedMoment_order_one B hB node4501 node4501Labels 1
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

theorem sound4496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4496 node4496Labels = Sparse.eval nodeValue4496 (mixedVector B) := by
  have h := singleton4496 B _hB
  rw [sound1080 B _hB _hF, sound1710 B _hB _hF] at h
  norm_num [nodeValue4496, nodeValue1080, nodeValue1710, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4500 node4500Labels = Sparse.eval nodeValue4500 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4500) = mixedMoment B node4500 node4500Labels := rfl
  simpa [nodeValue4500, Sparse.eval] using hc.symm

theorem sound4501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4501 node4501Labels = Sparse.eval nodeValue4501 (mixedVector B) := by
  simpa only [nodeValue4501, Sparse.eval_nil] using zero4501 B _hB _hF

theorem sound4508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4508 node4508Labels = Sparse.eval nodeValue4508 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4508) = mixedMoment B node4508 node4508Labels := rfl
  simpa [nodeValue4508, Sparse.eval] using hc.symm

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

theorem sound4845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4845 node4845Labels = Sparse.eval nodeValue4845 (mixedVector B) := by
  have h := singleton4845 B _hB
  rw [sound2065 B _hB _hF, sound2218 B _hB _hF] at h
  norm_num [nodeValue4845, nodeValue2065, nodeValue2218, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem zero4897 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4897 node4897Labels = 0 := by
  exact mixedMoment_order_one B hB node4897 node4897Labels 1
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

theorem sound4897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4897 node4897Labels = Sparse.eval nodeValue4897 (mixedVector B) := by
  simpa only [nodeValue4897, Sparse.eval_nil] using zero4897 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources47
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1534 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1534 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1534 + difference 0 0) (sourceB1534 + difference 0 0) sourceC1534) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 984) := by
    have ha : (tripleCharges (sourceA1534 + difference 0 0) (sourceB1534 + difference 0 0) sourceC1534) = raw23308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1534 sourceB1534 sourceC1534 difference raw23308; decide +kernel
    rw [ha]
    exact (canonical23308 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1534 + difference 0 1) (sourceB1534 + difference 1 0) sourceC1534) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2081) := by
    have ha : (tripleCharges (sourceA1534 + difference 0 1) (sourceB1534 + difference 1 0) sourceC1534) = raw23309 := by
      apply Matrix.ext; unfold tripleCharges sourceA1534 sourceB1534 sourceC1534 difference raw23309; decide +kernel
    rw [ha]
    exact (canonical23309 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1534 + difference 0 2) (sourceB1534 + difference 2 0) sourceC1534) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1989) := by
    have ha : (tripleCharges (sourceA1534 + difference 0 2) (sourceB1534 + difference 2 0) sourceC1534) = raw23310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1534 sourceB1534 sourceC1534 difference raw23310; decide +kernel
    rw [ha]
    exact (canonical23310 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1534 + difference 0 3) (sourceB1534 + difference 3 0) sourceC1534) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1917) := by
    have ha : (tripleCharges (sourceA1534 + difference 0 3) (sourceB1534 + difference 3 0) sourceC1534) = raw23311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1534 sourceB1534 sourceC1534 difference raw23311; decide +kernel
    rw [ha]
    exact (canonical23311 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1534 + difference 0 4) (sourceB1534 + difference 4 0) sourceC1534) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA1534 + difference 0 4) (sourceB1534 + difference 4 0) sourceC1534) = raw23312 := by
      apply Matrix.ext; unfold tripleCharges sourceA1534 sourceB1534 sourceC1534 difference raw23312; decide +kernel
    rw [ha]
    exact (canonical23312 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1534 + difference 0 5) (sourceB1534 + difference 5 0) sourceC1534) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1534 + difference 0 5) (sourceB1534 + difference 5 0) sourceC1534) = raw23313 := by
      apply Matrix.ext; unfold tripleCharges sourceA1534 sourceB1534 sourceC1534 difference raw23313; decide +kernel
    rw [ha]
    exact (canonical23313 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1534 + sourceB1534) sourceC1534) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1534 + sourceB1534) sourceC1534) = raw23314 := by
      apply Matrix.ext; unfold doubleCharges sourceA1534 sourceB1534 sourceC1534 raw23314; decide +kernel
    rw [ha]
    exact (canonical23314 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1534 sourceB1534 sourceC1534
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1534, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1535 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1535 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1535 + difference 0 0) (sourceB1535 + difference 0 0) sourceC1535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 985) := by
    have ha : (tripleCharges (sourceA1535 + difference 0 0) (sourceB1535 + difference 0 0) sourceC1535) = raw21590 := by
      apply Matrix.ext; unfold tripleCharges sourceA1535 sourceB1535 sourceC1535 difference raw21590; decide +kernel
    rw [ha]
    exact (canonical21590 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1535 + difference 0 1) (sourceB1535 + difference 1 0) sourceC1535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2082) := by
    have ha : (tripleCharges (sourceA1535 + difference 0 1) (sourceB1535 + difference 1 0) sourceC1535) = raw23315 := by
      apply Matrix.ext; unfold tripleCharges sourceA1535 sourceB1535 sourceC1535 difference raw23315; decide +kernel
    rw [ha]
    exact (canonical23315 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1535 + difference 0 2) (sourceB1535 + difference 2 0) sourceC1535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1990) := by
    have ha : (tripleCharges (sourceA1535 + difference 0 2) (sourceB1535 + difference 2 0) sourceC1535) = raw23316 := by
      apply Matrix.ext; unfold tripleCharges sourceA1535 sourceB1535 sourceC1535 difference raw23316; decide +kernel
    rw [ha]
    exact (canonical23316 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1535 + difference 0 3) (sourceB1535 + difference 3 0) sourceC1535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1918) := by
    have ha : (tripleCharges (sourceA1535 + difference 0 3) (sourceB1535 + difference 3 0) sourceC1535) = raw23317 := by
      apply Matrix.ext; unfold tripleCharges sourceA1535 sourceB1535 sourceC1535 difference raw23317; decide +kernel
    rw [ha]
    exact (canonical23317 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1535 + difference 0 4) (sourceB1535 + difference 4 0) sourceC1535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA1535 + difference 0 4) (sourceB1535 + difference 4 0) sourceC1535) = raw21585 := by
      apply Matrix.ext; unfold tripleCharges sourceA1535 sourceB1535 sourceC1535 difference raw21585; decide +kernel
    rw [ha]
    exact (canonical21585 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1535 + difference 0 5) (sourceB1535 + difference 5 0) sourceC1535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA1535 + difference 0 5) (sourceB1535 + difference 5 0) sourceC1535) = raw23318 := by
      apply Matrix.ext; unfold tripleCharges sourceA1535 sourceB1535 sourceC1535 difference raw23318; decide +kernel
    rw [ha]
    exact (canonical23318 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1535 + sourceB1535) sourceC1535) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1535 + sourceB1535) sourceC1535) = raw21586 := by
      apply Matrix.ext; unfold doubleCharges sourceA1535 sourceB1535 sourceC1535 raw21586; decide +kernel
    rw [ha]
    exact (canonical21586 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1535 sourceB1535 sourceC1535
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1535, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources48
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1537 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1537 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1537 + difference 0 3) (sourceB1537 + difference 3 0) sourceC1537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1918) := by
    have ha : (tripleCharges (sourceA1537 + difference 0 3) (sourceB1537 + difference 3 0) sourceC1537) = raw23317 := by
      apply Matrix.ext; unfold tripleCharges sourceA1537 sourceB1537 sourceC1537 difference raw23317; decide +kernel
    rw [ha]
    exact (canonical23317 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1537 + difference 1 3) (sourceB1537 + difference 3 1) sourceC1537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 889) := by
    have ha : (tripleCharges (sourceA1537 + difference 1 3) (sourceB1537 + difference 3 1) sourceC1537) = raw23321 := by
      apply Matrix.ext; unfold tripleCharges sourceA1537 sourceB1537 sourceC1537 difference raw23321; decide +kernel
    rw [ha]
    exact (canonical23321 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1537 + difference 2 3) (sourceB1537 + difference 3 2) sourceC1537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 866) := by
    have ha : (tripleCharges (sourceA1537 + difference 2 3) (sourceB1537 + difference 3 2) sourceC1537) = raw23323 := by
      apply Matrix.ext; unfold tripleCharges sourceA1537 sourceB1537 sourceC1537 difference raw23323; decide +kernel
    rw [ha]
    exact (canonical23323 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1537 + difference 3 3) (sourceB1537 + difference 3 3) sourceC1537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 985) := by
    have ha : (tripleCharges (sourceA1537 + difference 3 3) (sourceB1537 + difference 3 3) sourceC1537) = raw21590 := by
      apply Matrix.ext; unfold tripleCharges sourceA1537 sourceB1537 sourceC1537 difference raw21590; decide +kernel
    rw [ha]
    exact (canonical21590 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1537 + difference 4 3) (sourceB1537 + difference 3 4) sourceC1537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 873) := by
    have ha : (tripleCharges (sourceA1537 + difference 4 3) (sourceB1537 + difference 3 4) sourceC1537) = raw23324 := by
      apply Matrix.ext; unfold tripleCharges sourceA1537 sourceB1537 sourceC1537 difference raw23324; decide +kernel
    rw [ha]
    exact (canonical23324 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1537 + difference 5 3) (sourceB1537 + difference 3 5) sourceC1537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 874) := by
    have ha : (tripleCharges (sourceA1537 + difference 5 3) (sourceB1537 + difference 3 5) sourceC1537) = raw23325 := by
      apply Matrix.ext; unfold tripleCharges sourceA1537 sourceB1537 sourceC1537 difference raw23325; decide +kernel
    rw [ha]
    exact (canonical23325 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1537 + sourceB1537) sourceC1537) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1537 + sourceB1537) sourceC1537) = raw21586 := by
      apply Matrix.ext; unfold doubleCharges sourceA1537 sourceB1537 sourceC1537 raw21586; decide +kernel
    rw [ha]
    exact (canonical21586 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1537 sourceB1537 sourceC1537
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1537, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1538 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1538 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1538 + difference 0 0) (sourceB1538 + difference 0 0) sourceC1538) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1618) := by
    have ha : (tripleCharges (sourceA1538 + difference 0 0) (sourceB1538 + difference 0 0) sourceC1538) = raw23326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1538 sourceB1538 sourceC1538 difference raw23326; decide +kernel
    rw [ha]
    exact (canonical23326 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1538 + difference 1 0) (sourceB1538 + difference 0 1) sourceC1538) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 724) := by
    have ha : (tripleCharges (sourceA1538 + difference 1 0) (sourceB1538 + difference 0 1) sourceC1538) = raw23327 := by
      apply Matrix.ext; unfold tripleCharges sourceA1538 sourceB1538 sourceC1538 difference raw23327; decide +kernel
    rw [ha]
    exact (canonical23327 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1538 + difference 2 0) (sourceB1538 + difference 0 2) sourceC1538) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 710) := by
    have ha : (tripleCharges (sourceA1538 + difference 2 0) (sourceB1538 + difference 0 2) sourceC1538) = raw23328 := by
      apply Matrix.ext; unfold tripleCharges sourceA1538 sourceB1538 sourceC1538 difference raw23328; decide +kernel
    rw [ha]
    exact (canonical23328 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1538 + difference 3 0) (sourceB1538 + difference 0 3) sourceC1538) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 852) := by
    have ha : (tripleCharges (sourceA1538 + difference 3 0) (sourceB1538 + difference 0 3) sourceC1538) = raw23329 := by
      apply Matrix.ext; unfold tripleCharges sourceA1538 sourceB1538 sourceC1538 difference raw23329; decide +kernel
    rw [ha]
    exact (canonical23329 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1538 + difference 4 0) (sourceB1538 + difference 0 4) sourceC1538) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 715) := by
    have ha : (tripleCharges (sourceA1538 + difference 4 0) (sourceB1538 + difference 0 4) sourceC1538) = raw23330 := by
      apply Matrix.ext; unfold tripleCharges sourceA1538 sourceB1538 sourceC1538 difference raw23330; decide +kernel
    rw [ha]
    exact (canonical23330 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1538 + difference 5 0) (sourceB1538 + difference 0 5) sourceC1538) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 717) := by
    have ha : (tripleCharges (sourceA1538 + difference 5 0) (sourceB1538 + difference 0 5) sourceC1538) = raw23331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1538 sourceB1538 sourceC1538 difference raw23331; decide +kernel
    rw [ha]
    exact (canonical23331 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1538 + sourceB1538) sourceC1538) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1538 + sourceB1538) sourceC1538) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1538 sourceB1538 sourceC1538 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1538 sourceB1538 sourceC1538
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1538, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1540 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1540 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1540 + difference 0 1) (sourceB1540 + difference 1 0) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA1540 + difference 0 1) (sourceB1540 + difference 1 0) sourceC1540) = raw23333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23333; decide +kernel
    rw [ha]
    exact (canonical23333 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1540 + difference 0 2) (sourceB1540 + difference 2 0) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA1540 + difference 0 2) (sourceB1540 + difference 2 0) sourceC1540) = raw23334 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23334; decide +kernel
    rw [ha]
    exact (canonical23334 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1540 + difference 0 3) (sourceB1540 + difference 3 0) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA1540 + difference 0 3) (sourceB1540 + difference 3 0) sourceC1540) = raw23335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23335; decide +kernel
    rw [ha]
    exact (canonical23335 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1540 + difference 0 4) (sourceB1540 + difference 4 0) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA1540 + difference 0 4) (sourceB1540 + difference 4 0) sourceC1540) = raw3475 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw3475; decide +kernel
    rw [ha]
    exact (canonical3475 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1540 + difference 0 5) (sourceB1540 + difference 5 0) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA1540 + difference 0 5) (sourceB1540 + difference 5 0) sourceC1540) = raw23336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23336; decide +kernel
    rw [ha]
    exact (canonical23336 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1540 + difference 1 0) (sourceB1540 + difference 0 1) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4179) := by
    have ha : (tripleCharges (sourceA1540 + difference 1 0) (sourceB1540 + difference 0 1) sourceC1540) = raw23337 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23337; decide +kernel
    rw [ha]
    exact (canonical23337 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1540 + difference 1 2) (sourceB1540 + difference 2 1) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4348) := by
    have ha : (tripleCharges (sourceA1540 + difference 1 2) (sourceB1540 + difference 2 1) sourceC1540) = raw23338 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23338; decide +kernel
    rw [ha]
    exact (canonical23338 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1540 + difference 1 3) (sourceB1540 + difference 3 1) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4348) := by
    have ha : (tripleCharges (sourceA1540 + difference 1 3) (sourceB1540 + difference 3 1) sourceC1540) = raw23339 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23339; decide +kernel
    rw [ha]
    exact (canonical23339 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1540 + difference 1 4) (sourceB1540 + difference 4 1) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4500) := by
    have ha : (tripleCharges (sourceA1540 + difference 1 4) (sourceB1540 + difference 4 1) sourceC1540) = raw23340 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23340; decide +kernel
    rw [ha]
    exact (canonical23340 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1540 + difference 1 5) (sourceB1540 + difference 5 1) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA1540 + difference 1 5) (sourceB1540 + difference 5 1) sourceC1540) = raw23341 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23341; decide +kernel
    rw [ha]
    exact (canonical23341 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1540 + difference 2 0) (sourceB1540 + difference 0 2) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4179) := by
    have ha : (tripleCharges (sourceA1540 + difference 2 0) (sourceB1540 + difference 0 2) sourceC1540) = raw23342 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23342; decide +kernel
    rw [ha]
    exact (canonical23342 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1540 + difference 2 1) (sourceB1540 + difference 1 2) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4348) := by
    have ha : (tripleCharges (sourceA1540 + difference 2 1) (sourceB1540 + difference 1 2) sourceC1540) = raw23343 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23343; decide +kernel
    rw [ha]
    exact (canonical23343 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1540 + difference 2 3) (sourceB1540 + difference 3 2) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4348) := by
    have ha : (tripleCharges (sourceA1540 + difference 2 3) (sourceB1540 + difference 3 2) sourceC1540) = raw23344 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23344; decide +kernel
    rw [ha]
    exact (canonical23344 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1540 + difference 2 4) (sourceB1540 + difference 4 2) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4500) := by
    have ha : (tripleCharges (sourceA1540 + difference 2 4) (sourceB1540 + difference 4 2) sourceC1540) = raw23345 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23345; decide +kernel
    rw [ha]
    exact (canonical23345 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1540 + difference 2 5) (sourceB1540 + difference 5 2) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA1540 + difference 2 5) (sourceB1540 + difference 5 2) sourceC1540) = raw23346 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23346; decide +kernel
    rw [ha]
    exact (canonical23346 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1540 + difference 3 0) (sourceB1540 + difference 0 3) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4179) := by
    have ha : (tripleCharges (sourceA1540 + difference 3 0) (sourceB1540 + difference 0 3) sourceC1540) = raw23347 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23347; decide +kernel
    rw [ha]
    exact (canonical23347 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1540 + difference 3 1) (sourceB1540 + difference 1 3) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4348) := by
    have ha : (tripleCharges (sourceA1540 + difference 3 1) (sourceB1540 + difference 1 3) sourceC1540) = raw23348 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23348; decide +kernel
    rw [ha]
    exact (canonical23348 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1540 + difference 3 2) (sourceB1540 + difference 2 3) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4348) := by
    have ha : (tripleCharges (sourceA1540 + difference 3 2) (sourceB1540 + difference 2 3) sourceC1540) = raw23349 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23349; decide +kernel
    rw [ha]
    exact (canonical23349 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1540 + difference 3 4) (sourceB1540 + difference 4 3) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4500) := by
    have ha : (tripleCharges (sourceA1540 + difference 3 4) (sourceB1540 + difference 4 3) sourceC1540) = raw23350 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23350; decide +kernel
    rw [ha]
    exact (canonical23350 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1540 + difference 3 5) (sourceB1540 + difference 5 3) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA1540 + difference 3 5) (sourceB1540 + difference 5 3) sourceC1540) = raw23351 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23351; decide +kernel
    rw [ha]
    exact (canonical23351 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1540 + difference 4 0) (sourceB1540 + difference 0 4) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4190) := by
    have ha : (tripleCharges (sourceA1540 + difference 4 0) (sourceB1540 + difference 0 4) sourceC1540) = raw23352 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23352; decide +kernel
    rw [ha]
    exact (canonical23352 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1540 + difference 4 1) (sourceB1540 + difference 1 4) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4359) := by
    have ha : (tripleCharges (sourceA1540 + difference 4 1) (sourceB1540 + difference 1 4) sourceC1540) = raw23353 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23353; decide +kernel
    rw [ha]
    exact (canonical23353 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1540 + difference 4 2) (sourceB1540 + difference 2 4) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4359) := by
    have ha : (tripleCharges (sourceA1540 + difference 4 2) (sourceB1540 + difference 2 4) sourceC1540) = raw23354 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23354; decide +kernel
    rw [ha]
    exact (canonical23354 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1540 + difference 4 3) (sourceB1540 + difference 3 4) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4359) := by
    have ha : (tripleCharges (sourceA1540 + difference 4 3) (sourceB1540 + difference 3 4) sourceC1540) = raw23355 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23355; decide +kernel
    rw [ha]
    exact (canonical23355 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1540 + difference 4 5) (sourceB1540 + difference 5 4) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1540 + difference 4 5) (sourceB1540 + difference 5 4) sourceC1540) = raw23356 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23356; decide +kernel
    rw [ha]
    exact (canonical23356 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1540 + difference 5 0) (sourceB1540 + difference 0 5) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4193) := by
    have ha : (tripleCharges (sourceA1540 + difference 5 0) (sourceB1540 + difference 0 5) sourceC1540) = raw23357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23357; decide +kernel
    rw [ha]
    exact (canonical23357 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1540 + difference 5 1) (sourceB1540 + difference 1 5) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4362) := by
    have ha : (tripleCharges (sourceA1540 + difference 5 1) (sourceB1540 + difference 1 5) sourceC1540) = raw23358 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23358; decide +kernel
    rw [ha]
    exact (canonical23358 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1540 + difference 5 2) (sourceB1540 + difference 2 5) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4362) := by
    have ha : (tripleCharges (sourceA1540 + difference 5 2) (sourceB1540 + difference 2 5) sourceC1540) = raw23359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23359; decide +kernel
    rw [ha]
    exact (canonical23359 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1540 + difference 5 3) (sourceB1540 + difference 3 5) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4362) := by
    have ha : (tripleCharges (sourceA1540 + difference 5 3) (sourceB1540 + difference 3 5) sourceC1540) = raw23360 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23360; decide +kernel
    rw [ha]
    exact (canonical23360 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1540 + difference 5 4) (sourceB1540 + difference 4 5) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4508) := by
    have ha : (tripleCharges (sourceA1540 + difference 5 4) (sourceB1540 + difference 4 5) sourceC1540) = raw3471 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw3471; decide +kernel
    rw [ha]
    exact (canonical3471 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1540 sourceB1540 sourceC1540
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1540, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1542 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1542 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1542 + difference 0 1) (sourceB1542 + difference 1 0) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA1542 + difference 0 1) (sourceB1542 + difference 1 0) sourceC1542) = raw23389 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23389; decide +kernel
    rw [ha]
    exact (canonical23389 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1542 + difference 0 2) (sourceB1542 + difference 2 0) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA1542 + difference 0 2) (sourceB1542 + difference 2 0) sourceC1542) = raw23390 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23390; decide +kernel
    rw [ha]
    exact (canonical23390 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1542 + difference 0 3) (sourceB1542 + difference 3 0) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA1542 + difference 0 3) (sourceB1542 + difference 3 0) sourceC1542) = raw23391 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23391; decide +kernel
    rw [ha]
    exact (canonical23391 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1542 + difference 0 4) (sourceB1542 + difference 4 0) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA1542 + difference 0 4) (sourceB1542 + difference 4 0) sourceC1542) = raw23392 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23392; decide +kernel
    rw [ha]
    exact (canonical23392 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1542 + difference 0 5) (sourceB1542 + difference 5 0) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA1542 + difference 0 5) (sourceB1542 + difference 5 0) sourceC1542) = raw23393 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23393; decide +kernel
    rw [ha]
    exact (canonical23393 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1542 + difference 1 0) (sourceB1542 + difference 0 1) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1513) := by
    have ha : (tripleCharges (sourceA1542 + difference 1 0) (sourceB1542 + difference 0 1) sourceC1542) = raw23394 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23394; decide +kernel
    rw [ha]
    exact (canonical23394 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1542 + difference 1 2) (sourceB1542 + difference 2 1) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA1542 + difference 1 2) (sourceB1542 + difference 2 1) sourceC1542) = raw23395 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23395; decide +kernel
    rw [ha]
    exact (canonical23395 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1542 + difference 1 3) (sourceB1542 + difference 3 1) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA1542 + difference 1 3) (sourceB1542 + difference 3 1) sourceC1542) = raw23396 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23396; decide +kernel
    rw [ha]
    exact (canonical23396 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1542 + difference 1 4) (sourceB1542 + difference 4 1) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA1542 + difference 1 4) (sourceB1542 + difference 4 1) sourceC1542) = raw23397 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23397; decide +kernel
    rw [ha]
    exact (canonical23397 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1542 + difference 1 5) (sourceB1542 + difference 5 1) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1542 + difference 1 5) (sourceB1542 + difference 5 1) sourceC1542) = raw23398 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23398; decide +kernel
    rw [ha]
    exact (canonical23398 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1542 + difference 2 0) (sourceB1542 + difference 0 2) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1513) := by
    have ha : (tripleCharges (sourceA1542 + difference 2 0) (sourceB1542 + difference 0 2) sourceC1542) = raw23399 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23399; decide +kernel
    rw [ha]
    exact (canonical23399 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1542 + difference 2 1) (sourceB1542 + difference 1 2) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA1542 + difference 2 1) (sourceB1542 + difference 1 2) sourceC1542) = raw23400 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23400; decide +kernel
    rw [ha]
    exact (canonical23400 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1542 + difference 2 3) (sourceB1542 + difference 3 2) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA1542 + difference 2 3) (sourceB1542 + difference 3 2) sourceC1542) = raw23401 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23401; decide +kernel
    rw [ha]
    exact (canonical23401 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1542 + difference 2 4) (sourceB1542 + difference 4 2) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA1542 + difference 2 4) (sourceB1542 + difference 4 2) sourceC1542) = raw23402 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23402; decide +kernel
    rw [ha]
    exact (canonical23402 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1542 + difference 2 5) (sourceB1542 + difference 5 2) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1542 + difference 2 5) (sourceB1542 + difference 5 2) sourceC1542) = raw23403 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23403; decide +kernel
    rw [ha]
    exact (canonical23403 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1542 + difference 3 0) (sourceB1542 + difference 0 3) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1513) := by
    have ha : (tripleCharges (sourceA1542 + difference 3 0) (sourceB1542 + difference 0 3) sourceC1542) = raw23404 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23404; decide +kernel
    rw [ha]
    exact (canonical23404 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1542 + difference 3 1) (sourceB1542 + difference 1 3) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA1542 + difference 3 1) (sourceB1542 + difference 1 3) sourceC1542) = raw23405 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23405; decide +kernel
    rw [ha]
    exact (canonical23405 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1542 + difference 3 2) (sourceB1542 + difference 2 3) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA1542 + difference 3 2) (sourceB1542 + difference 2 3) sourceC1542) = raw23406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23406; decide +kernel
    rw [ha]
    exact (canonical23406 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1542 + difference 3 4) (sourceB1542 + difference 4 3) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA1542 + difference 3 4) (sourceB1542 + difference 4 3) sourceC1542) = raw23407 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23407; decide +kernel
    rw [ha]
    exact (canonical23407 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1542 + difference 3 5) (sourceB1542 + difference 5 3) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1542 + difference 3 5) (sourceB1542 + difference 5 3) sourceC1542) = raw23408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23408; decide +kernel
    rw [ha]
    exact (canonical23408 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1542 + difference 4 0) (sourceB1542 + difference 0 4) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1527) := by
    have ha : (tripleCharges (sourceA1542 + difference 4 0) (sourceB1542 + difference 0 4) sourceC1542) = raw23409 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23409; decide +kernel
    rw [ha]
    exact (canonical23409 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1542 + difference 4 1) (sourceB1542 + difference 1 4) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1683) := by
    have ha : (tripleCharges (sourceA1542 + difference 4 1) (sourceB1542 + difference 1 4) sourceC1542) = raw23410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23410; decide +kernel
    rw [ha]
    exact (canonical23410 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1542 + difference 4 2) (sourceB1542 + difference 2 4) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1683) := by
    have ha : (tripleCharges (sourceA1542 + difference 4 2) (sourceB1542 + difference 2 4) sourceC1542) = raw23411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23411; decide +kernel
    rw [ha]
    exact (canonical23411 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1542 + difference 4 3) (sourceB1542 + difference 3 4) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1683) := by
    have ha : (tripleCharges (sourceA1542 + difference 4 3) (sourceB1542 + difference 3 4) sourceC1542) = raw23412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23412; decide +kernel
    rw [ha]
    exact (canonical23412 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1542 + difference 4 5) (sourceB1542 + difference 5 4) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1542 + difference 4 5) (sourceB1542 + difference 5 4) sourceC1542) = raw23413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23413; decide +kernel
    rw [ha]
    exact (canonical23413 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1542 + difference 5 0) (sourceB1542 + difference 0 5) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1531) := by
    have ha : (tripleCharges (sourceA1542 + difference 5 0) (sourceB1542 + difference 0 5) sourceC1542) = raw23414 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23414; decide +kernel
    rw [ha]
    exact (canonical23414 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1542 + difference 5 1) (sourceB1542 + difference 1 5) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1687) := by
    have ha : (tripleCharges (sourceA1542 + difference 5 1) (sourceB1542 + difference 1 5) sourceC1542) = raw23415 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23415; decide +kernel
    rw [ha]
    exact (canonical23415 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1542 + difference 5 2) (sourceB1542 + difference 2 5) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1687) := by
    have ha : (tripleCharges (sourceA1542 + difference 5 2) (sourceB1542 + difference 2 5) sourceC1542) = raw23416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23416; decide +kernel
    rw [ha]
    exact (canonical23416 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1542 + difference 5 3) (sourceB1542 + difference 3 5) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1687) := by
    have ha : (tripleCharges (sourceA1542 + difference 5 3) (sourceB1542 + difference 3 5) sourceC1542) = raw23417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23417; decide +kernel
    rw [ha]
    exact (canonical23417 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1542 + difference 5 4) (sourceB1542 + difference 4 5) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1747) := by
    have ha : (tripleCharges (sourceA1542 + difference 5 4) (sourceB1542 + difference 4 5) sourceC1542) = raw23418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23418; decide +kernel
    rw [ha]
    exact (canonical23418 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1542 sourceB1542 sourceC1542
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1542, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1543 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1543 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1543 + difference 0 0) (sourceB1543 + difference 0 0) sourceC1543) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1094) := by
    have ha : (tripleCharges (sourceA1543 + difference 0 0) (sourceB1543 + difference 0 0) sourceC1543) = raw20092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1543 sourceB1543 sourceC1543 difference raw20092; decide +kernel
    rw [ha]
    exact (canonical20092 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1543 + difference 1 0) (sourceB1543 + difference 0 1) sourceC1543) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 607) := by
    have ha : (tripleCharges (sourceA1543 + difference 1 0) (sourceB1543 + difference 0 1) sourceC1543) = raw23419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1543 sourceB1543 sourceC1543 difference raw23419; decide +kernel
    rw [ha]
    exact (canonical23419 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1543 + difference 2 0) (sourceB1543 + difference 0 2) sourceC1543) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 607) := by
    have ha : (tripleCharges (sourceA1543 + difference 2 0) (sourceB1543 + difference 0 2) sourceC1543) = raw23420 := by
      apply Matrix.ext; unfold tripleCharges sourceA1543 sourceB1543 sourceC1543 difference raw23420; decide +kernel
    rw [ha]
    exact (canonical23420 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1543 + difference 3 0) (sourceB1543 + difference 0 3) sourceC1543) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 607) := by
    have ha : (tripleCharges (sourceA1543 + difference 3 0) (sourceB1543 + difference 0 3) sourceC1543) = raw23421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1543 sourceB1543 sourceC1543 difference raw23421; decide +kernel
    rw [ha]
    exact (canonical23421 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1543 + difference 4 0) (sourceB1543 + difference 0 4) sourceC1543) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 618) := by
    have ha : (tripleCharges (sourceA1543 + difference 4 0) (sourceB1543 + difference 0 4) sourceC1543) = raw23422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1543 sourceB1543 sourceC1543 difference raw23422; decide +kernel
    rw [ha]
    exact (canonical23422 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1543 + difference 5 0) (sourceB1543 + difference 0 5) sourceC1543) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 621) := by
    have ha : (tripleCharges (sourceA1543 + difference 5 0) (sourceB1543 + difference 0 5) sourceC1543) = raw20088 := by
      apply Matrix.ext; unfold tripleCharges sourceA1543 sourceB1543 sourceC1543 difference raw20088; decide +kernel
    rw [ha]
    exact (canonical20088 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1543 + sourceB1543) sourceC1543) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA1543 + sourceB1543) sourceC1543) = raw3517 := by
      apply Matrix.ext; unfold doubleCharges sourceA1543 sourceB1543 sourceC1543 raw3517; decide +kernel
    rw [ha]
    exact (canonical3517 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1543 sourceB1543 sourceC1543
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1543, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1551 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1551 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1551 + difference 0 1) (sourceB1551 + difference 1 0) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA1551 + difference 0 1) (sourceB1551 + difference 1 0) sourceC1551) = raw23535 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23535; decide +kernel
    rw [ha]
    exact (canonical23535 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1551 + difference 0 2) (sourceB1551 + difference 2 0) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA1551 + difference 0 2) (sourceB1551 + difference 2 0) sourceC1551) = raw23536 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23536; decide +kernel
    rw [ha]
    exact (canonical23536 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1551 + difference 0 3) (sourceB1551 + difference 3 0) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA1551 + difference 0 3) (sourceB1551 + difference 3 0) sourceC1551) = raw23537 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23537; decide +kernel
    rw [ha]
    exact (canonical23537 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1551 + difference 0 4) (sourceB1551 + difference 4 0) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA1551 + difference 0 4) (sourceB1551 + difference 4 0) sourceC1551) = raw21660 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw21660; decide +kernel
    rw [ha]
    exact (canonical21660 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1551 + difference 0 5) (sourceB1551 + difference 5 0) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA1551 + difference 0 5) (sourceB1551 + difference 5 0) sourceC1551) = raw23538 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23538; decide +kernel
    rw [ha]
    exact (canonical23538 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1551 + difference 1 0) (sourceB1551 + difference 0 1) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1519) := by
    have ha : (tripleCharges (sourceA1551 + difference 1 0) (sourceB1551 + difference 0 1) sourceC1551) = raw23539 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23539; decide +kernel
    rw [ha]
    exact (canonical23539 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1551 + difference 1 2) (sourceB1551 + difference 2 1) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1675) := by
    have ha : (tripleCharges (sourceA1551 + difference 1 2) (sourceB1551 + difference 2 1) sourceC1551) = raw23540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23540; decide +kernel
    rw [ha]
    exact (canonical23540 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1551 + difference 1 3) (sourceB1551 + difference 3 1) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1675) := by
    have ha : (tripleCharges (sourceA1551 + difference 1 3) (sourceB1551 + difference 3 1) sourceC1551) = raw23541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23541; decide +kernel
    rw [ha]
    exact (canonical23541 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1551 + difference 1 4) (sourceB1551 + difference 4 1) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1551 + difference 1 4) (sourceB1551 + difference 4 1) sourceC1551) = raw21665 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw21665; decide +kernel
    rw [ha]
    exact (canonical21665 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1551 + difference 1 5) (sourceB1551 + difference 5 1) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1551 + difference 1 5) (sourceB1551 + difference 5 1) sourceC1551) = raw23542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23542; decide +kernel
    rw [ha]
    exact (canonical23542 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1551 + difference 2 0) (sourceB1551 + difference 0 2) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1519) := by
    have ha : (tripleCharges (sourceA1551 + difference 2 0) (sourceB1551 + difference 0 2) sourceC1551) = raw23543 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23543; decide +kernel
    rw [ha]
    exact (canonical23543 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1551 + difference 2 1) (sourceB1551 + difference 1 2) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1675) := by
    have ha : (tripleCharges (sourceA1551 + difference 2 1) (sourceB1551 + difference 1 2) sourceC1551) = raw23544 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23544; decide +kernel
    rw [ha]
    exact (canonical23544 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1551 + difference 2 3) (sourceB1551 + difference 3 2) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1675) := by
    have ha : (tripleCharges (sourceA1551 + difference 2 3) (sourceB1551 + difference 3 2) sourceC1551) = raw23545 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23545; decide +kernel
    rw [ha]
    exact (canonical23545 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1551 + difference 2 4) (sourceB1551 + difference 4 2) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1551 + difference 2 4) (sourceB1551 + difference 4 2) sourceC1551) = raw21670 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw21670; decide +kernel
    rw [ha]
    exact (canonical21670 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1551 + difference 2 5) (sourceB1551 + difference 5 2) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1551 + difference 2 5) (sourceB1551 + difference 5 2) sourceC1551) = raw23546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23546; decide +kernel
    rw [ha]
    exact (canonical23546 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1551 + difference 3 0) (sourceB1551 + difference 0 3) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1519) := by
    have ha : (tripleCharges (sourceA1551 + difference 3 0) (sourceB1551 + difference 0 3) sourceC1551) = raw23547 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23547; decide +kernel
    rw [ha]
    exact (canonical23547 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1551 + difference 3 1) (sourceB1551 + difference 1 3) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1675) := by
    have ha : (tripleCharges (sourceA1551 + difference 3 1) (sourceB1551 + difference 1 3) sourceC1551) = raw23548 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23548; decide +kernel
    rw [ha]
    exact (canonical23548 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1551 + difference 3 2) (sourceB1551 + difference 2 3) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1675) := by
    have ha : (tripleCharges (sourceA1551 + difference 3 2) (sourceB1551 + difference 2 3) sourceC1551) = raw23549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23549; decide +kernel
    rw [ha]
    exact (canonical23549 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1551 + difference 3 4) (sourceB1551 + difference 4 3) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1551 + difference 3 4) (sourceB1551 + difference 4 3) sourceC1551) = raw21675 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw21675; decide +kernel
    rw [ha]
    exact (canonical21675 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1551 + difference 3 5) (sourceB1551 + difference 5 3) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1551 + difference 3 5) (sourceB1551 + difference 5 3) sourceC1551) = raw23550 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23550; decide +kernel
    rw [ha]
    exact (canonical23550 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1551 + difference 4 0) (sourceB1551 + difference 0 4) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1538) := by
    have ha : (tripleCharges (sourceA1551 + difference 4 0) (sourceB1551 + difference 0 4) sourceC1551) = raw23551 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23551; decide +kernel
    rw [ha]
    exact (canonical23551 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1551 + difference 4 1) (sourceB1551 + difference 1 4) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA1551 + difference 4 1) (sourceB1551 + difference 1 4) sourceC1551) = raw23552 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23552; decide +kernel
    rw [ha]
    exact (canonical23552 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1551 + difference 4 2) (sourceB1551 + difference 2 4) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA1551 + difference 4 2) (sourceB1551 + difference 2 4) sourceC1551) = raw23553 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23553; decide +kernel
    rw [ha]
    exact (canonical23553 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1551 + difference 4 3) (sourceB1551 + difference 3 4) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA1551 + difference 4 3) (sourceB1551 + difference 3 4) sourceC1551) = raw23554 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23554; decide +kernel
    rw [ha]
    exact (canonical23554 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1551 + difference 4 5) (sourceB1551 + difference 5 4) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1754) := by
    have ha : (tripleCharges (sourceA1551 + difference 4 5) (sourceB1551 + difference 5 4) sourceC1551) = raw23555 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23555; decide +kernel
    rw [ha]
    exact (canonical23555 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1551 + difference 5 0) (sourceB1551 + difference 0 5) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1539) := by
    have ha : (tripleCharges (sourceA1551 + difference 5 0) (sourceB1551 + difference 0 5) sourceC1551) = raw21676 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw21676; decide +kernel
    rw [ha]
    exact (canonical21676 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1551 + difference 5 1) (sourceB1551 + difference 1 5) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1694) := by
    have ha : (tripleCharges (sourceA1551 + difference 5 1) (sourceB1551 + difference 1 5) sourceC1551) = raw21677 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw21677; decide +kernel
    rw [ha]
    exact (canonical21677 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1551 + difference 5 2) (sourceB1551 + difference 2 5) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1694) := by
    have ha : (tripleCharges (sourceA1551 + difference 5 2) (sourceB1551 + difference 2 5) sourceC1551) = raw21678 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw21678; decide +kernel
    rw [ha]
    exact (canonical21678 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1551 + difference 5 3) (sourceB1551 + difference 3 5) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1694) := by
    have ha : (tripleCharges (sourceA1551 + difference 5 3) (sourceB1551 + difference 3 5) sourceC1551) = raw21679 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw21679; decide +kernel
    rw [ha]
    exact (canonical21679 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1551 + difference 5 4) (sourceB1551 + difference 4 5) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1756) := by
    have ha : (tripleCharges (sourceA1551 + difference 5 4) (sourceB1551 + difference 4 5) sourceC1551) = raw23556 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23556; decide +kernel
    rw [ha]
    exact (canonical23556 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1551 sourceB1551 sourceC1551
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1551, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1552 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1552 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1552 + difference 0 0) (sourceB1552 + difference 0 0) sourceC1552) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1095) := by
    have ha : (tripleCharges (sourceA1552 + difference 0 0) (sourceB1552 + difference 0 0) sourceC1552) = raw23557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1552 sourceB1552 sourceC1552 difference raw23557; decide +kernel
    rw [ha]
    exact (canonical23557 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1552 + difference 1 0) (sourceB1552 + difference 0 1) sourceC1552) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 608) := by
    have ha : (tripleCharges (sourceA1552 + difference 1 0) (sourceB1552 + difference 0 1) sourceC1552) = raw23558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1552 sourceB1552 sourceC1552 difference raw23558; decide +kernel
    rw [ha]
    exact (canonical23558 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1552 + difference 2 0) (sourceB1552 + difference 0 2) sourceC1552) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 608) := by
    have ha : (tripleCharges (sourceA1552 + difference 2 0) (sourceB1552 + difference 0 2) sourceC1552) = raw23559 := by
      apply Matrix.ext; unfold tripleCharges sourceA1552 sourceB1552 sourceC1552 difference raw23559; decide +kernel
    rw [ha]
    exact (canonical23559 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1552 + difference 3 0) (sourceB1552 + difference 0 3) sourceC1552) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 608) := by
    have ha : (tripleCharges (sourceA1552 + difference 3 0) (sourceB1552 + difference 0 3) sourceC1552) = raw23560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1552 sourceB1552 sourceC1552 difference raw23560; decide +kernel
    rw [ha]
    exact (canonical23560 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1552 + difference 4 0) (sourceB1552 + difference 0 4) sourceC1552) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 619) := by
    have ha : (tripleCharges (sourceA1552 + difference 4 0) (sourceB1552 + difference 0 4) sourceC1552) = raw23561 := by
      apply Matrix.ext; unfold tripleCharges sourceA1552 sourceB1552 sourceC1552 difference raw23561; decide +kernel
    rw [ha]
    exact (canonical23561 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1552 + difference 5 0) (sourceB1552 + difference 0 5) sourceC1552) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 620) := by
    have ha : (tripleCharges (sourceA1552 + difference 5 0) (sourceB1552 + difference 0 5) sourceC1552) = raw23562 := by
      apply Matrix.ext; unfold tripleCharges sourceA1552 sourceB1552 sourceC1552 difference raw23562; decide +kernel
    rw [ha]
    exact (canonical23562 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1552 + sourceB1552) sourceC1552) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1552 + sourceB1552) sourceC1552) = raw19413 := by
      apply Matrix.ext; unfold doubleCharges sourceA1552 sourceB1552 sourceC1552 raw19413; decide +kernel
    rw [ha]
    exact (canonical19413 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1552 sourceB1552 sourceC1552
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1552, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1554 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1554 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1554 + difference 0 0) (sourceB1554 + difference 0 0) sourceC1554) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1012) := by
    have ha : (tripleCharges (sourceA1554 + difference 0 0) (sourceB1554 + difference 0 0) sourceC1554) = raw21894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1554 sourceB1554 sourceC1554 difference raw21894; decide +kernel
    rw [ha]
    exact (canonical21894 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1554 + difference 0 1) (sourceB1554 + difference 1 0) sourceC1554) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2006) := by
    have ha : (tripleCharges (sourceA1554 + difference 0 1) (sourceB1554 + difference 1 0) sourceC1554) = raw23571 := by
      apply Matrix.ext; unfold tripleCharges sourceA1554 sourceB1554 sourceC1554 difference raw23571; decide +kernel
    rw [ha]
    exact (canonical23571 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1554 + difference 0 2) (sourceB1554 + difference 2 0) sourceC1554) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2006) := by
    have ha : (tripleCharges (sourceA1554 + difference 0 2) (sourceB1554 + difference 2 0) sourceC1554) = raw23572 := by
      apply Matrix.ext; unfold tripleCharges sourceA1554 sourceB1554 sourceC1554 difference raw23572; decide +kernel
    rw [ha]
    exact (canonical23572 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1554 + difference 0 3) (sourceB1554 + difference 3 0) sourceC1554) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1953) := by
    have ha : (tripleCharges (sourceA1554 + difference 0 3) (sourceB1554 + difference 3 0) sourceC1554) = raw23573 := by
      apply Matrix.ext; unfold tripleCharges sourceA1554 sourceB1554 sourceC1554 difference raw23573; decide +kernel
    rw [ha]
    exact (canonical23573 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1554 + difference 0 4) (sourceB1554 + difference 4 0) sourceC1554) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA1554 + difference 0 4) (sourceB1554 + difference 4 0) sourceC1554) = raw21889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1554 sourceB1554 sourceC1554 difference raw21889; decide +kernel
    rw [ha]
    exact (canonical21889 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1554 + difference 0 5) (sourceB1554 + difference 5 0) sourceC1554) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA1554 + difference 0 5) (sourceB1554 + difference 5 0) sourceC1554) = raw23574 := by
      apply Matrix.ext; unfold tripleCharges sourceA1554 sourceB1554 sourceC1554 difference raw23574; decide +kernel
    rw [ha]
    exact (canonical23574 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1554 + sourceB1554) sourceC1554) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1554 + sourceB1554) sourceC1554) = raw21890 := by
      apply Matrix.ext; unfold doubleCharges sourceA1554 sourceB1554 sourceC1554 raw21890; decide +kernel
    rw [ha]
    exact (canonical21890 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1554 sourceB1554 sourceC1554
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1554, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1558 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1558 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1558 + difference 0 0) (sourceB1558 + difference 0 0) sourceC1558) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1013) := by
    have ha : (tripleCharges (sourceA1558 + difference 0 0) (sourceB1558 + difference 0 0) sourceC1558) = raw21909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1558 sourceB1558 sourceC1558 difference raw21909; decide +kernel
    rw [ha]
    exact (canonical21909 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1558 + difference 1 0) (sourceB1558 + difference 0 1) sourceC1558) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 569) := by
    have ha : (tripleCharges (sourceA1558 + difference 1 0) (sourceB1558 + difference 0 1) sourceC1558) = raw23639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1558 sourceB1558 sourceC1558 difference raw23639; decide +kernel
    rw [ha]
    exact (canonical23639 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1558 + difference 2 0) (sourceB1558 + difference 0 2) sourceC1558) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 569) := by
    have ha : (tripleCharges (sourceA1558 + difference 2 0) (sourceB1558 + difference 0 2) sourceC1558) = raw23640 := by
      apply Matrix.ext; unfold tripleCharges sourceA1558 sourceB1558 sourceC1558 difference raw23640; decide +kernel
    rw [ha]
    exact (canonical23640 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1558 + difference 3 0) (sourceB1558 + difference 0 3) sourceC1558) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 595) := by
    have ha : (tripleCharges (sourceA1558 + difference 3 0) (sourceB1558 + difference 0 3) sourceC1558) = raw23641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1558 sourceB1558 sourceC1558 difference raw23641; decide +kernel
    rw [ha]
    exact (canonical23641 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1558 + difference 4 0) (sourceB1558 + difference 0 4) sourceC1558) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 576) := by
    have ha : (tripleCharges (sourceA1558 + difference 4 0) (sourceB1558 + difference 0 4) sourceC1558) = raw23642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1558 sourceB1558 sourceC1558 difference raw23642; decide +kernel
    rw [ha]
    exact (canonical23642 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1558 + difference 5 0) (sourceB1558 + difference 0 5) sourceC1558) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 576) := by
    have ha : (tripleCharges (sourceA1558 + difference 5 0) (sourceB1558 + difference 0 5) sourceC1558) = raw21906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1558 sourceB1558 sourceC1558 difference raw21906; decide +kernel
    rw [ha]
    exact (canonical21906 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1558 + sourceB1558) sourceC1558) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1558 + sourceB1558) sourceC1558) = raw21901 := by
      apply Matrix.ext; unfold doubleCharges sourceA1558 sourceB1558 sourceC1558 raw21901; decide +kernel
    rw [ha]
    exact (canonical21901 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1558 sourceB1558 sourceC1558
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1558, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1313 : Integer.Sparse.reindex keyMap MixedData.row1313 = numericRow1313 := by decide +kernel

theorem numericCheck1313 (x : Master → ℝ) : Integer.Sparse.eval numericRow1313 x =
    (1 : ℝ) * reducedSource1313 x := by
  norm_num [numericRow1313, reducedSource1313, Integer.Sparse.eval, Sparse.eval, nodeValue984, nodeValue1917, nodeValue1989, nodeValue2081, nodeValue2203, nodeValue2207, nodeValue4081]

theorem reindexCheck1314 : Integer.Sparse.reindex keyMap MixedData.row1314 = numericRow1314 := by decide +kernel

theorem numericCheck1314 (x : Master → ℝ) : Integer.Sparse.eval numericRow1314 x =
    (1 : ℝ) * reducedSource1314 x := by
  norm_num [numericRow1314, reducedSource1314, Integer.Sparse.eval, Sparse.eval, nodeValue985, nodeValue1918, nodeValue1990, nodeValue2082, nodeValue2205, nodeValue2206, nodeValue4080]

theorem reindexCheck1315 : Integer.Sparse.reindex keyMap MixedData.row1315 = numericRow1315 := by decide +kernel

theorem numericCheck1315 (x : Master → ℝ) : Integer.Sparse.eval numericRow1315 x =
    (1 : ℝ) * reducedSource1315 x := by
  norm_num [numericRow1315, reducedSource1315, Integer.Sparse.eval, Sparse.eval, nodeValue866, nodeValue873, nodeValue874, nodeValue889, nodeValue985, nodeValue1918, nodeValue4080]

theorem reindexCheck1316 : Integer.Sparse.reindex keyMap MixedData.row1316 = numericRow1316 := by decide +kernel

theorem numericCheck1316 (x : Master → ℝ) : Integer.Sparse.eval numericRow1316 x =
    (1 : ℝ) * reducedSource1316 x := by
  norm_num [numericRow1316, reducedSource1316, Integer.Sparse.eval, Sparse.eval, nodeValue710, nodeValue715, nodeValue717, nodeValue724, nodeValue852, nodeValue1618, nodeValue4071]

theorem reindexCheck1317 : Integer.Sparse.reindex keyMap MixedData.row1317 = numericRow1317 := by decide +kernel

theorem numericCheck1317 (x : Master → ℝ) : Integer.Sparse.eval numericRow1317 x =
    (4 : ℝ) * reducedSource1317 x := by
  norm_num [numericRow1317, reducedSource1317, Integer.Sparse.eval, Sparse.eval, nodeValue4179, nodeValue4190, nodeValue4193, nodeValue4348, nodeValue4359, nodeValue4362, nodeValue4496, nodeValue4500, nodeValue4501, nodeValue4508, nodeValue4845, nodeValue4897, nodeValue4899]
  ring

theorem reindexCheck1319 : Integer.Sparse.reindex keyMap MixedData.row1319 = numericRow1319 := by decide +kernel

theorem numericCheck1319 (x : Master → ℝ) : Integer.Sparse.eval numericRow1319 x =
    (1 : ℝ) * reducedSource1319 x := by
  norm_num [numericRow1319, reducedSource1319, Integer.Sparse.eval, Sparse.eval, nodeValue1513, nodeValue1527, nodeValue1531, nodeValue1669, nodeValue1683, nodeValue1687, nodeValue1710, nodeValue1716, nodeValue1730, nodeValue1747, nodeValue2218, nodeValue2268, nodeValue2281]

theorem reindexCheck1320 : Integer.Sparse.reindex keyMap MixedData.row1320 = numericRow1320 := by decide +kernel

theorem numericCheck1320 (x : Master → ℝ) : Integer.Sparse.eval numericRow1320 x =
    (1 : ℝ) * reducedSource1320 x := by
  norm_num [numericRow1320, reducedSource1320, Integer.Sparse.eval, Sparse.eval, nodeValue607, nodeValue618, nodeValue621, nodeValue1094, nodeValue4085]

theorem reindexCheck1322 : Integer.Sparse.reindex keyMap MixedData.row1322 = numericRow1322 := by decide +kernel

theorem numericCheck1322 (x : Master → ℝ) : Integer.Sparse.eval numericRow1322 x =
    (1 : ℝ) * reducedSource1322 x := by
  norm_num [numericRow1322, reducedSource1322, Integer.Sparse.eval, Sparse.eval, nodeValue1519, nodeValue1538, nodeValue1539, nodeValue1675, nodeValue1693, nodeValue1694, nodeValue1727, nodeValue1728, nodeValue1754, nodeValue1756, nodeValue2229, nodeValue2293, nodeValue4084]

theorem reindexCheck1323 : Integer.Sparse.reindex keyMap MixedData.row1323 = numericRow1323 := by decide +kernel

theorem numericCheck1323 (x : Master → ℝ) : Integer.Sparse.eval numericRow1323 x =
    (1 : ℝ) * reducedSource1323 x := by
  norm_num [numericRow1323, reducedSource1323, Integer.Sparse.eval, Sparse.eval, nodeValue608, nodeValue619, nodeValue620, nodeValue1095, nodeValue4084]

theorem reindexCheck1325 : Integer.Sparse.reindex keyMap MixedData.row1325 = numericRow1325 := by decide +kernel

theorem numericCheck1325 (x : Master → ℝ) : Integer.Sparse.eval numericRow1325 x =
    (1 : ℝ) * reducedSource1325 x := by
  norm_num [numericRow1325, reducedSource1325, Integer.Sparse.eval, Sparse.eval, nodeValue1012, nodeValue1953, nodeValue2006, nodeValue2228, nodeValue2230, nodeValue4081]

theorem reindexCheck1327 : Integer.Sparse.reindex keyMap MixedData.row1327 = numericRow1327 := by decide +kernel

theorem numericCheck1327 (x : Master → ℝ) : Integer.Sparse.eval numericRow1327 x =
    (1 : ℝ) * reducedSource1327 x := by
  norm_num [numericRow1327, reducedSource1327, Integer.Sparse.eval, Sparse.eval, nodeValue569, nodeValue576, nodeValue595, nodeValue1013, nodeValue4082]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1313 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1313 (mixedVector B) = 0 := by
  have h984 : mixedVector B (Sum.inr 984) = Sparse.eval nodeValue984 (mixedVector B) := by
    change mixedMoment B node984 node984Labels = _
    exact sound984 B hB hF
  have h1917 : mixedVector B (Sum.inr 1917) = Sparse.eval nodeValue1917 (mixedVector B) := by
    change mixedMoment B node1917 node1917Labels = _
    exact sound1917 B hB hF
  have h1989 : mixedVector B (Sum.inr 1989) = Sparse.eval nodeValue1989 (mixedVector B) := by
    change mixedMoment B node1989 node1989Labels = _
    exact sound1989 B hB hF
  have h2081 : mixedVector B (Sum.inr 2081) = Sparse.eval nodeValue2081 (mixedVector B) := by
    change mixedMoment B node2081 node2081Labels = _
    exact sound2081 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h2207 : mixedVector B (Sum.inr 2207) = Sparse.eval nodeValue2207 (mixedVector B) := by
    change mixedMoment B node2207 node2207Labels = _
    exact sound2207 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1534, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h984, h1917, h1989, h2081, h2203, h2207, h4081, reducedSource1313] using sourceEq1534 B hB

theorem rowSound1313 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1313 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1313, numericCheck1313, reducedZero1313 B hB hF, mul_zero]

theorem reducedZero1314 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1314 (mixedVector B) = 0 := by
  have h985 : mixedVector B (Sum.inr 985) = Sparse.eval nodeValue985 (mixedVector B) := by
    change mixedMoment B node985 node985Labels = _
    exact sound985 B hB hF
  have h1918 : mixedVector B (Sum.inr 1918) = Sparse.eval nodeValue1918 (mixedVector B) := by
    change mixedMoment B node1918 node1918Labels = _
    exact sound1918 B hB hF
  have h1990 : mixedVector B (Sum.inr 1990) = Sparse.eval nodeValue1990 (mixedVector B) := by
    change mixedMoment B node1990 node1990Labels = _
    exact sound1990 B hB hF
  have h2082 : mixedVector B (Sum.inr 2082) = Sparse.eval nodeValue2082 (mixedVector B) := by
    change mixedMoment B node2082 node2082Labels = _
    exact sound2082 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h2206 : mixedVector B (Sum.inr 2206) = Sparse.eval nodeValue2206 (mixedVector B) := by
    change mixedMoment B node2206 node2206Labels = _
    exact sound2206 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1535, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h985, h1918, h1990, h2082, h2205, h2206, h4080, reducedSource1314] using sourceEq1535 B hB

theorem rowSound1314 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1314 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1314, numericCheck1314, reducedZero1314 B hB hF, mul_zero]

theorem reducedZero1315 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1315 (mixedVector B) = 0 := by
  have h866 : mixedVector B (Sum.inr 866) = Sparse.eval nodeValue866 (mixedVector B) := by
    change mixedMoment B node866 node866Labels = _
    exact sound866 B hB hF
  have h873 : mixedVector B (Sum.inr 873) = Sparse.eval nodeValue873 (mixedVector B) := by
    change mixedMoment B node873 node873Labels = _
    exact sound873 B hB hF
  have h874 : mixedVector B (Sum.inr 874) = Sparse.eval nodeValue874 (mixedVector B) := by
    change mixedMoment B node874 node874Labels = _
    exact sound874 B hB hF
  have h889 : mixedVector B (Sum.inr 889) = Sparse.eval nodeValue889 (mixedVector B) := by
    change mixedMoment B node889 node889Labels = _
    exact sound889 B hB hF
  have h985 : mixedVector B (Sum.inr 985) = Sparse.eval nodeValue985 (mixedVector B) := by
    change mixedMoment B node985 node985Labels = _
    exact sound985 B hB hF
  have h1918 : mixedVector B (Sum.inr 1918) = Sparse.eval nodeValue1918 (mixedVector B) := by
    change mixedMoment B node1918 node1918Labels = _
    exact sound1918 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1537, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h866, h873, h874, h889, h985, h1918, h4080, reducedSource1315] using sourceEq1537 B hB

theorem rowSound1315 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1315 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1315, numericCheck1315, reducedZero1315 B hB hF, mul_zero]

theorem reducedZero1316 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1316 (mixedVector B) = 0 := by
  have h710 : mixedVector B (Sum.inr 710) = Sparse.eval nodeValue710 (mixedVector B) := by
    change mixedMoment B node710 node710Labels = _
    exact sound710 B hB hF
  have h715 : mixedVector B (Sum.inr 715) = Sparse.eval nodeValue715 (mixedVector B) := by
    change mixedMoment B node715 node715Labels = _
    exact sound715 B hB hF
  have h717 : mixedVector B (Sum.inr 717) = Sparse.eval nodeValue717 (mixedVector B) := by
    change mixedMoment B node717 node717Labels = _
    exact sound717 B hB hF
  have h724 : mixedVector B (Sum.inr 724) = Sparse.eval nodeValue724 (mixedVector B) := by
    change mixedMoment B node724 node724Labels = _
    exact sound724 B hB hF
  have h852 : mixedVector B (Sum.inr 852) = Sparse.eval nodeValue852 (mixedVector B) := by
    change mixedMoment B node852 node852Labels = _
    exact sound852 B hB hF
  have h1618 : mixedVector B (Sum.inr 1618) = Sparse.eval nodeValue1618 (mixedVector B) := by
    change mixedMoment B node1618 node1618Labels = _
    exact sound1618 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1538, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h710, h715, h717, h724, h852, h1618, h4071, reducedSource1316] using sourceEq1538 B hB

theorem rowSound1316 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1316 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1316, numericCheck1316, reducedZero1316 B hB hF, mul_zero]

theorem reducedZero1317 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1317 (mixedVector B) = 0 := by
  have h4179 : mixedVector B (Sum.inr 4179) = Sparse.eval nodeValue4179 (mixedVector B) := by
    change mixedMoment B node4179 node4179Labels = _
    exact sound4179 B hB hF
  have h4190 : mixedVector B (Sum.inr 4190) = Sparse.eval nodeValue4190 (mixedVector B) := by
    change mixedMoment B node4190 node4190Labels = _
    exact sound4190 B hB hF
  have h4193 : mixedVector B (Sum.inr 4193) = Sparse.eval nodeValue4193 (mixedVector B) := by
    change mixedMoment B node4193 node4193Labels = _
    exact sound4193 B hB hF
  have h4348 : mixedVector B (Sum.inr 4348) = Sparse.eval nodeValue4348 (mixedVector B) := by
    change mixedMoment B node4348 node4348Labels = _
    exact sound4348 B hB hF
  have h4359 : mixedVector B (Sum.inr 4359) = Sparse.eval nodeValue4359 (mixedVector B) := by
    change mixedMoment B node4359 node4359Labels = _
    exact sound4359 B hB hF
  have h4362 : mixedVector B (Sum.inr 4362) = Sparse.eval nodeValue4362 (mixedVector B) := by
    change mixedMoment B node4362 node4362Labels = _
    exact sound4362 B hB hF
  have h4496 : mixedVector B (Sum.inr 4496) = Sparse.eval nodeValue4496 (mixedVector B) := by
    change mixedMoment B node4496 node4496Labels = _
    exact sound4496 B hB hF
  have h4500 : mixedVector B (Sum.inr 4500) = Sparse.eval nodeValue4500 (mixedVector B) := by
    change mixedMoment B node4500 node4500Labels = _
    exact sound4500 B hB hF
  have h4501 : mixedVector B (Sum.inr 4501) = Sparse.eval nodeValue4501 (mixedVector B) := by
    change mixedMoment B node4501 node4501Labels = _
    exact sound4501 B hB hF
  have h4508 : mixedVector B (Sum.inr 4508) = Sparse.eval nodeValue4508 (mixedVector B) := by
    change mixedMoment B node4508 node4508Labels = _
    exact sound4508 B hB hF
  have h4845 : mixedVector B (Sum.inr 4845) = Sparse.eval nodeValue4845 (mixedVector B) := by
    change mixedMoment B node4845 node4845Labels = _
    exact sound4845 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  have h4899 : mixedVector B (Sum.inr 4899) = Sparse.eval nodeValue4899 (mixedVector B) := by
    change mixedMoment B node4899 node4899Labels = _
    exact sound4899 B hB hF
  simpa only [sourceForm1540, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4179, h4190, h4193, h4348, h4359, h4362, h4496, h4500, h4501, h4508, h4845, h4897, h4899, reducedSource1317] using sourceEq1540 B hB

theorem rowSound1317 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1317 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1317, numericCheck1317, reducedZero1317 B hB hF, mul_zero]

theorem reducedZero1319 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1319 (mixedVector B) = 0 := by
  have h1513 : mixedVector B (Sum.inr 1513) = Sparse.eval nodeValue1513 (mixedVector B) := by
    change mixedMoment B node1513 node1513Labels = _
    exact sound1513 B hB hF
  have h1527 : mixedVector B (Sum.inr 1527) = Sparse.eval nodeValue1527 (mixedVector B) := by
    change mixedMoment B node1527 node1527Labels = _
    exact sound1527 B hB hF
  have h1531 : mixedVector B (Sum.inr 1531) = Sparse.eval nodeValue1531 (mixedVector B) := by
    change mixedMoment B node1531 node1531Labels = _
    exact sound1531 B hB hF
  have h1669 : mixedVector B (Sum.inr 1669) = Sparse.eval nodeValue1669 (mixedVector B) := by
    change mixedMoment B node1669 node1669Labels = _
    exact sound1669 B hB hF
  have h1683 : mixedVector B (Sum.inr 1683) = Sparse.eval nodeValue1683 (mixedVector B) := by
    change mixedMoment B node1683 node1683Labels = _
    exact sound1683 B hB hF
  have h1687 : mixedVector B (Sum.inr 1687) = Sparse.eval nodeValue1687 (mixedVector B) := by
    change mixedMoment B node1687 node1687Labels = _
    exact sound1687 B hB hF
  have h1710 : mixedVector B (Sum.inr 1710) = Sparse.eval nodeValue1710 (mixedVector B) := by
    change mixedMoment B node1710 node1710Labels = _
    exact sound1710 B hB hF
  have h1716 : mixedVector B (Sum.inr 1716) = Sparse.eval nodeValue1716 (mixedVector B) := by
    change mixedMoment B node1716 node1716Labels = _
    exact sound1716 B hB hF
  have h1730 : mixedVector B (Sum.inr 1730) = Sparse.eval nodeValue1730 (mixedVector B) := by
    change mixedMoment B node1730 node1730Labels = _
    exact sound1730 B hB hF
  have h1747 : mixedVector B (Sum.inr 1747) = Sparse.eval nodeValue1747 (mixedVector B) := by
    change mixedMoment B node1747 node1747Labels = _
    exact sound1747 B hB hF
  have h2218 : mixedVector B (Sum.inr 2218) = Sparse.eval nodeValue2218 (mixedVector B) := by
    change mixedMoment B node2218 node2218Labels = _
    exact sound2218 B hB hF
  have h2268 : mixedVector B (Sum.inr 2268) = Sparse.eval nodeValue2268 (mixedVector B) := by
    change mixedMoment B node2268 node2268Labels = _
    exact sound2268 B hB hF
  have h2281 : mixedVector B (Sum.inr 2281) = Sparse.eval nodeValue2281 (mixedVector B) := by
    change mixedMoment B node2281 node2281Labels = _
    exact sound2281 B hB hF
  simpa only [sourceForm1542, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1513, h1527, h1531, h1669, h1683, h1687, h1710, h1716, h1730, h1747, h2218, h2268, h2281, reducedSource1319] using sourceEq1542 B hB

theorem rowSound1319 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1319 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1319, numericCheck1319, reducedZero1319 B hB hF, mul_zero]

theorem reducedZero1320 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1320 (mixedVector B) = 0 := by
  have h607 : mixedVector B (Sum.inr 607) = Sparse.eval nodeValue607 (mixedVector B) := by
    change mixedMoment B node607 node607Labels = _
    exact sound607 B hB hF
  have h618 : mixedVector B (Sum.inr 618) = Sparse.eval nodeValue618 (mixedVector B) := by
    change mixedMoment B node618 node618Labels = _
    exact sound618 B hB hF
  have h621 : mixedVector B (Sum.inr 621) = Sparse.eval nodeValue621 (mixedVector B) := by
    change mixedMoment B node621 node621Labels = _
    exact sound621 B hB hF
  have h1094 : mixedVector B (Sum.inr 1094) = Sparse.eval nodeValue1094 (mixedVector B) := by
    change mixedMoment B node1094 node1094Labels = _
    exact sound1094 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm1543, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h607, h618, h621, h1094, h4085, reducedSource1320] using sourceEq1543 B hB

theorem rowSound1320 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1320 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1320, numericCheck1320, reducedZero1320 B hB hF, mul_zero]

theorem reducedZero1322 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1322 (mixedVector B) = 0 := by
  have h1519 : mixedVector B (Sum.inr 1519) = Sparse.eval nodeValue1519 (mixedVector B) := by
    change mixedMoment B node1519 node1519Labels = _
    exact sound1519 B hB hF
  have h1538 : mixedVector B (Sum.inr 1538) = Sparse.eval nodeValue1538 (mixedVector B) := by
    change mixedMoment B node1538 node1538Labels = _
    exact sound1538 B hB hF
  have h1539 : mixedVector B (Sum.inr 1539) = Sparse.eval nodeValue1539 (mixedVector B) := by
    change mixedMoment B node1539 node1539Labels = _
    exact sound1539 B hB hF
  have h1675 : mixedVector B (Sum.inr 1675) = Sparse.eval nodeValue1675 (mixedVector B) := by
    change mixedMoment B node1675 node1675Labels = _
    exact sound1675 B hB hF
  have h1693 : mixedVector B (Sum.inr 1693) = Sparse.eval nodeValue1693 (mixedVector B) := by
    change mixedMoment B node1693 node1693Labels = _
    exact sound1693 B hB hF
  have h1694 : mixedVector B (Sum.inr 1694) = Sparse.eval nodeValue1694 (mixedVector B) := by
    change mixedMoment B node1694 node1694Labels = _
    exact sound1694 B hB hF
  have h1727 : mixedVector B (Sum.inr 1727) = Sparse.eval nodeValue1727 (mixedVector B) := by
    change mixedMoment B node1727 node1727Labels = _
    exact sound1727 B hB hF
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h1754 : mixedVector B (Sum.inr 1754) = Sparse.eval nodeValue1754 (mixedVector B) := by
    change mixedMoment B node1754 node1754Labels = _
    exact sound1754 B hB hF
  have h1756 : mixedVector B (Sum.inr 1756) = Sparse.eval nodeValue1756 (mixedVector B) := by
    change mixedMoment B node1756 node1756Labels = _
    exact sound1756 B hB hF
  have h2229 : mixedVector B (Sum.inr 2229) = Sparse.eval nodeValue2229 (mixedVector B) := by
    change mixedMoment B node2229 node2229Labels = _
    exact sound2229 B hB hF
  have h2293 : mixedVector B (Sum.inr 2293) = Sparse.eval nodeValue2293 (mixedVector B) := by
    change mixedMoment B node2293 node2293Labels = _
    exact sound2293 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1551, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1519, h1538, h1539, h1675, h1693, h1694, h1727, h1728, h1754, h1756, h2229, h2293, h4084, reducedSource1322] using sourceEq1551 B hB

theorem rowSound1322 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1322 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1322, numericCheck1322, reducedZero1322 B hB hF, mul_zero]

theorem reducedZero1323 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1323 (mixedVector B) = 0 := by
  have h608 : mixedVector B (Sum.inr 608) = Sparse.eval nodeValue608 (mixedVector B) := by
    change mixedMoment B node608 node608Labels = _
    exact sound608 B hB hF
  have h619 : mixedVector B (Sum.inr 619) = Sparse.eval nodeValue619 (mixedVector B) := by
    change mixedMoment B node619 node619Labels = _
    exact sound619 B hB hF
  have h620 : mixedVector B (Sum.inr 620) = Sparse.eval nodeValue620 (mixedVector B) := by
    change mixedMoment B node620 node620Labels = _
    exact sound620 B hB hF
  have h1095 : mixedVector B (Sum.inr 1095) = Sparse.eval nodeValue1095 (mixedVector B) := by
    change mixedMoment B node1095 node1095Labels = _
    exact sound1095 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1552, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h608, h619, h620, h1095, h4084, reducedSource1323] using sourceEq1552 B hB

theorem rowSound1323 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1323 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1323, numericCheck1323, reducedZero1323 B hB hF, mul_zero]

theorem reducedZero1325 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1325 (mixedVector B) = 0 := by
  have h1012 : mixedVector B (Sum.inr 1012) = Sparse.eval nodeValue1012 (mixedVector B) := by
    change mixedMoment B node1012 node1012Labels = _
    exact sound1012 B hB hF
  have h1953 : mixedVector B (Sum.inr 1953) = Sparse.eval nodeValue1953 (mixedVector B) := by
    change mixedMoment B node1953 node1953Labels = _
    exact sound1953 B hB hF
  have h2006 : mixedVector B (Sum.inr 2006) = Sparse.eval nodeValue2006 (mixedVector B) := by
    change mixedMoment B node2006 node2006Labels = _
    exact sound2006 B hB hF
  have h2228 : mixedVector B (Sum.inr 2228) = Sparse.eval nodeValue2228 (mixedVector B) := by
    change mixedMoment B node2228 node2228Labels = _
    exact sound2228 B hB hF
  have h2230 : mixedVector B (Sum.inr 2230) = Sparse.eval nodeValue2230 (mixedVector B) := by
    change mixedMoment B node2230 node2230Labels = _
    exact sound2230 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1554, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1012, h1953, h2006, h2228, h2230, h4081, reducedSource1325] using sourceEq1554 B hB

theorem rowSound1325 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1325 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1325, numericCheck1325, reducedZero1325 B hB hF, mul_zero]

theorem reducedZero1327 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1327 (mixedVector B) = 0 := by
  have h569 : mixedVector B (Sum.inr 569) = Sparse.eval nodeValue569 (mixedVector B) := by
    change mixedMoment B node569 node569Labels = _
    exact sound569 B hB hF
  have h576 : mixedVector B (Sum.inr 576) = Sparse.eval nodeValue576 (mixedVector B) := by
    change mixedMoment B node576 node576Labels = _
    exact sound576 B hB hF
  have h595 : mixedVector B (Sum.inr 595) = Sparse.eval nodeValue595 (mixedVector B) := by
    change mixedMoment B node595 node595Labels = _
    exact sound595 B hB hF
  have h1013 : mixedVector B (Sum.inr 1013) = Sparse.eval nodeValue1013 (mixedVector B) := by
    change mixedMoment B node1013 node1013Labels = _
    exact sound1013 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1558, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h569, h576, h595, h1013, h4082, reducedSource1327] using sourceEq1558 B hB

theorem rowSound1327 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1327 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1327, numericCheck1327, reducedZero1327 B hB hF, mul_zero]

theorem sourceRowsAt1312 : MixedData.sourceRows (1312 : Fin 2425) =
    MixedData.row1312 := by decide +kernel

theorem sourceRowsAt1313 : MixedData.sourceRows (1313 : Fin 2425) =
    MixedData.row1313 := by decide +kernel

theorem sourceRowsAt1314 : MixedData.sourceRows (1314 : Fin 2425) =
    MixedData.row1314 := by decide +kernel

theorem sourceRowsAt1315 : MixedData.sourceRows (1315 : Fin 2425) =
    MixedData.row1315 := by decide +kernel

theorem sourceRowsAt1316 : MixedData.sourceRows (1316 : Fin 2425) =
    MixedData.row1316 := by decide +kernel

theorem sourceRowsAt1317 : MixedData.sourceRows (1317 : Fin 2425) =
    MixedData.row1317 := by decide +kernel

theorem sourceRowsAt1318 : MixedData.sourceRows (1318 : Fin 2425) =
    MixedData.row1318 := by decide +kernel

theorem sourceRowsAt1319 : MixedData.sourceRows (1319 : Fin 2425) =
    MixedData.row1319 := by decide +kernel

theorem sourceRowsAt1320 : MixedData.sourceRows (1320 : Fin 2425) =
    MixedData.row1320 := by decide +kernel

theorem sourceRowsAt1321 : MixedData.sourceRows (1321 : Fin 2425) =
    MixedData.row1321 := by decide +kernel

theorem sourceRowsAt1322 : MixedData.sourceRows (1322 : Fin 2425) =
    MixedData.row1322 := by decide +kernel

theorem sourceRowsAt1323 : MixedData.sourceRows (1323 : Fin 2425) =
    MixedData.row1323 := by decide +kernel

theorem sourceRowsAt1324 : MixedData.sourceRows (1324 : Fin 2425) =
    MixedData.row1324 := by decide +kernel

theorem sourceRowsAt1325 : MixedData.sourceRows (1325 : Fin 2425) =
    MixedData.row1325 := by decide +kernel

theorem sourceRowsAt1326 : MixedData.sourceRows (1326 : Fin 2425) =
    MixedData.row1326 := by decide +kernel

theorem sourceRowsAt1327 : MixedData.sourceRows (1327 : Fin 2425) =
    MixedData.row1327 := by decide +kernel

theorem chunkSound82_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 82) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1312 ∨ k.val = 1313 ∨ k.val = 1314 ∨ k.val = 1315 ∨ k.val = 1316 ∨ k.val = 1317 ∨ k.val = 1318 ∨ k.val = 1319 ∨ k.val = 1320 ∨ k.val = 1321 ∨ k.val = 1322 ∨ k.val = 1323 ∨ k.val = 1324 ∨ k.val = 1325 ∨ k.val = 1326 ∨ k.val = 1327 := by omega
  rcases heq with h1312 | h1313 | h1314 | h1315 | h1316 | h1317 | h1318 | h1319 | h1320 | h1321 | h1322 | h1323 | h1324 | h1325 | h1326 | h1327
  · have he : k = (1312 : Fin 2425) := Fin.ext h1312
    subst k
    rw [sourceRowsAt1312]
    exact rowSound1312_e B hB hF
  · have he : k = (1313 : Fin 2425) := Fin.ext h1313
    subst k
    rw [sourceRowsAt1313]
    exact rowSound1313 B hB hF
  · have he : k = (1314 : Fin 2425) := Fin.ext h1314
    subst k
    rw [sourceRowsAt1314]
    exact rowSound1314 B hB hF
  · have he : k = (1315 : Fin 2425) := Fin.ext h1315
    subst k
    rw [sourceRowsAt1315]
    exact rowSound1315 B hB hF
  · have he : k = (1316 : Fin 2425) := Fin.ext h1316
    subst k
    rw [sourceRowsAt1316]
    exact rowSound1316 B hB hF
  · have he : k = (1317 : Fin 2425) := Fin.ext h1317
    subst k
    rw [sourceRowsAt1317]
    exact rowSound1317 B hB hF
  · have he : k = (1318 : Fin 2425) := Fin.ext h1318
    subst k
    rw [sourceRowsAt1318]
    exact rowSound1318_e B hB hF
  · have he : k = (1319 : Fin 2425) := Fin.ext h1319
    subst k
    rw [sourceRowsAt1319]
    exact rowSound1319 B hB hF
  · have he : k = (1320 : Fin 2425) := Fin.ext h1320
    subst k
    rw [sourceRowsAt1320]
    exact rowSound1320 B hB hF
  · have he : k = (1321 : Fin 2425) := Fin.ext h1321
    subst k
    rw [sourceRowsAt1321]
    exact rowSound1321_e B hB hF
  · have he : k = (1322 : Fin 2425) := Fin.ext h1322
    subst k
    rw [sourceRowsAt1322]
    exact rowSound1322 B hB hF
  · have he : k = (1323 : Fin 2425) := Fin.ext h1323
    subst k
    rw [sourceRowsAt1323]
    exact rowSound1323 B hB hF
  · have he : k = (1324 : Fin 2425) := Fin.ext h1324
    subst k
    rw [sourceRowsAt1324]
    exact rowSound1324_e B hB hF
  · have he : k = (1325 : Fin 2425) := Fin.ext h1325
    subst k
    rw [sourceRowsAt1325]
    exact rowSound1325 B hB hF
  · have he : k = (1326 : Fin 2425) := Fin.ext h1326
    subst k
    rw [sourceRowsAt1326]
    exact rowSound1326_e B hB hF
  · have he : k = (1327 : Fin 2425) := Fin.ext h1327
    subst k
    rw [sourceRowsAt1327]
    exact rowSound1327 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82_e_oai
