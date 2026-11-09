-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound88_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:39:40.305795+00:00
-- url     : https://prove2.me/submissions/7ad4699a-d992-4988-9b7b-02a4f9d5615b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1409_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1410_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1411_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1412_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1413_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1414_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1417_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1418_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1419_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1420_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1421_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1423_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1425 raw1425Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw1425 raw1425Labels = mixedMoment B raw1425step0 raw1425step0Labels := by
      have ha : raw1425step0 = (fun i j => raw1425 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1425step0 raw1425; decide +kernel
      have hl : raw1425step0Labels = raw1425Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1425 raw1425Labels permutation32 permutation4
    mixedMoment B raw1425step0 raw1425step0Labels = mixedMoment B raw1425step1 raw1425step1Labels := by
      have ha : raw1425step1 = raw1425step0 := by apply Matrix.ext; unfold raw1425step1 raw1425step0; decide +kernel
      have hl : raw1425step0Labels = labelEmbedding7 ∘ raw1425step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1425step0 raw1425step0Labels raw1425step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical1426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1426 raw1426Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw1426 raw1426Labels = mixedMoment B raw1426step0 raw1426step0Labels := by
      have ha : raw1426step0 = (fun i j => raw1426 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1426step0 raw1426; decide +kernel
      have hl : raw1426step0Labels = raw1426Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1426 raw1426Labels permutation32 permutation4
    _ = mixedMoment B node1236 node1236Labels := by rfl

theorem canonical1427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1427 raw1427Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw1427 raw1427Labels = mixedMoment B raw1427step0 raw1427step0Labels := by
      have ha : raw1427step0 = (fun i j => raw1427 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1427step0 raw1427; decide +kernel
      have hl : raw1427step0Labels = raw1427Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1427 raw1427Labels permutation32 permutation6
    mixedMoment B raw1427step0 raw1427step0Labels = mixedMoment B raw1427step1 raw1427step1Labels := by
      have ha : raw1427step1 = -raw1427step0 := by apply Matrix.ext; change ∀ i j, raw1427step1 i j = -(raw1427step0 i j); unfold raw1427step1 raw1427step0; decide +kernel
      have hl : raw1427step1Labels = raw1427step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1427step1 raw1427step1Labels = mixedMoment B raw1427step2 raw1427step2Labels := by
      have ha : raw1427step2 = raw1427step1 := by apply Matrix.ext; unfold raw1427step2 raw1427step1; decide +kernel
      have hl : raw1427step1Labels = labelEmbedding1 ∘ raw1427step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1427step1 raw1427step1Labels raw1427step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

theorem canonical1434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1434 raw1434Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw1434 raw1434Labels = mixedMoment B raw1434step0 raw1434step0Labels := by
      have ha : raw1434step0 = (fun i j => raw1434 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1434step0 raw1434; decide +kernel
      have hl : raw1434step0Labels = raw1434Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1434 raw1434Labels permutation8 permutation4
    mixedMoment B raw1434step0 raw1434step0Labels = mixedMoment B raw1434step1 raw1434step1Labels := by
      have ha : raw1434step1 = raw1434step0 := by apply Matrix.ext; unfold raw1434step1 raw1434step0; decide +kernel
      have hl : raw1434step0Labels = labelEmbedding7 ∘ raw1434step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1434step0 raw1434step0Labels raw1434step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

theorem canonical1435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1435 raw1435Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw1435 raw1435Labels = mixedMoment B raw1435step0 raw1435step0Labels := by
      have ha : raw1435step0 = (fun i j => raw1435 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1435step0 raw1435; decide +kernel
      have hl : raw1435step0Labels = raw1435Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1435 raw1435Labels permutation8 permutation4
    _ = mixedMoment B node1242 node1242Labels := by rfl

theorem canonical1436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1436 raw1436Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw1436 raw1436Labels = mixedMoment B raw1436step0 raw1436step0Labels := by
      have ha : raw1436step0 = (fun i j => raw1436 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1436step0 raw1436; decide +kernel
      have hl : raw1436step0Labels = raw1436Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1436 raw1436Labels permutation8 permutation6
    mixedMoment B raw1436step0 raw1436step0Labels = mixedMoment B raw1436step1 raw1436step1Labels := by
      have ha : raw1436step1 = -raw1436step0 := by apply Matrix.ext; change ∀ i j, raw1436step1 i j = -(raw1436step0 i j); unfold raw1436step1 raw1436step0; decide +kernel
      have hl : raw1436step1Labels = raw1436step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1436step1 raw1436step1Labels = mixedMoment B raw1436step2 raw1436step2Labels := by
      have ha : raw1436step2 = raw1436step1 := by apply Matrix.ext; unfold raw1436step2 raw1436step1; decide +kernel
      have hl : raw1436step1Labels = labelEmbedding1 ∘ raw1436step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1436step1 raw1436step1Labels raw1436step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3300 node3300Labels := by rfl

theorem canonical1437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1437 raw1437Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw1437 raw1437Labels = mixedMoment B raw1437step0 raw1437step0Labels := by
      have ha : raw1437step0 = (fun i j => raw1437 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1437step0 raw1437; decide +kernel
      have hl : raw1437step0Labels = raw1437Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1437 raw1437Labels permutation8 permutation4
    mixedMoment B raw1437step0 raw1437step0Labels = mixedMoment B raw1437step1 raw1437step1Labels := by
      have ha : raw1437step1 = raw1437step0 := by apply Matrix.ext; unfold raw1437step1 raw1437step0; decide +kernel
      have hl : raw1437step0Labels = labelEmbedding7 ∘ raw1437step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1437step0 raw1437step0Labels raw1437step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical1438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1438 raw1438Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw1438 raw1438Labels = mixedMoment B raw1438step0 raw1438step0Labels := by
      have ha : raw1438step0 = (fun i j => raw1438 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1438step0 raw1438; decide +kernel
      have hl : raw1438step0Labels = raw1438Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1438 raw1438Labels permutation8 permutation4
    _ = mixedMoment B node1246 node1246Labels := by rfl

theorem canonical1439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1439 raw1439Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw1439 raw1439Labels = mixedMoment B raw1439step0 raw1439step0Labels := by
      have ha : raw1439step0 = (fun i j => raw1439 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1439step0 raw1439; decide +kernel
      have hl : raw1439step0Labels = raw1439Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1439 raw1439Labels permutation8 permutation6
    mixedMoment B raw1439step0 raw1439step0Labels = mixedMoment B raw1439step1 raw1439step1Labels := by
      have ha : raw1439step1 = -raw1439step0 := by apply Matrix.ext; change ∀ i j, raw1439step1 i j = -(raw1439step0 i j); unfold raw1439step1 raw1439step0; decide +kernel
      have hl : raw1439step1Labels = raw1439step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1439step1 raw1439step1Labels = mixedMoment B raw1439step2 raw1439step2Labels := by
      have ha : raw1439step2 = raw1439step1 := by apply Matrix.ext; unfold raw1439step2 raw1439step1; decide +kernel
      have hl : raw1439step1Labels = labelEmbedding1 ∘ raw1439step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1439step1 raw1439step1Labels raw1439step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3301 node3301Labels := by rfl

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

theorem canonical2190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2190 raw2190Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw2190 raw2190Labels = mixedMoment B raw2190step0 raw2190step0Labels := by
      have ha : raw2190step0 = (fun i j => raw2190 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2190step0 raw2190; decide +kernel
      have hl : raw2190step0Labels = raw2190Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2190 raw2190Labels permutation32 permutation4
    mixedMoment B raw2190step0 raw2190step0Labels = mixedMoment B raw2190step1 raw2190step1Labels := by
      have ha : raw2190step1 = raw2190step0 := by apply Matrix.ext; unfold raw2190step1 raw2190step0; decide +kernel
      have hl : raw2190step0Labels = labelEmbedding7 ∘ raw2190step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2190step0 raw2190step0Labels raw2190step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

theorem canonical2191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2191 raw2191Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw2191 raw2191Labels = mixedMoment B raw2191step0 raw2191step0Labels := by
      have ha : raw2191step0 = (fun i j => raw2191 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2191step0 raw2191; decide +kernel
      have hl : raw2191step0Labels = raw2191Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2191 raw2191Labels permutation32 permutation4
    _ = mixedMoment B node2590 node2590Labels := by rfl

theorem canonical2192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2192 raw2192Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw2192 raw2192Labels = mixedMoment B raw2192step0 raw2192step0Labels := by
      have ha : raw2192step0 = (fun i j => raw2192 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2192step0 raw2192; decide +kernel
      have hl : raw2192step0Labels = raw2192Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2192 raw2192Labels permutation38 permutation6
    mixedMoment B raw2192step0 raw2192step0Labels = mixedMoment B raw2192step1 raw2192step1Labels := by
      have ha : raw2192step1 = -raw2192step0 := by apply Matrix.ext; change ∀ i j, raw2192step1 i j = -(raw2192step0 i j); unfold raw2192step1 raw2192step0; decide +kernel
      have hl : raw2192step1Labels = raw2192step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2192step1 raw2192step1Labels = mixedMoment B raw2192step2 raw2192step2Labels := by
      have ha : raw2192step2 = raw2192step1 := by apply Matrix.ext; unfold raw2192step2 raw2192step1; decide +kernel
      have hl : raw2192step1Labels = labelEmbedding1 ∘ raw2192step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2192step1 raw2192step1Labels raw2192step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3564 node3564Labels := by rfl

theorem canonical2295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2295 raw2295Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw2295 raw2295Labels = mixedMoment B raw2295step0 raw2295step0Labels := by
      have ha : raw2295step0 = (fun i j => raw2295 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2295step0 raw2295; decide +kernel
      have hl : raw2295step0Labels = raw2295Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2295 raw2295Labels permutation8 permutation4
    mixedMoment B raw2295step0 raw2295step0Labels = mixedMoment B raw2295step1 raw2295step1Labels := by
      have ha : raw2295step1 = raw2295step0 := by apply Matrix.ext; unfold raw2295step1 raw2295step0; decide +kernel
      have hl : raw2295step0Labels = labelEmbedding7 ∘ raw2295step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2295step0 raw2295step0Labels raw2295step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

theorem canonical2296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2296 raw2296Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw2296 raw2296Labels = mixedMoment B raw2296step0 raw2296step0Labels := by
      have ha : raw2296step0 = (fun i j => raw2296 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2296step0 raw2296; decide +kernel
      have hl : raw2296step0Labels = raw2296Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2296 raw2296Labels permutation8 permutation4
    _ = mixedMoment B node2765 node2765Labels := by rfl

theorem canonical2297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2297 raw2297Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw2297 raw2297Labels = mixedMoment B raw2297step0 raw2297step0Labels := by
      have ha : raw2297step0 = (fun i j => raw2297 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2297step0 raw2297; decide +kernel
      have hl : raw2297step0Labels = raw2297Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2297 raw2297Labels permutation10 permutation6
    mixedMoment B raw2297step0 raw2297step0Labels = mixedMoment B raw2297step1 raw2297step1Labels := by
      have ha : raw2297step1 = -raw2297step0 := by apply Matrix.ext; change ∀ i j, raw2297step1 i j = -(raw2297step0 i j); unfold raw2297step1 raw2297step0; decide +kernel
      have hl : raw2297step1Labels = raw2297step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2297step1 raw2297step1Labels = mixedMoment B raw2297step2 raw2297step2Labels := by
      have ha : raw2297step2 = raw2297step1 := by apply Matrix.ext; unfold raw2297step2 raw2297step1; decide +kernel
      have hl : raw2297step1Labels = labelEmbedding1 ∘ raw2297step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2297step1 raw2297step1Labels raw2297step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3582 node3582Labels := by rfl

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

theorem canonical2316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2316 raw2316Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw2316 raw2316Labels = mixedMoment B raw2316step0 raw2316step0Labels := by
      have ha : raw2316step0 = (fun i j => raw2316 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2316step0 raw2316; decide +kernel
      have hl : raw2316step0Labels = raw2316Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2316 raw2316Labels permutation8 permutation4
    mixedMoment B raw2316step0 raw2316step0Labels = mixedMoment B raw2316step1 raw2316step1Labels := by
      have ha : raw2316step1 = raw2316step0 := by apply Matrix.ext; unfold raw2316step1 raw2316step0; decide +kernel
      have hl : raw2316step0Labels = labelEmbedding7 ∘ raw2316step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2316step0 raw2316step0Labels raw2316step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

theorem canonical2317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2317 raw2317Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw2317 raw2317Labels = mixedMoment B raw2317step0 raw2317step0Labels := by
      have ha : raw2317step0 = (fun i j => raw2317 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2317step0 raw2317; decide +kernel
      have hl : raw2317step0Labels = raw2317Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2317 raw2317Labels permutation8 permutation4
    _ = mixedMoment B node2782 node2782Labels := by rfl

theorem canonical2318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2318 raw2318Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw2318 raw2318Labels = mixedMoment B raw2318step0 raw2318step0Labels := by
      have ha : raw2318step0 = (fun i j => raw2318 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2318step0 raw2318; decide +kernel
      have hl : raw2318step0Labels = raw2318Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2318 raw2318Labels permutation8 permutation6
    mixedMoment B raw2318step0 raw2318step0Labels = mixedMoment B raw2318step1 raw2318step1Labels := by
      have ha : raw2318step1 = -raw2318step0 := by apply Matrix.ext; change ∀ i j, raw2318step1 i j = -(raw2318step0 i j); unfold raw2318step1 raw2318step0; decide +kernel
      have hl : raw2318step1Labels = raw2318step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2318step1 raw2318step1Labels = mixedMoment B raw2318step2 raw2318step2Labels := by
      have ha : raw2318step2 = raw2318step1 := by apply Matrix.ext; unfold raw2318step2 raw2318step1; decide +kernel
      have hl : raw2318step1Labels = labelEmbedding1 ∘ raw2318step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2318step1 raw2318step1Labels raw2318step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3583 node3583Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical185
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23799 raw23799Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw23799 raw23799Labels = mixedMoment B raw23799step0 raw23799step0Labels := by
      have hz : ∀ j, raw23799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23799step0 = (fun i j => raw23799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23799step0 raw23799; decide +kernel
      have hl : raw23799step0Labels = raw23799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23799 raw23799Labels permutation346 hz
    mixedMoment B raw23799step0 raw23799step0Labels = mixedMoment B raw23799step1 raw23799step1Labels := by
      have hz : ∀ j, raw23799step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23799step1 = (fun i j => raw23799step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23799step1 raw23799step0; decide +kernel
      have hl : raw23799step1Labels = raw23799step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23799step0 raw23799step0Labels permutation56 hz
    mixedMoment B raw23799step1 raw23799step1Labels = mixedMoment B raw23799step2 raw23799step2Labels := by
      have ha : raw23799step2 = -raw23799step1 := by apply Matrix.ext; change ∀ i j, raw23799step2 i j = -(raw23799step1 i j); unfold raw23799step2 raw23799step1; decide +kernel
      have hl : raw23799step2Labels = raw23799step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4069 node4069Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical187
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23942 raw23942Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw23942 raw23942Labels = mixedMoment B raw23942step0 raw23942step0Labels := by
      have hz : ∀ j, raw23942 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23942step0 = (fun i j => raw23942 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23942step0 raw23942; decide +kernel
      have hl : raw23942step0Labels = raw23942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23942 raw23942Labels permutation346 hz
    mixedMoment B raw23942step0 raw23942step0Labels = mixedMoment B raw23942step1 raw23942step1Labels := by
      have ha : raw23942step1 = (fun i j => raw23942step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23942step1 raw23942step0; decide +kernel
      have hl : raw23942step1Labels = raw23942step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23942step0 raw23942step0Labels permutation50 permutation2
    mixedMoment B raw23942step1 raw23942step1Labels = mixedMoment B raw23942step2 raw23942step2Labels := by
      have ha : raw23942step2 = -raw23942step1 := by apply Matrix.ext; change ∀ i j, raw23942step2 i j = -(raw23942step1 i j); unfold raw23942step2 raw23942step1; decide +kernel
      have hl : raw23942step2Labels = raw23942step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1737 node1737Labels := by rfl

theorem canonical23947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23947 raw23947Labels = mixedMoment B node3308 node3308Labels := by
  calc
    mixedMoment B raw23947 raw23947Labels = mixedMoment B raw23947step0 raw23947step0Labels := by
      have hz : ∀ j, raw23947 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23947step0 = (fun i j => raw23947 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23947step0 raw23947; decide +kernel
      have hl : raw23947step0Labels = raw23947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23947 raw23947Labels permutation346 hz
    mixedMoment B raw23947step0 raw23947step0Labels = mixedMoment B raw23947step1 raw23947step1Labels := by
      have hz : ∀ j, raw23947step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23947step1 = (fun i j => raw23947step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23947step1 raw23947step0; decide +kernel
      have hl : raw23947step1Labels = raw23947step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23947step0 raw23947step0Labels permutation56 hz
    mixedMoment B raw23947step1 raw23947step1Labels = mixedMoment B raw23947step2 raw23947step2Labels := by
      have ha : raw23947step2 = (fun i j => raw23947step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23947step2 raw23947step1; decide +kernel
      have hl : raw23947step2Labels = raw23947step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23947step1 raw23947step1Labels permutation8 permutation4
    mixedMoment B raw23947step2 raw23947step2Labels = mixedMoment B raw23947step3 raw23947step3Labels := by
      have ha : raw23947step3 = -raw23947step2 := by apply Matrix.ext; change ∀ i j, raw23947step3 i j = -(raw23947step2 i j); unfold raw23947step3 raw23947step2; decide +kernel
      have hl : raw23947step3Labels = raw23947step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3308 node3308Labels := by rfl

theorem canonical23952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23952 raw23952Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw23952 raw23952Labels = mixedMoment B raw23952step0 raw23952step0Labels := by
      have hz : ∀ j, raw23952 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23952step0 = (fun i j => raw23952 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23952step0 raw23952; decide +kernel
      have hl : raw23952step0Labels = raw23952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23952 raw23952Labels permutation346 hz
    mixedMoment B raw23952step0 raw23952step0Labels = mixedMoment B raw23952step1 raw23952step1Labels := by
      have ha : raw23952step1 = (fun i j => raw23952step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23952step1 raw23952step0; decide +kernel
      have hl : raw23952step1Labels = raw23952step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23952step0 raw23952step0Labels permutation34 permutation4
    mixedMoment B raw23952step1 raw23952step1Labels = mixedMoment B raw23952step2 raw23952step2Labels := by
      have ha : raw23952step2 = -raw23952step1 := by apply Matrix.ext; change ∀ i j, raw23952step2 i j = -(raw23952step1 i j); unfold raw23952step2 raw23952step1; decide +kernel
      have hl : raw23952step2Labels = raw23952step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3293 node3293Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical188
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24081 raw24081Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw24081 raw24081Labels = mixedMoment B raw24081step0 raw24081step0Labels := by
      have hz : ∀ j, raw24081 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24081step0 = (fun i j => raw24081 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24081step0 raw24081; decide +kernel
      have hl : raw24081step0Labels = raw24081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24081 raw24081Labels permutation346 hz
    mixedMoment B raw24081step0 raw24081step0Labels = mixedMoment B raw24081step1 raw24081step1Labels := by
      have hz : ∀ j, raw24081step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24081step1 = (fun i j => raw24081step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24081step1 raw24081step0; decide +kernel
      have hl : raw24081step1Labels = raw24081step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24081step0 raw24081step0Labels permutation56 hz
    mixedMoment B raw24081step1 raw24081step1Labels = mixedMoment B raw24081step2 raw24081step2Labels := by
      have ha : raw24081step2 = (fun i j => raw24081step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24081step2 raw24081step1; decide +kernel
      have hl : raw24081step2Labels = raw24081step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24081step1 raw24081step1Labels permutation13 permutation2
    mixedMoment B raw24081step2 raw24081step2Labels = mixedMoment B raw24081step3 raw24081step3Labels := by
      have ha : raw24081step3 = -raw24081step2 := by apply Matrix.ext; change ∀ i j, raw24081step3 i j = -(raw24081step2 i j); unfold raw24081step3 raw24081step2; decide +kernel
      have hl : raw24081step3Labels = raw24081step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1739 node1739Labels := by rfl

theorem canonical24094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24094 raw24094Labels = mixedMoment B node1288 node1288Labels := by
  calc
    mixedMoment B raw24094 raw24094Labels = mixedMoment B raw24094step0 raw24094step0Labels := by
      have hz : ∀ j, raw24094 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24094step0 = (fun i j => raw24094 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24094step0 raw24094; decide +kernel
      have hl : raw24094step0Labels = raw24094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24094 raw24094Labels permutation346 hz
    mixedMoment B raw24094step0 raw24094step0Labels = mixedMoment B raw24094step1 raw24094step1Labels := by
      have hz : ∀ j, raw24094step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24094step1 = (fun i j => raw24094step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24094step1 raw24094step0; decide +kernel
      have hl : raw24094step1Labels = raw24094step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24094step0 raw24094step0Labels permutation56 hz
    mixedMoment B raw24094step1 raw24094step1Labels = mixedMoment B raw24094step2 raw24094step2Labels := by
      have ha : raw24094step2 = (fun i j => raw24094step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24094step2 raw24094step1; decide +kernel
      have hl : raw24094step2Labels = raw24094step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24094step1 raw24094step1Labels permutation10 permutation2
    _ = mixedMoment B node1288 node1288Labels := by rfl

theorem canonical24095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24095 raw24095Labels = mixedMoment B node2585 node2585Labels := by
  calc
    mixedMoment B raw24095 raw24095Labels = mixedMoment B raw24095step0 raw24095step0Labels := by
      have hz : ∀ j, raw24095 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24095step0 = (fun i j => raw24095 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24095step0 raw24095; decide +kernel
      have hl : raw24095step0Labels = raw24095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24095 raw24095Labels permutation346 hz
    mixedMoment B raw24095step0 raw24095step0Labels = mixedMoment B raw24095step1 raw24095step1Labels := by
      have ha : raw24095step1 = (fun i j => raw24095step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24095step1 raw24095step0; decide +kernel
      have hl : raw24095step1Labels = raw24095step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24095step0 raw24095step0Labels permutation34 permutation2
    _ = mixedMoment B node2585 node2585Labels := by rfl

theorem canonical24096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24096 raw24096Labels = mixedMoment B node2585 node2585Labels := by
  calc
    mixedMoment B raw24096 raw24096Labels = mixedMoment B raw24096step0 raw24096step0Labels := by
      have hz : ∀ j, raw24096 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24096step0 = (fun i j => raw24096 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24096step0 raw24096; decide +kernel
      have hl : raw24096step0Labels = raw24096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24096 raw24096Labels permutation265 hz
    mixedMoment B raw24096step0 raw24096step0Labels = mixedMoment B raw24096step1 raw24096step1Labels := by
      have ha : raw24096step1 = (fun i j => raw24096step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24096step1 raw24096step0; decide +kernel
      have hl : raw24096step1Labels = raw24096step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24096step0 raw24096step0Labels permutation34 permutation2
    _ = mixedMoment B node2585 node2585Labels := by rfl

theorem canonical24097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24097 raw24097Labels = mixedMoment B node2771 node2771Labels := by
  calc
    mixedMoment B raw24097 raw24097Labels = mixedMoment B raw24097step0 raw24097step0Labels := by
      have hz : ∀ j, raw24097 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24097step0 = (fun i j => raw24097 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24097step0 raw24097; decide +kernel
      have hl : raw24097step0Labels = raw24097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24097 raw24097Labels permutation346 hz
    mixedMoment B raw24097step0 raw24097step0Labels = mixedMoment B raw24097step1 raw24097step1Labels := by
      have hz : ∀ j, raw24097step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24097step1 = (fun i j => raw24097step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24097step1 raw24097step0; decide +kernel
      have hl : raw24097step1Labels = raw24097step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24097step0 raw24097step0Labels permutation56 hz
    _ = mixedMoment B node2771 node2771Labels := by rfl

theorem canonical24098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24098 raw24098Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw24098 raw24098Labels = mixedMoment B raw24098step0 raw24098step0Labels := by
      have hz : ∀ j, raw24098 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24098step0 = (fun i j => raw24098 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24098step0 raw24098; decide +kernel
      have hl : raw24098step0Labels = raw24098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24098 raw24098Labels permutation346 hz
    mixedMoment B raw24098step0 raw24098step0Labels = mixedMoment B raw24098step1 raw24098step1Labels := by
      have hz : ∀ j, raw24098step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24098step1 = (fun i j => raw24098step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24098step1 raw24098step0; decide +kernel
      have hl : raw24098step1Labels = raw24098step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24098step0 raw24098step0Labels permutation56 hz
    mixedMoment B raw24098step1 raw24098step1Labels = mixedMoment B raw24098step2 raw24098step2Labels := by
      have ha : raw24098step2 = (fun i j => raw24098step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24098step2 raw24098step1; decide +kernel
      have hl : raw24098step2Labels = raw24098step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24098step1 raw24098step1Labels permutation10 permutation2
    _ = mixedMoment B node2686 node2686Labels := by rfl

theorem canonical24099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24099 raw24099Labels = mixedMoment B node2779 node2779Labels := by
  calc
    mixedMoment B raw24099 raw24099Labels = mixedMoment B raw24099step0 raw24099step0Labels := by
      have hz : ∀ j, raw24099 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24099step0 = (fun i j => raw24099 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24099step0 raw24099; decide +kernel
      have hl : raw24099step0Labels = raw24099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24099 raw24099Labels permutation346 hz
    mixedMoment B raw24099step0 raw24099step0Labels = mixedMoment B raw24099step1 raw24099step1Labels := by
      have hz : ∀ j, raw24099step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24099step1 = (fun i j => raw24099step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24099step1 raw24099step0; decide +kernel
      have hl : raw24099step1Labels = raw24099step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24099step0 raw24099step0Labels permutation56 hz
    mixedMoment B raw24099step1 raw24099step1Labels = mixedMoment B raw24099step2 raw24099step2Labels := by
      have ha : raw24099step2 = (fun i j => raw24099step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24099step2 raw24099step1; decide +kernel
      have hl : raw24099step2Labels = raw24099step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24099step1 raw24099step1Labels permutation10 permutation2
    _ = mixedMoment B node2779 node2779Labels := by rfl

theorem canonical24100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24100 raw24100Labels = mixedMoment B node4089 node4089Labels := by
  calc
    mixedMoment B raw24100 raw24100Labels = mixedMoment B raw24100step0 raw24100step0Labels := by
      have hz : ∀ j, raw24100 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24100step0 = (fun i j => raw24100 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24100step0 raw24100; decide +kernel
      have hl : raw24100step0Labels = raw24100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24100 raw24100Labels permutation346 hz
    mixedMoment B raw24100step0 raw24100step0Labels = mixedMoment B raw24100step1 raw24100step1Labels := by
      have hz : ∀ j, raw24100step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24100step1 = (fun i j => raw24100step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24100step1 raw24100step0; decide +kernel
      have hl : raw24100step1Labels = raw24100step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24100step0 raw24100step0Labels permutation56 hz
    mixedMoment B raw24100step1 raw24100step1Labels = mixedMoment B raw24100step2 raw24100step2Labels := by
      have ha : raw24100step2 = (fun i j => raw24100step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24100step2 raw24100step1; decide +kernel
      have hl : raw24100step2Labels = raw24100step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24100step1 raw24100step1Labels permutation10 permutation0
    _ = mixedMoment B node4089 node4089Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical189
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24212 raw24212Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw24212 raw24212Labels = mixedMoment B raw24212step0 raw24212step0Labels := by
      have hz : ∀ j, raw24212 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24212step0 = (fun i j => raw24212 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24212step0 raw24212; decide +kernel
      have hl : raw24212step0Labels = raw24212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24212 raw24212Labels permutation265 hz
    mixedMoment B raw24212step0 raw24212step0Labels = mixedMoment B raw24212step1 raw24212step1Labels := by
      have ha : raw24212step1 = (fun i j => raw24212step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24212step1 raw24212step0; decide +kernel
      have hl : raw24212step1Labels = raw24212step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24212step0 raw24212step0Labels permutation50 permutation2
    mixedMoment B raw24212step1 raw24212step1Labels = mixedMoment B raw24212step2 raw24212step2Labels := by
      have ha : raw24212step2 = -raw24212step1 := by apply Matrix.ext; change ∀ i j, raw24212step2 i j = -(raw24212step1 i j); unfold raw24212step2 raw24212step1; decide +kernel
      have hl : raw24212step2Labels = raw24212step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1737 node1737Labels := by rfl

theorem canonical24213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24213 raw24213Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw24213 raw24213Labels = mixedMoment B raw24213step0 raw24213step0Labels := by
      have hz : ∀ j, raw24213 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24213step0 = (fun i j => raw24213 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24213step0 raw24213; decide +kernel
      have hl : raw24213step0Labels = raw24213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24213 raw24213Labels permutation346 hz
    mixedMoment B raw24213step0 raw24213step0Labels = mixedMoment B raw24213step1 raw24213step1Labels := by
      have hz : ∀ j, raw24213step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24213step1 = (fun i j => raw24213step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24213step1 raw24213step0; decide +kernel
      have hl : raw24213step1Labels = raw24213step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24213step0 raw24213step0Labels permutation56 hz
    mixedMoment B raw24213step1 raw24213step1Labels = mixedMoment B raw24213step2 raw24213step2Labels := by
      have ha : raw24213step2 = (fun i j => raw24213step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24213step2 raw24213step1; decide +kernel
      have hl : raw24213step2Labels = raw24213step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24213step1 raw24213step1Labels permutation12 permutation2
    mixedMoment B raw24213step2 raw24213step2Labels = mixedMoment B raw24213step3 raw24213step3Labels := by
      have ha : raw24213step3 = -raw24213step2 := by apply Matrix.ext; change ∀ i j, raw24213step3 i j = -(raw24213step2 i j); unfold raw24213step3 raw24213step2; decide +kernel
      have hl : raw24213step3Labels = raw24213step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1739 node1739Labels := by rfl

theorem canonical24214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24214 raw24214Labels = mixedMoment B node1753 node1753Labels := by
  calc
    mixedMoment B raw24214 raw24214Labels = mixedMoment B raw24214step0 raw24214step0Labels := by
      have hz : ∀ j, raw24214 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24214step0 = (fun i j => raw24214 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24214step0 raw24214; decide +kernel
      have hl : raw24214step0Labels = raw24214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24214 raw24214Labels permutation346 hz
    mixedMoment B raw24214step0 raw24214step0Labels = mixedMoment B raw24214step1 raw24214step1Labels := by
      have hz : ∀ j, raw24214step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24214step1 = (fun i j => raw24214step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24214step1 raw24214step0; decide +kernel
      have hl : raw24214step1Labels = raw24214step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24214step0 raw24214step0Labels permutation56 hz
    mixedMoment B raw24214step1 raw24214step1Labels = mixedMoment B raw24214step2 raw24214step2Labels := by
      have ha : raw24214step2 = -raw24214step1 := by apply Matrix.ext; change ∀ i j, raw24214step2 i j = -(raw24214step1 i j); unfold raw24214step2 raw24214step1; decide +kernel
      have hl : raw24214step2Labels = raw24214step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1753 node1753Labels := by rfl

theorem canonical24215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24215 raw24215Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw24215 raw24215Labels = mixedMoment B raw24215step0 raw24215step0Labels := by
      have hz : ∀ j, raw24215 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24215step0 = (fun i j => raw24215 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24215step0 raw24215; decide +kernel
      have hl : raw24215step0Labels = raw24215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24215 raw24215Labels permutation346 hz
    mixedMoment B raw24215step0 raw24215step0Labels = mixedMoment B raw24215step1 raw24215step1Labels := by
      have hz : ∀ j, raw24215step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24215step1 = (fun i j => raw24215step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24215step1 raw24215step0; decide +kernel
      have hl : raw24215step1Labels = raw24215step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24215step0 raw24215step0Labels permutation56 hz
    mixedMoment B raw24215step1 raw24215step1Labels = mixedMoment B raw24215step2 raw24215step2Labels := by
      have ha : raw24215step2 = (fun i j => raw24215step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24215step2 raw24215step1; decide +kernel
      have hl : raw24215step2Labels = raw24215step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24215step1 raw24215step1Labels permutation10 permutation4
    mixedMoment B raw24215step2 raw24215step2Labels = mixedMoment B raw24215step3 raw24215step3Labels := by
      have ha : raw24215step3 = -raw24215step2 := by apply Matrix.ext; change ∀ i j, raw24215step3 i j = -(raw24215step2 i j); unfold raw24215step3 raw24215step2; decide +kernel
      have hl : raw24215step3Labels = raw24215step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1727 node1727Labels := by rfl

theorem canonical24216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24216 raw24216Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw24216 raw24216Labels = mixedMoment B raw24216step0 raw24216step0Labels := by
      have hz : ∀ j, raw24216 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24216step0 = (fun i j => raw24216 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24216step0 raw24216; decide +kernel
      have hl : raw24216step0Labels = raw24216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24216 raw24216Labels permutation265 hz
    mixedMoment B raw24216step0 raw24216step0Labels = mixedMoment B raw24216step1 raw24216step1Labels := by
      have ha : raw24216step1 = (fun i j => raw24216step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24216step1 raw24216step0; decide +kernel
      have hl : raw24216step1Labels = raw24216step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24216step0 raw24216step0Labels permutation34 permutation4
    mixedMoment B raw24216step1 raw24216step1Labels = mixedMoment B raw24216step2 raw24216step2Labels := by
      have ha : raw24216step2 = -raw24216step1 := by apply Matrix.ext; change ∀ i j, raw24216step2 i j = -(raw24216step1 i j); unfold raw24216step2 raw24216step1; decide +kernel
      have hl : raw24216step2Labels = raw24216step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3293 node3293Labels := by rfl

theorem canonical24217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24217 raw24217Labels = mixedMoment B node3305 node3305Labels := by
  calc
    mixedMoment B raw24217 raw24217Labels = mixedMoment B raw24217step0 raw24217step0Labels := by
      have hz : ∀ j, raw24217 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24217step0 = (fun i j => raw24217 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24217step0 raw24217; decide +kernel
      have hl : raw24217step0Labels = raw24217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24217 raw24217Labels permutation346 hz
    mixedMoment B raw24217step0 raw24217step0Labels = mixedMoment B raw24217step1 raw24217step1Labels := by
      have hz : ∀ j, raw24217step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24217step1 = (fun i j => raw24217step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24217step1 raw24217step0; decide +kernel
      have hl : raw24217step1Labels = raw24217step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24217step0 raw24217step0Labels permutation56 hz
    mixedMoment B raw24217step1 raw24217step1Labels = mixedMoment B raw24217step2 raw24217step2Labels := by
      have ha : raw24217step2 = (fun i j => raw24217step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24217step2 raw24217step1; decide +kernel
      have hl : raw24217step2Labels = raw24217step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24217step1 raw24217step1Labels permutation10 permutation4
    mixedMoment B raw24217step2 raw24217step2Labels = mixedMoment B raw24217step3 raw24217step3Labels := by
      have ha : raw24217step3 = -raw24217step2 := by apply Matrix.ext; change ∀ i j, raw24217step3 i j = -(raw24217step2 i j); unfold raw24217step3 raw24217step2; decide +kernel
      have hl : raw24217step3Labels = raw24217step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3305 node3305Labels := by rfl

theorem canonical24218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24218 raw24218Labels = mixedMoment B node3309 node3309Labels := by
  calc
    mixedMoment B raw24218 raw24218Labels = mixedMoment B raw24218step0 raw24218step0Labels := by
      have hz : ∀ j, raw24218 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24218step0 = (fun i j => raw24218 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24218step0 raw24218; decide +kernel
      have hl : raw24218step0Labels = raw24218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24218 raw24218Labels permutation346 hz
    mixedMoment B raw24218step0 raw24218step0Labels = mixedMoment B raw24218step1 raw24218step1Labels := by
      have hz : ∀ j, raw24218step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24218step1 = (fun i j => raw24218step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24218step1 raw24218step0; decide +kernel
      have hl : raw24218step1Labels = raw24218step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24218step0 raw24218step0Labels permutation56 hz
    mixedMoment B raw24218step1 raw24218step1Labels = mixedMoment B raw24218step2 raw24218step2Labels := by
      have ha : raw24218step2 = -raw24218step1 := by apply Matrix.ext; change ∀ i j, raw24218step2 i j = -(raw24218step1 i j); unfold raw24218step2 raw24218step1; decide +kernel
      have hl : raw24218step2Labels = raw24218step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3309 node3309Labels := by rfl

theorem canonical24304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24304 raw24304Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw24304 raw24304Labels = mixedMoment B raw24304step0 raw24304step0Labels := by
      have hz : ∀ j, raw24304 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24304step0 = (fun i j => raw24304 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24304step0 raw24304; decide +kernel
      have hl : raw24304step0Labels = raw24304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24304 raw24304Labels permutation346 hz
    mixedMoment B raw24304step0 raw24304step0Labels = mixedMoment B raw24304step1 raw24304step1Labels := by
      have ha : raw24304step1 = (fun i j => raw24304step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24304step1 raw24304step0; decide +kernel
      have hl : raw24304step1Labels = raw24304step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24304step0 raw24304step0Labels permutation34 permutation2
    _ = mixedMoment B node5163 node5163Labels := by rfl

theorem canonical24305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24305 raw24305Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw24305 raw24305Labels = mixedMoment B raw24305step0 raw24305step0Labels := by
      have hz : ∀ j, raw24305 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24305step0 = (fun i j => raw24305 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24305step0 raw24305; decide +kernel
      have hl : raw24305step0Labels = raw24305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24305 raw24305Labels permutation265 hz
    mixedMoment B raw24305step0 raw24305step0Labels = mixedMoment B raw24305step1 raw24305step1Labels := by
      have ha : raw24305step1 = (fun i j => raw24305step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24305step1 raw24305step0; decide +kernel
      have hl : raw24305step1Labels = raw24305step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24305step0 raw24305step0Labels permutation34 permutation2
    _ = mixedMoment B node5163 node5163Labels := by rfl

theorem canonical24306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24306 raw24306Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw24306 raw24306Labels = mixedMoment B raw24306step0 raw24306step0Labels := by
      have hz : ∀ j, raw24306 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24306step0 = (fun i j => raw24306 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24306step0 raw24306; decide +kernel
      have hl : raw24306step0Labels = raw24306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24306 raw24306Labels permutation346 hz
    mixedMoment B raw24306step0 raw24306step0Labels = mixedMoment B raw24306step1 raw24306step1Labels := by
      have hz : ∀ j, raw24306step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24306step1 = (fun i j => raw24306step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24306step1 raw24306step0; decide +kernel
      have hl : raw24306step1Labels = raw24306step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24306step0 raw24306step0Labels permutation56 hz
    _ = mixedMoment B node5291 node5291Labels := by rfl

theorem canonical24307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24307 raw24307Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw24307 raw24307Labels = mixedMoment B raw24307step0 raw24307step0Labels := by
      have hz : ∀ j, raw24307 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24307step0 = (fun i j => raw24307 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24307step0 raw24307; decide +kernel
      have hl : raw24307step0Labels = raw24307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24307 raw24307Labels permutation346 hz
    mixedMoment B raw24307step0 raw24307step0Labels = mixedMoment B raw24307step1 raw24307step1Labels := by
      have hz : ∀ j, raw24307step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24307step1 = (fun i j => raw24307step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24307step1 raw24307step0; decide +kernel
      have hl : raw24307step1Labels = raw24307step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24307step0 raw24307step0Labels permutation56 hz
    mixedMoment B raw24307step1 raw24307step1Labels = mixedMoment B raw24307step2 raw24307step2Labels := by
      have ha : raw24307step2 = (fun i j => raw24307step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24307step2 raw24307step1; decide +kernel
      have hl : raw24307step2Labels = raw24307step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24307step1 raw24307step1Labels permutation10 permutation2
    _ = mixedMoment B node5274 node5274Labels := by rfl

theorem canonical24308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24308 raw24308Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw24308 raw24308Labels = mixedMoment B raw24308step0 raw24308step0Labels := by
      have hz : ∀ j, raw24308 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24308step0 = (fun i j => raw24308 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24308step0 raw24308; decide +kernel
      have hl : raw24308step0Labels = raw24308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24308 raw24308Labels permutation346 hz
    mixedMoment B raw24308step0 raw24308step0Labels = mixedMoment B raw24308step1 raw24308step1Labels := by
      have hz : ∀ j, raw24308step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24308step1 = (fun i j => raw24308step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24308step1 raw24308step0; decide +kernel
      have hl : raw24308step1Labels = raw24308step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24308step0 raw24308step0Labels permutation56 hz
    mixedMoment B raw24308step1 raw24308step1Labels = mixedMoment B raw24308step2 raw24308step2Labels := by
      have ha : raw24308step2 = (fun i j => raw24308step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24308step2 raw24308step1; decide +kernel
      have hl : raw24308step2Labels = raw24308step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24308step1 raw24308step1Labels permutation10 permutation2
    _ = mixedMoment B node5304 node5304Labels := by rfl

theorem canonical24309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24309 raw24309Labels = mixedMoment B node4176 node4176Labels := by
  calc
    mixedMoment B raw24309 raw24309Labels = mixedMoment B raw24309step0 raw24309step0Labels := by
      have hz : ∀ j, raw24309 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24309step0 = (fun i j => raw24309 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24309step0 raw24309; decide +kernel
      have hl : raw24309step0Labels = raw24309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24309 raw24309Labels permutation346 hz
    mixedMoment B raw24309step0 raw24309step0Labels = mixedMoment B raw24309step1 raw24309step1Labels := by
      have ha : raw24309step1 = (fun i j => raw24309step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24309step1 raw24309step0; decide +kernel
      have hl : raw24309step1Labels = raw24309step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24309step0 raw24309step0Labels permutation38 permutation3
    mixedMoment B raw24309step1 raw24309step1Labels = mixedMoment B raw24309step2 raw24309step2Labels := by
      have ha : raw24309step2 = raw24309step1 := by apply Matrix.ext; unfold raw24309step2 raw24309step1; decide +kernel
      have hl : raw24309step1Labels = labelEmbedding6 ∘ raw24309step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24309step1 raw24309step1Labels raw24309step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4176 node4176Labels := by rfl

theorem canonical24310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24310 raw24310Labels = mixedMoment B node4545 node4545Labels := by
  calc
    mixedMoment B raw24310 raw24310Labels = mixedMoment B raw24310step0 raw24310step0Labels := by
      have ha : raw24310step0 = (fun i j => raw24310 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24310step0 raw24310; decide +kernel
      have hl : raw24310step0Labels = raw24310Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24310 raw24310Labels permutation182 permutation3
    mixedMoment B raw24310step0 raw24310step0Labels = mixedMoment B raw24310step1 raw24310step1Labels := by
      have ha : raw24310step1 = raw24310step0 := by apply Matrix.ext; unfold raw24310step1 raw24310step0; decide +kernel
      have hl : raw24310step0Labels = labelEmbedding6 ∘ raw24310step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24310step0 raw24310step0Labels raw24310step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4545 node4545Labels := by rfl

theorem canonical24311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24311 raw24311Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw24311 raw24311Labels = mixedMoment B raw24311step0 raw24311step0Labels := by
      have hz : ∀ j, raw24311 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24311step0 = (fun i j => raw24311 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24311step0 raw24311; decide +kernel
      have hl : raw24311step0Labels = raw24311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24311 raw24311Labels permutation346 hz
    mixedMoment B raw24311step0 raw24311step0Labels = mixedMoment B raw24311step1 raw24311step1Labels := by
      have ha : raw24311step1 = (fun i j => raw24311step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24311step1 raw24311step0; decide +kernel
      have hl : raw24311step1Labels = raw24311step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24311step0 raw24311step0Labels permutation38 permutation3
    mixedMoment B raw24311step1 raw24311step1Labels = mixedMoment B raw24311step2 raw24311step2Labels := by
      have ha : raw24311step2 = raw24311step1 := by apply Matrix.ext; unfold raw24311step2 raw24311step1; decide +kernel
      have hl : raw24311step1Labels = labelEmbedding6 ∘ raw24311step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24311step1 raw24311step1Labels raw24311step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4607 node4607Labels := by rfl

theorem canonical24312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24312 raw24312Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw24312 raw24312Labels = mixedMoment B raw24312step0 raw24312step0Labels := by
      have hz : ∀ j, raw24312 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24312step0 = (fun i j => raw24312 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24312step0 raw24312; decide +kernel
      have hl : raw24312step0Labels = raw24312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24312 raw24312Labels permutation346 hz
    mixedMoment B raw24312step0 raw24312step0Labels = mixedMoment B raw24312step1 raw24312step1Labels := by
      have ha : raw24312step1 = (fun i j => raw24312step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24312step1 raw24312step0; decide +kernel
      have hl : raw24312step1Labels = raw24312step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24312step0 raw24312step0Labels permutation44 permutation2
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical24313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24313 raw24313Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw24313 raw24313Labels = mixedMoment B raw24313step0 raw24313step0Labels := by
      have hz : ∀ j, raw24313 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24313step0 = (fun i j => raw24313 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24313step0 raw24313; decide +kernel
      have hl : raw24313step0Labels = raw24313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24313 raw24313Labels permutation346 hz
    mixedMoment B raw24313step0 raw24313step0Labels = mixedMoment B raw24313step1 raw24313step1Labels := by
      have ha : raw24313step1 = (fun i j => raw24313step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24313step1 raw24313step0; decide +kernel
      have hl : raw24313step1Labels = raw24313step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24313step0 raw24313step0Labels permutation44 permutation2
    _ = mixedMoment B node4616 node4616Labels := by rfl

theorem canonical24314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24314 raw24314Labels = mixedMoment B node4176 node4176Labels := by
  calc
    mixedMoment B raw24314 raw24314Labels = mixedMoment B raw24314step0 raw24314step0Labels := by
      have hz : ∀ j, raw24314 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24314step0 = (fun i j => raw24314 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24314step0 raw24314; decide +kernel
      have hl : raw24314step0Labels = raw24314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24314 raw24314Labels permutation265 hz
    mixedMoment B raw24314step0 raw24314step0Labels = mixedMoment B raw24314step1 raw24314step1Labels := by
      have ha : raw24314step1 = (fun i j => raw24314step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24314step1 raw24314step0; decide +kernel
      have hl : raw24314step1Labels = raw24314step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24314step0 raw24314step0Labels permutation38 permutation3
    mixedMoment B raw24314step1 raw24314step1Labels = mixedMoment B raw24314step2 raw24314step2Labels := by
      have ha : raw24314step2 = raw24314step1 := by apply Matrix.ext; unfold raw24314step2 raw24314step1; decide +kernel
      have hl : raw24314step1Labels = labelEmbedding6 ∘ raw24314step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24314step1 raw24314step1Labels raw24314step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4176 node4176Labels := by rfl

theorem canonical24315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24315 raw24315Labels = mixedMoment B node4545 node4545Labels := by
  calc
    mixedMoment B raw24315 raw24315Labels = mixedMoment B raw24315step0 raw24315step0Labels := by
      have ha : raw24315step0 = (fun i j => raw24315 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24315step0 raw24315; decide +kernel
      have hl : raw24315step0Labels = raw24315Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24315 raw24315Labels permutation158 permutation3
    mixedMoment B raw24315step0 raw24315step0Labels = mixedMoment B raw24315step1 raw24315step1Labels := by
      have ha : raw24315step1 = raw24315step0 := by apply Matrix.ext; unfold raw24315step1 raw24315step0; decide +kernel
      have hl : raw24315step0Labels = labelEmbedding6 ∘ raw24315step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24315step0 raw24315step0Labels raw24315step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4545 node4545Labels := by rfl

theorem canonical24316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24316 raw24316Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw24316 raw24316Labels = mixedMoment B raw24316step0 raw24316step0Labels := by
      have hz : ∀ j, raw24316 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24316step0 = (fun i j => raw24316 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24316step0 raw24316; decide +kernel
      have hl : raw24316step0Labels = raw24316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24316 raw24316Labels permutation265 hz
    mixedMoment B raw24316step0 raw24316step0Labels = mixedMoment B raw24316step1 raw24316step1Labels := by
      have ha : raw24316step1 = (fun i j => raw24316step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24316step1 raw24316step0; decide +kernel
      have hl : raw24316step1Labels = raw24316step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24316step0 raw24316step0Labels permutation38 permutation3
    mixedMoment B raw24316step1 raw24316step1Labels = mixedMoment B raw24316step2 raw24316step2Labels := by
      have ha : raw24316step2 = raw24316step1 := by apply Matrix.ext; unfold raw24316step2 raw24316step1; decide +kernel
      have hl : raw24316step1Labels = labelEmbedding6 ∘ raw24316step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24316step1 raw24316step1Labels raw24316step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4607 node4607Labels := by rfl

theorem canonical24317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24317 raw24317Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw24317 raw24317Labels = mixedMoment B raw24317step0 raw24317step0Labels := by
      have hz : ∀ j, raw24317 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24317step0 = (fun i j => raw24317 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24317step0 raw24317; decide +kernel
      have hl : raw24317step0Labels = raw24317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24317 raw24317Labels permutation265 hz
    mixedMoment B raw24317step0 raw24317step0Labels = mixedMoment B raw24317step1 raw24317step1Labels := by
      have ha : raw24317step1 = (fun i j => raw24317step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24317step1 raw24317step0; decide +kernel
      have hl : raw24317step1Labels = raw24317step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24317step0 raw24317step0Labels permutation44 permutation2
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical24318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24318 raw24318Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw24318 raw24318Labels = mixedMoment B raw24318step0 raw24318step0Labels := by
      have hz : ∀ j, raw24318 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24318step0 = (fun i j => raw24318 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24318step0 raw24318; decide +kernel
      have hl : raw24318step0Labels = raw24318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24318 raw24318Labels permutation265 hz
    mixedMoment B raw24318step0 raw24318step0Labels = mixedMoment B raw24318step1 raw24318step1Labels := by
      have ha : raw24318step1 = (fun i j => raw24318step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24318step1 raw24318step0; decide +kernel
      have hl : raw24318step1Labels = raw24318step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24318step0 raw24318step0Labels permutation44 permutation2
    _ = mixedMoment B node4616 node4616Labels := by rfl

theorem canonical24319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24319 raw24319Labels = mixedMoment B node4188 node4188Labels := by
  calc
    mixedMoment B raw24319 raw24319Labels = mixedMoment B raw24319step0 raw24319step0Labels := by
      have hz : ∀ j, raw24319 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24319step0 = (fun i j => raw24319 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24319step0 raw24319; decide +kernel
      have hl : raw24319step0Labels = raw24319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24319 raw24319Labels permutation346 hz
    mixedMoment B raw24319step0 raw24319step0Labels = mixedMoment B raw24319step1 raw24319step1Labels := by
      have hz : ∀ j, raw24319step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24319step1 = (fun i j => raw24319step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24319step1 raw24319step0; decide +kernel
      have hl : raw24319step1Labels = raw24319step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24319step0 raw24319step0Labels permutation56 hz
    mixedMoment B raw24319step1 raw24319step1Labels = mixedMoment B raw24319step2 raw24319step2Labels := by
      have ha : raw24319step2 = (fun i j => raw24319step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24319step2 raw24319step1; decide +kernel
      have hl : raw24319step2Labels = raw24319step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24319step1 raw24319step1Labels permutation11 permutation3
    mixedMoment B raw24319step2 raw24319step2Labels = mixedMoment B raw24319step3 raw24319step3Labels := by
      have ha : raw24319step3 = raw24319step2 := by apply Matrix.ext; unfold raw24319step3 raw24319step2; decide +kernel
      have hl : raw24319step2Labels = labelEmbedding6 ∘ raw24319step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24319step2 raw24319step2Labels raw24319step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4188 node4188Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical190
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24320 raw24320Labels = mixedMoment B node4556 node4556Labels := by
  calc
    mixedMoment B raw24320 raw24320Labels = mixedMoment B raw24320step0 raw24320step0Labels := by
      have hz : ∀ j, raw24320 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24320step0 = (fun i j => raw24320 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24320step0 raw24320; decide +kernel
      have hl : raw24320step0Labels = raw24320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24320 raw24320Labels permutation346 hz
    mixedMoment B raw24320step0 raw24320step0Labels = mixedMoment B raw24320step1 raw24320step1Labels := by
      have ha : raw24320step1 = (fun i j => raw24320step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24320step1 raw24320step0; decide +kernel
      have hl : raw24320step1Labels = raw24320step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24320step0 raw24320step0Labels permutation35 permutation3
    mixedMoment B raw24320step1 raw24320step1Labels = mixedMoment B raw24320step2 raw24320step2Labels := by
      have ha : raw24320step2 = raw24320step1 := by apply Matrix.ext; unfold raw24320step2 raw24320step1; decide +kernel
      have hl : raw24320step1Labels = labelEmbedding6 ∘ raw24320step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24320step1 raw24320step1Labels raw24320step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4556 node4556Labels := by rfl

theorem canonical24321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24321 raw24321Labels = mixedMoment B node4556 node4556Labels := by
  calc
    mixedMoment B raw24321 raw24321Labels = mixedMoment B raw24321step0 raw24321step0Labels := by
      have hz : ∀ j, raw24321 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24321step0 = (fun i j => raw24321 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24321step0 raw24321; decide +kernel
      have hl : raw24321step0Labels = raw24321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24321 raw24321Labels permutation265 hz
    mixedMoment B raw24321step0 raw24321step0Labels = mixedMoment B raw24321step1 raw24321step1Labels := by
      have ha : raw24321step1 = (fun i j => raw24321step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24321step1 raw24321step0; decide +kernel
      have hl : raw24321step1Labels = raw24321step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24321step0 raw24321step0Labels permutation35 permutation3
    mixedMoment B raw24321step1 raw24321step1Labels = mixedMoment B raw24321step2 raw24321step2Labels := by
      have ha : raw24321step2 = raw24321step1 := by apply Matrix.ext; unfold raw24321step2 raw24321step1; decide +kernel
      have hl : raw24321step1Labels = labelEmbedding6 ∘ raw24321step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24321step1 raw24321step1Labels raw24321step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4556 node4556Labels := by rfl

theorem canonical24322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24322 raw24322Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw24322 raw24322Labels = mixedMoment B raw24322step0 raw24322step0Labels := by
      have hz : ∀ j, raw24322 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24322step0 = (fun i j => raw24322 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24322step0 raw24322; decide +kernel
      have hl : raw24322step0Labels = raw24322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24322 raw24322Labels permutation346 hz
    mixedMoment B raw24322step0 raw24322step0Labels = mixedMoment B raw24322step1 raw24322step1Labels := by
      have hz : ∀ j, raw24322step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24322step1 = (fun i j => raw24322step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24322step1 raw24322step0; decide +kernel
      have hl : raw24322step1Labels = raw24322step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24322step0 raw24322step0Labels permutation56 hz
    mixedMoment B raw24322step1 raw24322step1Labels = mixedMoment B raw24322step2 raw24322step2Labels := by
      have ha : raw24322step2 = (fun i j => raw24322step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24322step2 raw24322step1; decide +kernel
      have hl : raw24322step2Labels = raw24322step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24322step1 raw24322step1Labels permutation10 permutation2
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical24323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24323 raw24323Labels = mixedMoment B node4620 node4620Labels := by
  calc
    mixedMoment B raw24323 raw24323Labels = mixedMoment B raw24323step0 raw24323step0Labels := by
      have hz : ∀ j, raw24323 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24323step0 = (fun i j => raw24323 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24323step0 raw24323; decide +kernel
      have hl : raw24323step0Labels = raw24323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24323 raw24323Labels permutation346 hz
    mixedMoment B raw24323step0 raw24323step0Labels = mixedMoment B raw24323step1 raw24323step1Labels := by
      have hz : ∀ j, raw24323step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24323step1 = (fun i j => raw24323step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24323step1 raw24323step0; decide +kernel
      have hl : raw24323step1Labels = raw24323step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24323step0 raw24323step0Labels permutation56 hz
    mixedMoment B raw24323step1 raw24323step1Labels = mixedMoment B raw24323step2 raw24323step2Labels := by
      have ha : raw24323step2 = (fun i j => raw24323step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24323step2 raw24323step1; decide +kernel
      have hl : raw24323step2Labels = raw24323step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24323step1 raw24323step1Labels permutation11 permutation2
    _ = mixedMoment B node4620 node4620Labels := by rfl

theorem canonical24324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24324 raw24324Labels = mixedMoment B node4179 node4179Labels := by
  calc
    mixedMoment B raw24324 raw24324Labels = mixedMoment B raw24324step0 raw24324step0Labels := by
      have hz : ∀ j, raw24324 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24324step0 = (fun i j => raw24324 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24324step0 raw24324; decide +kernel
      have hl : raw24324step0Labels = raw24324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24324 raw24324Labels permutation346 hz
    mixedMoment B raw24324step0 raw24324step0Labels = mixedMoment B raw24324step1 raw24324step1Labels := by
      have hz : ∀ j, raw24324step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24324step1 = (fun i j => raw24324step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24324step1 raw24324step0; decide +kernel
      have hl : raw24324step1Labels = raw24324step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24324step0 raw24324step0Labels permutation56 hz
    mixedMoment B raw24324step1 raw24324step1Labels = mixedMoment B raw24324step2 raw24324step2Labels := by
      have ha : raw24324step2 = (fun i j => raw24324step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24324step2 raw24324step1; decide +kernel
      have hl : raw24324step2Labels = raw24324step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24324step1 raw24324step1Labels permutation9 permutation3
    mixedMoment B raw24324step2 raw24324step2Labels = mixedMoment B raw24324step3 raw24324step3Labels := by
      have ha : raw24324step3 = raw24324step2 := by apply Matrix.ext; unfold raw24324step3 raw24324step2; decide +kernel
      have hl : raw24324step2Labels = labelEmbedding6 ∘ raw24324step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24324step2 raw24324step2Labels raw24324step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4179 node4179Labels := by rfl

theorem canonical24325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24325 raw24325Labels = mixedMoment B node4548 node4548Labels := by
  calc
    mixedMoment B raw24325 raw24325Labels = mixedMoment B raw24325step0 raw24325step0Labels := by
      have hz : ∀ j, raw24325 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24325step0 = (fun i j => raw24325 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24325step0 raw24325; decide +kernel
      have hl : raw24325step0Labels = raw24325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24325 raw24325Labels permutation346 hz
    mixedMoment B raw24325step0 raw24325step0Labels = mixedMoment B raw24325step1 raw24325step1Labels := by
      have ha : raw24325step1 = (fun i j => raw24325step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24325step1 raw24325step0; decide +kernel
      have hl : raw24325step1Labels = raw24325step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24325step0 raw24325step0Labels permutation33 permutation3
    mixedMoment B raw24325step1 raw24325step1Labels = mixedMoment B raw24325step2 raw24325step2Labels := by
      have ha : raw24325step2 = raw24325step1 := by apply Matrix.ext; unfold raw24325step2 raw24325step1; decide +kernel
      have hl : raw24325step1Labels = labelEmbedding6 ∘ raw24325step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24325step1 raw24325step1Labels raw24325step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4548 node4548Labels := by rfl

theorem canonical24326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24326 raw24326Labels = mixedMoment B node4548 node4548Labels := by
  calc
    mixedMoment B raw24326 raw24326Labels = mixedMoment B raw24326step0 raw24326step0Labels := by
      have hz : ∀ j, raw24326 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24326step0 = (fun i j => raw24326 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24326step0 raw24326; decide +kernel
      have hl : raw24326step0Labels = raw24326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24326 raw24326Labels permutation265 hz
    mixedMoment B raw24326step0 raw24326step0Labels = mixedMoment B raw24326step1 raw24326step1Labels := by
      have ha : raw24326step1 = (fun i j => raw24326step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24326step1 raw24326step0; decide +kernel
      have hl : raw24326step1Labels = raw24326step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24326step0 raw24326step0Labels permutation33 permutation3
    mixedMoment B raw24326step1 raw24326step1Labels = mixedMoment B raw24326step2 raw24326step2Labels := by
      have ha : raw24326step2 = raw24326step1 := by apply Matrix.ext; unfold raw24326step2 raw24326step1; decide +kernel
      have hl : raw24326step1Labels = labelEmbedding6 ∘ raw24326step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24326step1 raw24326step1Labels raw24326step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4548 node4548Labels := by rfl

theorem canonical24327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24327 raw24327Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw24327 raw24327Labels = mixedMoment B raw24327step0 raw24327step0Labels := by
      have hz : ∀ j, raw24327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24327step0 = (fun i j => raw24327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24327step0 raw24327; decide +kernel
      have hl : raw24327step0Labels = raw24327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24327 raw24327Labels permutation346 hz
    mixedMoment B raw24327step0 raw24327step0Labels = mixedMoment B raw24327step1 raw24327step1Labels := by
      have hz : ∀ j, raw24327step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24327step1 = (fun i j => raw24327step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24327step1 raw24327step0; decide +kernel
      have hl : raw24327step1Labels = raw24327step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24327step0 raw24327step0Labels permutation56 hz
    mixedMoment B raw24327step1 raw24327step1Labels = mixedMoment B raw24327step2 raw24327step2Labels := by
      have ha : raw24327step2 = (fun i j => raw24327step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24327step2 raw24327step1; decide +kernel
      have hl : raw24327step2Labels = raw24327step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24327step1 raw24327step1Labels permutation9 permutation3
    mixedMoment B raw24327step2 raw24327step2Labels = mixedMoment B raw24327step3 raw24327step3Labels := by
      have ha : raw24327step3 = raw24327step2 := by apply Matrix.ext; unfold raw24327step3 raw24327step2; decide +kernel
      have hl : raw24327step2Labels = labelEmbedding6 ∘ raw24327step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24327step2 raw24327step2Labels raw24327step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4611 node4611Labels := by rfl

theorem canonical24328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24328 raw24328Labels = mixedMoment B node4617 node4617Labels := by
  calc
    mixedMoment B raw24328 raw24328Labels = mixedMoment B raw24328step0 raw24328step0Labels := by
      have hz : ∀ j, raw24328 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24328step0 = (fun i j => raw24328 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24328step0 raw24328; decide +kernel
      have hl : raw24328step0Labels = raw24328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24328 raw24328Labels permutation346 hz
    mixedMoment B raw24328step0 raw24328step0Labels = mixedMoment B raw24328step1 raw24328step1Labels := by
      have hz : ∀ j, raw24328step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24328step1 = (fun i j => raw24328step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24328step1 raw24328step0; decide +kernel
      have hl : raw24328step1Labels = raw24328step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24328step0 raw24328step0Labels permutation56 hz
    mixedMoment B raw24328step1 raw24328step1Labels = mixedMoment B raw24328step2 raw24328step2Labels := by
      have ha : raw24328step2 = (fun i j => raw24328step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24328step2 raw24328step1; decide +kernel
      have hl : raw24328step2Labels = raw24328step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24328step1 raw24328step1Labels permutation12 permutation3
    mixedMoment B raw24328step2 raw24328step2Labels = mixedMoment B raw24328step3 raw24328step3Labels := by
      have ha : raw24328step3 = raw24328step2 := by apply Matrix.ext; unfold raw24328step3 raw24328step2; decide +kernel
      have hl : raw24328step2Labels = labelEmbedding6 ∘ raw24328step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24328step2 raw24328step2Labels raw24328step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4617 node4617Labels := by rfl

theorem canonical24329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24329 raw24329Labels = mixedMoment B node4178 node4178Labels := by
  calc
    mixedMoment B raw24329 raw24329Labels = mixedMoment B raw24329step0 raw24329step0Labels := by
      have hz : ∀ j, raw24329 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24329step0 = (fun i j => raw24329 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24329step0 raw24329; decide +kernel
      have hl : raw24329step0Labels = raw24329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24329 raw24329Labels permutation346 hz
    mixedMoment B raw24329step0 raw24329step0Labels = mixedMoment B raw24329step1 raw24329step1Labels := by
      have hz : ∀ j, raw24329step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24329step1 = (fun i j => raw24329step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24329step1 raw24329step0; decide +kernel
      have hl : raw24329step1Labels = raw24329step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24329step0 raw24329step0Labels permutation56 hz
    mixedMoment B raw24329step1 raw24329step1Labels = mixedMoment B raw24329step2 raw24329step2Labels := by
      have ha : raw24329step2 = (fun i j => raw24329step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24329step2 raw24329step1; decide +kernel
      have hl : raw24329step2Labels = raw24329step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24329step1 raw24329step1Labels permutation8 permutation3
    mixedMoment B raw24329step2 raw24329step2Labels = mixedMoment B raw24329step3 raw24329step3Labels := by
      have ha : raw24329step3 = raw24329step2 := by apply Matrix.ext; unfold raw24329step3 raw24329step2; decide +kernel
      have hl : raw24329step2Labels = labelEmbedding6 ∘ raw24329step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24329step2 raw24329step2Labels raw24329step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4178 node4178Labels := by rfl

theorem canonical24330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24330 raw24330Labels = mixedMoment B node4547 node4547Labels := by
  calc
    mixedMoment B raw24330 raw24330Labels = mixedMoment B raw24330step0 raw24330step0Labels := by
      have hz : ∀ j, raw24330 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24330step0 = (fun i j => raw24330 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24330step0 raw24330; decide +kernel
      have hl : raw24330step0Labels = raw24330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24330 raw24330Labels permutation346 hz
    mixedMoment B raw24330step0 raw24330step0Labels = mixedMoment B raw24330step1 raw24330step1Labels := by
      have ha : raw24330step1 = (fun i j => raw24330step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24330step1 raw24330step0; decide +kernel
      have hl : raw24330step1Labels = raw24330step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24330step0 raw24330step0Labels permutation32 permutation3
    mixedMoment B raw24330step1 raw24330step1Labels = mixedMoment B raw24330step2 raw24330step2Labels := by
      have ha : raw24330step2 = raw24330step1 := by apply Matrix.ext; unfold raw24330step2 raw24330step1; decide +kernel
      have hl : raw24330step1Labels = labelEmbedding6 ∘ raw24330step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24330step1 raw24330step1Labels raw24330step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4547 node4547Labels := by rfl

theorem canonical24331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24331 raw24331Labels = mixedMoment B node4547 node4547Labels := by
  calc
    mixedMoment B raw24331 raw24331Labels = mixedMoment B raw24331step0 raw24331step0Labels := by
      have hz : ∀ j, raw24331 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24331step0 = (fun i j => raw24331 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24331step0 raw24331; decide +kernel
      have hl : raw24331step0Labels = raw24331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24331 raw24331Labels permutation265 hz
    mixedMoment B raw24331step0 raw24331step0Labels = mixedMoment B raw24331step1 raw24331step1Labels := by
      have ha : raw24331step1 = (fun i j => raw24331step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24331step1 raw24331step0; decide +kernel
      have hl : raw24331step1Labels = raw24331step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24331step0 raw24331step0Labels permutation32 permutation3
    mixedMoment B raw24331step1 raw24331step1Labels = mixedMoment B raw24331step2 raw24331step2Labels := by
      have ha : raw24331step2 = raw24331step1 := by apply Matrix.ext; unfold raw24331step2 raw24331step1; decide +kernel
      have hl : raw24331step1Labels = labelEmbedding6 ∘ raw24331step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24331step1 raw24331step1Labels raw24331step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4547 node4547Labels := by rfl

theorem canonical24332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24332 raw24332Labels = mixedMoment B node4609 node4609Labels := by
  calc
    mixedMoment B raw24332 raw24332Labels = mixedMoment B raw24332step0 raw24332step0Labels := by
      have hz : ∀ j, raw24332 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24332step0 = (fun i j => raw24332 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24332step0 raw24332; decide +kernel
      have hl : raw24332step0Labels = raw24332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24332 raw24332Labels permutation346 hz
    mixedMoment B raw24332step0 raw24332step0Labels = mixedMoment B raw24332step1 raw24332step1Labels := by
      have hz : ∀ j, raw24332step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24332step1 = (fun i j => raw24332step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24332step1 raw24332step0; decide +kernel
      have hl : raw24332step1Labels = raw24332step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24332step0 raw24332step0Labels permutation56 hz
    mixedMoment B raw24332step1 raw24332step1Labels = mixedMoment B raw24332step2 raw24332step2Labels := by
      have ha : raw24332step2 = (fun i j => raw24332step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24332step2 raw24332step1; decide +kernel
      have hl : raw24332step2Labels = raw24332step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24332step1 raw24332step1Labels permutation8 permutation3
    mixedMoment B raw24332step2 raw24332step2Labels = mixedMoment B raw24332step3 raw24332step3Labels := by
      have ha : raw24332step3 = raw24332step2 := by apply Matrix.ext; unfold raw24332step3 raw24332step2; decide +kernel
      have hl : raw24332step2Labels = labelEmbedding6 ∘ raw24332step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24332step2 raw24332step2Labels raw24332step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4609 node4609Labels := by rfl

theorem canonical24333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24333 raw24333Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw24333 raw24333Labels = mixedMoment B raw24333step0 raw24333step0Labels := by
      have hz : ∀ j, raw24333 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24333step0 = (fun i j => raw24333 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24333step0 raw24333; decide +kernel
      have hl : raw24333step0Labels = raw24333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24333 raw24333Labels permutation346 hz
    mixedMoment B raw24333step0 raw24333step0Labels = mixedMoment B raw24333step1 raw24333step1Labels := by
      have hz : ∀ j, raw24333step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24333step1 = (fun i j => raw24333step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24333step1 raw24333step0; decide +kernel
      have hl : raw24333step1Labels = raw24333step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24333step0 raw24333step0Labels permutation56 hz
    mixedMoment B raw24333step1 raw24333step1Labels = mixedMoment B raw24333step2 raw24333step2Labels := by
      have ha : raw24333step2 = (fun i j => raw24333step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24333step2 raw24333step1; decide +kernel
      have hl : raw24333step2Labels = raw24333step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24333step1 raw24333step1Labels permutation10 permutation2
    _ = mixedMoment B node4608 node4608Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4602 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4602 node4602Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1236 node1236Labels + mixedMoment B node3293 node3293Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1425 singletonSmall4602
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4602) = raw1425Labels := by decide +kernel
  rw [hl, canonical1425 B hB] at h
  have hc0 : mixedMoment B raw1425 (Fin.cases (0 : Fin 2) singletonSmall4602) =
      mixedMoment B node1236 node1236Labels := by
    have ha : raw1425 = raw1426 := by apply Matrix.ext; unfold raw1425 raw1426; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4602 = raw1426Labels := by decide +kernel
    rw [ha, hj, canonical1426 B hB]
  have hc1 : mixedMoment B raw1425 (Fin.cases (1 : Fin 2) singletonSmall4602) =
      mixedMoment B node3293 node3293Labels := by
    have ha : raw1425 = raw1427 := by apply Matrix.ext; unfold raw1425 raw1427; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4602 = raw1427Labels := by decide +kernel
    rw [ha, hj, canonical1427 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4608 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4608 node4608Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1242 node1242Labels + mixedMoment B node3300 node3300Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1434 singletonSmall4608
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4608) = raw1434Labels := by decide +kernel
  rw [hl, canonical1434 B hB] at h
  have hc0 : mixedMoment B raw1434 (Fin.cases (0 : Fin 2) singletonSmall4608) =
      mixedMoment B node1242 node1242Labels := by
    have ha : raw1434 = raw1435 := by apply Matrix.ext; unfold raw1434 raw1435; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4608 = raw1435Labels := by decide +kernel
    rw [ha, hj, canonical1435 B hB]
  have hc1 : mixedMoment B raw1434 (Fin.cases (1 : Fin 2) singletonSmall4608) =
      mixedMoment B node3300 node3300Labels := by
    have ha : raw1434 = raw1436 := by apply Matrix.ext; unfold raw1434 raw1436; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4608 = raw1436Labels := by decide +kernel
    rw [ha, hj, canonical1436 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4612 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4612 node4612Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1246 node1246Labels + mixedMoment B node3301 node3301Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1437 singletonSmall4612
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4612) = raw1437Labels := by decide +kernel
  rw [hl, canonical1437 B hB] at h
  have hc0 : mixedMoment B raw1437 (Fin.cases (0 : Fin 2) singletonSmall4612) =
      mixedMoment B node1246 node1246Labels := by
    have ha : raw1437 = raw1438 := by apply Matrix.ext; unfold raw1437 raw1438; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4612 = raw1438Labels := by decide +kernel
    rw [ha, hj, canonical1438 B hB]
  have hc1 : mixedMoment B raw1437 (Fin.cases (1 : Fin 2) singletonSmall4612) =
      mixedMoment B node3301 node3301Labels := by
    have ha : raw1437 = raw1439 := by apply Matrix.ext; unfold raw1437 raw1439; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4612 = raw1439Labels := by decide +kernel
    rw [ha, hj, canonical1439 B hB]
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

theorem singleton5163 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5163 node5163Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2590 node2590Labels + mixedMoment B node3564 node3564Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2190 singletonSmall5163
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5163) = raw2190Labels := by decide +kernel
  rw [hl, canonical2190 B hB] at h
  have hc0 : mixedMoment B raw2190 (Fin.cases (0 : Fin 2) singletonSmall5163) =
      mixedMoment B node2590 node2590Labels := by
    have ha : raw2190 = raw2191 := by apply Matrix.ext; unfold raw2190 raw2191; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5163 = raw2191Labels := by decide +kernel
    rw [ha, hj, canonical2191 B hB]
  have hc1 : mixedMoment B raw2190 (Fin.cases (1 : Fin 2) singletonSmall5163) =
      mixedMoment B node3564 node3564Labels := by
    have ha : raw2190 = raw2192 := by apply Matrix.ext; unfold raw2190 raw2192; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5163 = raw2192Labels := by decide +kernel
    rw [ha, hj, canonical2192 B hB]
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

theorem singleton5291 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5291 node5291Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2765 node2765Labels + mixedMoment B node3582 node3582Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2295 singletonSmall5291
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5291) = raw2295Labels := by decide +kernel
  rw [hl, canonical2295 B hB] at h
  have hc0 : mixedMoment B raw2295 (Fin.cases (0 : Fin 2) singletonSmall5291) =
      mixedMoment B node2765 node2765Labels := by
    have ha : raw2295 = raw2296 := by apply Matrix.ext; unfold raw2295 raw2296; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5291 = raw2296Labels := by decide +kernel
    rw [ha, hj, canonical2296 B hB]
  have hc1 : mixedMoment B raw2295 (Fin.cases (1 : Fin 2) singletonSmall5291) =
      mixedMoment B node3582 node3582Labels := by
    have ha : raw2295 = raw2297 := by apply Matrix.ext; unfold raw2295 raw2297; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5291 = raw2297Labels := by decide +kernel
    rw [ha, hj, canonical2297 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5304 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5304 node5304Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2782 node2782Labels + mixedMoment B node3583 node3583Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2316 singletonSmall5304
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5304) = raw2316Labels := by decide +kernel
  rw [hl, canonical2316 B hB] at h
  have hc0 : mixedMoment B raw2316 (Fin.cases (0 : Fin 2) singletonSmall5304) =
      mixedMoment B node2782 node2782Labels := by
    have ha : raw2316 = raw2317 := by apply Matrix.ext; unfold raw2316 raw2317; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5304 = raw2317Labels := by decide +kernel
    rw [ha, hj, canonical2317 B hB]
  have hc1 : mixedMoment B raw2316 (Fin.cases (1 : Fin 2) singletonSmall5304) =
      mixedMoment B node3583 node3583Labels := by
    have ha : raw2316 = raw2318 := by apply Matrix.ext; unfold raw2316 raw2318; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5304 = raw2318Labels := by decide +kernel
    rw [ha, hj, canonical2318 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound1236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1236 node1236Labels = Sparse.eval nodeValue1236 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1236) = mixedMoment B node1236 node1236Labels := rfl
  simpa [nodeValue1236, Sparse.eval] using hc.symm

theorem sound1242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1242 node1242Labels = Sparse.eval nodeValue1242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1242) = mixedMoment B node1242 node1242Labels := rfl
  simpa [nodeValue1242, Sparse.eval] using hc.symm

theorem sound1246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1246 node1246Labels = Sparse.eval nodeValue1246 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1246) = mixedMoment B node1246 node1246Labels := rfl
  simpa [nodeValue1246, Sparse.eval] using hc.symm

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

theorem sound1288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1288 node1288Labels = Sparse.eval nodeValue1288 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1288) = mixedMoment B node1288 node1288Labels := rfl
  simpa [nodeValue1288, Sparse.eval] using hc.symm

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

theorem zero1753 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1753 node1753Labels = 0 := by
  exact mixedMoment_order_one B hB node1753 node1753Labels 1
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

theorem sound1737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1737 node1737Labels = Sparse.eval nodeValue1737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1737) = mixedMoment B node1737 node1737Labels := rfl
  simpa [nodeValue1737, Sparse.eval] using hc.symm

theorem sound1739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1739 node1739Labels = Sparse.eval nodeValue1739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1739) = mixedMoment B node1739 node1739Labels := rfl
  simpa [nodeValue1739, Sparse.eval] using hc.symm

theorem sound1753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1753 node1753Labels = Sparse.eval nodeValue1753 (mixedVector B) := by
  simpa only [nodeValue1753, Sparse.eval_nil] using zero1753 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2585 node2585Labels = Sparse.eval nodeValue2585 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2585) = mixedMoment B node2585 node2585Labels := rfl
  simpa [nodeValue2585, Sparse.eval] using hc.symm

theorem sound2590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2590 node2590Labels = Sparse.eval nodeValue2590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2590) = mixedMoment B node2590 node2590Labels := rfl
  simpa [nodeValue2590, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2765 node2765Labels = Sparse.eval nodeValue2765 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2765) = mixedMoment B node2765 node2765Labels := rfl
  simpa [nodeValue2765, Sparse.eval] using hc.symm

theorem sound2771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2771 node2771Labels = Sparse.eval nodeValue2771 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2771) = mixedMoment B node2771 node2771Labels := rfl
  simpa [nodeValue2771, Sparse.eval] using hc.symm

theorem sound2779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2779 node2779Labels = Sparse.eval nodeValue2779 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2779) = mixedMoment B node2779 node2779Labels := rfl
  simpa [nodeValue2779, Sparse.eval] using hc.symm

theorem sound2782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2782 node2782Labels = Sparse.eval nodeValue2782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2782) = mixedMoment B node2782 node2782Labels := rfl
  simpa [nodeValue2782, Sparse.eval] using hc.symm

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

theorem sound3293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3293 node3293Labels = Sparse.eval nodeValue3293 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3293) = mixedMoment B node3293 node3293Labels := rfl
  simpa [nodeValue3293, Sparse.eval] using hc.symm

theorem sound3300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3300 node3300Labels = Sparse.eval nodeValue3300 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3300) = mixedMoment B node3300 node3300Labels := rfl
  simpa [nodeValue3300, Sparse.eval] using hc.symm

theorem sound3301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3301 node3301Labels = Sparse.eval nodeValue3301 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3301) = mixedMoment B node3301 node3301Labels := rfl
  simpa [nodeValue3301, Sparse.eval] using hc.symm

theorem sound3305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3305 node3305Labels = Sparse.eval nodeValue3305 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3305) = mixedMoment B node3305 node3305Labels := rfl
  simpa [nodeValue3305, Sparse.eval] using hc.symm

theorem sound3308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3308 node3308Labels = Sparse.eval nodeValue3308 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3308) = mixedMoment B node3308 node3308Labels := rfl
  simpa [nodeValue3308, Sparse.eval] using hc.symm

theorem sound3309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3309 node3309Labels = Sparse.eval nodeValue3309 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3309) = mixedMoment B node3309 node3309Labels := rfl
  simpa [nodeValue3309, Sparse.eval] using hc.symm

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

theorem sound3564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3564 node3564Labels = Sparse.eval nodeValue3564 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3564) = mixedMoment B node3564 node3564Labels := rfl
  simpa [nodeValue3564, Sparse.eval] using hc.symm

theorem sound3582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3582 node3582Labels = Sparse.eval nodeValue3582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3582) = mixedMoment B node3582 node3582Labels := rfl
  simpa [nodeValue3582, Sparse.eval] using hc.symm

theorem sound3583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3583 node3583Labels = Sparse.eval nodeValue3583 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3583) = mixedMoment B node3583 node3583Labels := rfl
  simpa [nodeValue3583, Sparse.eval] using hc.symm

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

theorem sound4069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4069 node4069Labels = Sparse.eval nodeValue4069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4069) = mixedMoment B node4069 node4069Labels := rfl
  simpa [nodeValue4069, Sparse.eval] using hc.symm

theorem sound4089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4089 node4089Labels = Sparse.eval nodeValue4089 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4089) = mixedMoment B node4089 node4089Labels := rfl
  simpa [nodeValue4089, Sparse.eval] using hc.symm

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

theorem sound4176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4176 node4176Labels = Sparse.eval nodeValue4176 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4176) = mixedMoment B node4176 node4176Labels := rfl
  simpa [nodeValue4176, Sparse.eval] using hc.symm

theorem sound4178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4178 node4178Labels = Sparse.eval nodeValue4178 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4178) = mixedMoment B node4178 node4178Labels := rfl
  simpa [nodeValue4178, Sparse.eval] using hc.symm

theorem sound4179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4179 node4179Labels = Sparse.eval nodeValue4179 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4179) = mixedMoment B node4179 node4179Labels := rfl
  simpa [nodeValue4179, Sparse.eval] using hc.symm

theorem sound4188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4188 node4188Labels = Sparse.eval nodeValue4188 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4188) = mixedMoment B node4188 node4188Labels := rfl
  simpa [nodeValue4188, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4545 node4545Labels = Sparse.eval nodeValue4545 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4545) = mixedMoment B node4545 node4545Labels := rfl
  simpa [nodeValue4545, Sparse.eval] using hc.symm

theorem sound4547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4547 node4547Labels = Sparse.eval nodeValue4547 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4547) = mixedMoment B node4547 node4547Labels := rfl
  simpa [nodeValue4547, Sparse.eval] using hc.symm

theorem sound4548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4548 node4548Labels = Sparse.eval nodeValue4548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4548) = mixedMoment B node4548 node4548Labels := rfl
  simpa [nodeValue4548, Sparse.eval] using hc.symm

theorem sound4556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4556 node4556Labels = Sparse.eval nodeValue4556 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4556) = mixedMoment B node4556 node4556Labels := rfl
  simpa [nodeValue4556, Sparse.eval] using hc.symm

theorem sound4602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4602 node4602Labels = Sparse.eval nodeValue4602 (mixedVector B) := by
  have h := singleton4602 B _hB
  rw [sound1236 B _hB _hF, sound3293 B _hB _hF] at h
  norm_num [nodeValue4602, nodeValue1236, nodeValue3293, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4607 node4607Labels = Sparse.eval nodeValue4607 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4607) = mixedMoment B node4607 node4607Labels := rfl
  simpa [nodeValue4607, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4608 node4608Labels = Sparse.eval nodeValue4608 (mixedVector B) := by
  have h := singleton4608 B _hB
  rw [sound1242 B _hB _hF, sound3300 B _hB _hF] at h
  norm_num [nodeValue4608, nodeValue1242, nodeValue3300, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4609 node4609Labels = Sparse.eval nodeValue4609 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4609) = mixedMoment B node4609 node4609Labels := rfl
  simpa [nodeValue4609, Sparse.eval] using hc.symm

theorem sound4611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4611 node4611Labels = Sparse.eval nodeValue4611 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4611) = mixedMoment B node4611 node4611Labels := rfl
  simpa [nodeValue4611, Sparse.eval] using hc.symm

theorem sound4612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4612 node4612Labels = Sparse.eval nodeValue4612 (mixedVector B) := by
  have h := singleton4612 B _hB
  rw [sound1246 B _hB _hF, sound3301 B _hB _hF] at h
  norm_num [nodeValue4612, nodeValue1246, nodeValue3301, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4616 node4616Labels = Sparse.eval nodeValue4616 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4616) = mixedMoment B node4616 node4616Labels := rfl
  simpa [nodeValue4616, Sparse.eval] using hc.symm

theorem sound4617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4617 node4617Labels = Sparse.eval nodeValue4617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4617) = mixedMoment B node4617 node4617Labels := rfl
  simpa [nodeValue4617, Sparse.eval] using hc.symm

theorem sound4620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4620 node4620Labels = Sparse.eval nodeValue4620 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4620) = mixedMoment B node4620 node4620Labels := rfl
  simpa [nodeValue4620, Sparse.eval] using hc.symm

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

theorem sound5163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5163 node5163Labels = Sparse.eval nodeValue5163 (mixedVector B) := by
  have h := singleton5163 B _hB
  rw [sound2590 B _hB _hF, sound3564 B _hB _hF] at h
  norm_num [nodeValue5163, nodeValue2590, nodeValue3564, Sparse.eval] at h ⊢
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

theorem sound5274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5274 node5274Labels = Sparse.eval nodeValue5274 (mixedVector B) := by
  simpa only [nodeValue5274, Sparse.eval_nil] using zero5274 B _hB _hF

theorem sound5291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5291 node5291Labels = Sparse.eval nodeValue5291 (mixedVector B) := by
  have h := singleton5291 B _hB
  rw [sound2765 B _hB _hF, sound3582 B _hB _hF] at h
  norm_num [nodeValue5291, nodeValue2765, nodeValue3582, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5304 node5304Labels = Sparse.eval nodeValue5304 (mixedVector B) := by
  have h := singleton5304 B _hB
  rw [sound2782 B _hB _hF, sound3583 B _hB _hF] at h
  norm_num [nodeValue5304, nodeValue2782, nodeValue3583, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources51
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1647 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1647 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1647 + difference 0 0) (sourceB1647 + difference 0 0) sourceC1647) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1288) := by
    have ha : (tripleCharges (sourceA1647 + difference 0 0) (sourceB1647 + difference 0 0) sourceC1647) = raw24094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1647 sourceB1647 sourceC1647 difference raw24094; decide +kernel
    rw [ha]
    exact (canonical24094 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1647 + difference 0 1) (sourceB1647 + difference 1 0) sourceC1647) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2585) := by
    have ha : (tripleCharges (sourceA1647 + difference 0 1) (sourceB1647 + difference 1 0) sourceC1647) = raw24095 := by
      apply Matrix.ext; unfold tripleCharges sourceA1647 sourceB1647 sourceC1647 difference raw24095; decide +kernel
    rw [ha]
    exact (canonical24095 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1647 + difference 0 2) (sourceB1647 + difference 2 0) sourceC1647) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2585) := by
    have ha : (tripleCharges (sourceA1647 + difference 0 2) (sourceB1647 + difference 2 0) sourceC1647) = raw24096 := by
      apply Matrix.ext; unfold tripleCharges sourceA1647 sourceB1647 sourceC1647 difference raw24096; decide +kernel
    rw [ha]
    exact (canonical24096 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1647 + difference 0 3) (sourceB1647 + difference 3 0) sourceC1647) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2771) := by
    have ha : (tripleCharges (sourceA1647 + difference 0 3) (sourceB1647 + difference 3 0) sourceC1647) = raw24097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1647 sourceB1647 sourceC1647 difference raw24097; decide +kernel
    rw [ha]
    exact (canonical24097 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1647 + difference 0 4) (sourceB1647 + difference 4 0) sourceC1647) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA1647 + difference 0 4) (sourceB1647 + difference 4 0) sourceC1647) = raw24098 := by
      apply Matrix.ext; unfold tripleCharges sourceA1647 sourceB1647 sourceC1647 difference raw24098; decide +kernel
    rw [ha]
    exact (canonical24098 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1647 + difference 0 5) (sourceB1647 + difference 5 0) sourceC1647) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2779) := by
    have ha : (tripleCharges (sourceA1647 + difference 0 5) (sourceB1647 + difference 5 0) sourceC1647) = raw24099 := by
      apply Matrix.ext; unfold tripleCharges sourceA1647 sourceB1647 sourceC1647 difference raw24099; decide +kernel
    rw [ha]
    exact (canonical24099 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1647 + sourceB1647) sourceC1647) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (doubleCharges (sourceA1647 + sourceB1647) sourceC1647) = raw24100 := by
      apply Matrix.ext; unfold doubleCharges sourceA1647 sourceB1647 sourceC1647 raw24100; decide +kernel
    rw [ha]
    exact (canonical24100 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1647 sourceB1647 sourceC1647
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1647, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1654 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1654 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1654 + difference 0 0) (sourceB1654 + difference 0 0) sourceC1654) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3308) := by
    have ha : (tripleCharges (sourceA1654 + difference 0 0) (sourceB1654 + difference 0 0) sourceC1654) = raw23947 := by
      apply Matrix.ext; unfold tripleCharges sourceA1654 sourceB1654 sourceC1654 difference raw23947; decide +kernel
    rw [ha]
    exact (canonical23947 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1654 + difference 0 1) (sourceB1654 + difference 1 0) sourceC1654) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1654 + difference 0 1) (sourceB1654 + difference 1 0) sourceC1654) = raw23942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1654 sourceB1654 sourceC1654 difference raw23942; decide +kernel
    rw [ha]
    exact (canonical23942 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1654 + difference 0 2) (sourceB1654 + difference 2 0) sourceC1654) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1654 + difference 0 2) (sourceB1654 + difference 2 0) sourceC1654) = raw24212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1654 sourceB1654 sourceC1654 difference raw24212; decide +kernel
    rw [ha]
    exact (canonical24212 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1654 + difference 0 3) (sourceB1654 + difference 3 0) sourceC1654) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1654 + difference 0 3) (sourceB1654 + difference 3 0) sourceC1654) = raw24081 := by
      apply Matrix.ext; unfold tripleCharges sourceA1654 sourceB1654 sourceC1654 difference raw24081; decide +kernel
    rw [ha]
    exact (canonical24081 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1654 + difference 0 4) (sourceB1654 + difference 4 0) sourceC1654) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1654 + difference 0 4) (sourceB1654 + difference 4 0) sourceC1654) = raw24213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1654 sourceB1654 sourceC1654 difference raw24213; decide +kernel
    rw [ha]
    exact (canonical24213 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1654 + difference 0 5) (sourceB1654 + difference 5 0) sourceC1654) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1753) := by
    have ha : (tripleCharges (sourceA1654 + difference 0 5) (sourceB1654 + difference 5 0) sourceC1654) = raw24214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1654 sourceB1654 sourceC1654 difference raw24214; decide +kernel
    rw [ha]
    exact (canonical24214 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1654 + sourceB1654) sourceC1654) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1654 + sourceB1654) sourceC1654) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1654 sourceB1654 sourceC1654 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1654 sourceB1654 sourceC1654
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1654, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1655 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1655 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1655 + difference 3 0) (sourceB1655 + difference 0 3) sourceC1655) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1655 + difference 3 0) (sourceB1655 + difference 0 3) sourceC1655) = raw24215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1655 sourceB1655 sourceC1655 difference raw24215; decide +kernel
    rw [ha]
    exact (canonical24215 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1655 + difference 3 1) (sourceB1655 + difference 1 3) sourceC1655) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1655 + difference 3 1) (sourceB1655 + difference 1 3) sourceC1655) = raw23952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1655 sourceB1655 sourceC1655 difference raw23952; decide +kernel
    rw [ha]
    exact (canonical23952 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1655 + difference 3 2) (sourceB1655 + difference 2 3) sourceC1655) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1655 + difference 3 2) (sourceB1655 + difference 2 3) sourceC1655) = raw24216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1655 sourceB1655 sourceC1655 difference raw24216; decide +kernel
    rw [ha]
    exact (canonical24216 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1655 + difference 3 3) (sourceB1655 + difference 3 3) sourceC1655) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3308) := by
    have ha : (tripleCharges (sourceA1655 + difference 3 3) (sourceB1655 + difference 3 3) sourceC1655) = raw23947 := by
      apply Matrix.ext; unfold tripleCharges sourceA1655 sourceB1655 sourceC1655 difference raw23947; decide +kernel
    rw [ha]
    exact (canonical23947 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1655 + difference 3 4) (sourceB1655 + difference 4 3) sourceC1655) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA1655 + difference 3 4) (sourceB1655 + difference 4 3) sourceC1655) = raw24217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1655 sourceB1655 sourceC1655 difference raw24217; decide +kernel
    rw [ha]
    exact (canonical24217 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1655 + difference 3 5) (sourceB1655 + difference 5 3) sourceC1655) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3309) := by
    have ha : (tripleCharges (sourceA1655 + difference 3 5) (sourceB1655 + difference 5 3) sourceC1655) = raw24218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1655 sourceB1655 sourceC1655 difference raw24218; decide +kernel
    rw [ha]
    exact (canonical24218 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1655 + sourceB1655) sourceC1655) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1655 + sourceB1655) sourceC1655) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1655 sourceB1655 sourceC1655 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1655 sourceB1655 sourceC1655
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1655, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1661 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1661 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1661 + difference 0 1) (sourceB1661 + difference 1 0) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA1661 + difference 0 1) (sourceB1661 + difference 1 0) sourceC1661) = raw24304 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24304; decide +kernel
    rw [ha]
    exact (canonical24304 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1661 + difference 0 2) (sourceB1661 + difference 2 0) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA1661 + difference 0 2) (sourceB1661 + difference 2 0) sourceC1661) = raw24305 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24305; decide +kernel
    rw [ha]
    exact (canonical24305 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1661 + difference 0 3) (sourceB1661 + difference 3 0) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA1661 + difference 0 3) (sourceB1661 + difference 3 0) sourceC1661) = raw24306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24306; decide +kernel
    rw [ha]
    exact (canonical24306 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1661 + difference 0 4) (sourceB1661 + difference 4 0) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA1661 + difference 0 4) (sourceB1661 + difference 4 0) sourceC1661) = raw24307 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24307; decide +kernel
    rw [ha]
    exact (canonical24307 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1661 + difference 0 5) (sourceB1661 + difference 5 0) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA1661 + difference 0 5) (sourceB1661 + difference 5 0) sourceC1661) = raw24308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24308; decide +kernel
    rw [ha]
    exact (canonical24308 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1661 + difference 1 0) (sourceB1661 + difference 0 1) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4176) := by
    have ha : (tripleCharges (sourceA1661 + difference 1 0) (sourceB1661 + difference 0 1) sourceC1661) = raw24309 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24309; decide +kernel
    rw [ha]
    exact (canonical24309 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1661 + difference 1 2) (sourceB1661 + difference 2 1) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4545) := by
    have ha : (tripleCharges (sourceA1661 + difference 1 2) (sourceB1661 + difference 2 1) sourceC1661) = raw24310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24310; decide +kernel
    rw [ha]
    exact (canonical24310 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1661 + difference 1 3) (sourceB1661 + difference 3 1) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA1661 + difference 1 3) (sourceB1661 + difference 3 1) sourceC1661) = raw24311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24311; decide +kernel
    rw [ha]
    exact (canonical24311 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1661 + difference 1 4) (sourceB1661 + difference 4 1) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1661 + difference 1 4) (sourceB1661 + difference 4 1) sourceC1661) = raw24312 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24312; decide +kernel
    rw [ha]
    exact (canonical24312 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1661 + difference 1 5) (sourceB1661 + difference 5 1) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA1661 + difference 1 5) (sourceB1661 + difference 5 1) sourceC1661) = raw24313 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24313; decide +kernel
    rw [ha]
    exact (canonical24313 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1661 + difference 2 0) (sourceB1661 + difference 0 2) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4176) := by
    have ha : (tripleCharges (sourceA1661 + difference 2 0) (sourceB1661 + difference 0 2) sourceC1661) = raw24314 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24314; decide +kernel
    rw [ha]
    exact (canonical24314 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1661 + difference 2 1) (sourceB1661 + difference 1 2) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4545) := by
    have ha : (tripleCharges (sourceA1661 + difference 2 1) (sourceB1661 + difference 1 2) sourceC1661) = raw24315 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24315; decide +kernel
    rw [ha]
    exact (canonical24315 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1661 + difference 2 3) (sourceB1661 + difference 3 2) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA1661 + difference 2 3) (sourceB1661 + difference 3 2) sourceC1661) = raw24316 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24316; decide +kernel
    rw [ha]
    exact (canonical24316 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1661 + difference 2 4) (sourceB1661 + difference 4 2) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1661 + difference 2 4) (sourceB1661 + difference 4 2) sourceC1661) = raw24317 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24317; decide +kernel
    rw [ha]
    exact (canonical24317 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1661 + difference 2 5) (sourceB1661 + difference 5 2) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA1661 + difference 2 5) (sourceB1661 + difference 5 2) sourceC1661) = raw24318 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24318; decide +kernel
    rw [ha]
    exact (canonical24318 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1661 + difference 3 0) (sourceB1661 + difference 0 3) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4188) := by
    have ha : (tripleCharges (sourceA1661 + difference 3 0) (sourceB1661 + difference 0 3) sourceC1661) = raw24319 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24319; decide +kernel
    rw [ha]
    exact (canonical24319 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1661 + difference 3 1) (sourceB1661 + difference 1 3) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4556) := by
    have ha : (tripleCharges (sourceA1661 + difference 3 1) (sourceB1661 + difference 1 3) sourceC1661) = raw24320 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24320; decide +kernel
    rw [ha]
    exact (canonical24320 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1661 + difference 3 2) (sourceB1661 + difference 2 3) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4556) := by
    have ha : (tripleCharges (sourceA1661 + difference 3 2) (sourceB1661 + difference 2 3) sourceC1661) = raw24321 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24321; decide +kernel
    rw [ha]
    exact (canonical24321 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1661 + difference 3 4) (sourceB1661 + difference 4 3) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1661 + difference 3 4) (sourceB1661 + difference 4 3) sourceC1661) = raw24322 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24322; decide +kernel
    rw [ha]
    exact (canonical24322 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1661 + difference 3 5) (sourceB1661 + difference 5 3) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4620) := by
    have ha : (tripleCharges (sourceA1661 + difference 3 5) (sourceB1661 + difference 5 3) sourceC1661) = raw24323 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24323; decide +kernel
    rw [ha]
    exact (canonical24323 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1661 + difference 4 0) (sourceB1661 + difference 0 4) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4179) := by
    have ha : (tripleCharges (sourceA1661 + difference 4 0) (sourceB1661 + difference 0 4) sourceC1661) = raw24324 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24324; decide +kernel
    rw [ha]
    exact (canonical24324 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1661 + difference 4 1) (sourceB1661 + difference 1 4) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4548) := by
    have ha : (tripleCharges (sourceA1661 + difference 4 1) (sourceB1661 + difference 1 4) sourceC1661) = raw24325 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24325; decide +kernel
    rw [ha]
    exact (canonical24325 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1661 + difference 4 2) (sourceB1661 + difference 2 4) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4548) := by
    have ha : (tripleCharges (sourceA1661 + difference 4 2) (sourceB1661 + difference 2 4) sourceC1661) = raw24326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24326; decide +kernel
    rw [ha]
    exact (canonical24326 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1661 + difference 4 3) (sourceB1661 + difference 3 4) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA1661 + difference 4 3) (sourceB1661 + difference 3 4) sourceC1661) = raw24327 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24327; decide +kernel
    rw [ha]
    exact (canonical24327 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1661 + difference 4 5) (sourceB1661 + difference 5 4) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA1661 + difference 4 5) (sourceB1661 + difference 5 4) sourceC1661) = raw24328 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24328; decide +kernel
    rw [ha]
    exact (canonical24328 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1661 + difference 5 0) (sourceB1661 + difference 0 5) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4178) := by
    have ha : (tripleCharges (sourceA1661 + difference 5 0) (sourceB1661 + difference 0 5) sourceC1661) = raw24329 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24329; decide +kernel
    rw [ha]
    exact (canonical24329 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1661 + difference 5 1) (sourceB1661 + difference 1 5) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4547) := by
    have ha : (tripleCharges (sourceA1661 + difference 5 1) (sourceB1661 + difference 1 5) sourceC1661) = raw24330 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24330; decide +kernel
    rw [ha]
    exact (canonical24330 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1661 + difference 5 2) (sourceB1661 + difference 2 5) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4547) := by
    have ha : (tripleCharges (sourceA1661 + difference 5 2) (sourceB1661 + difference 2 5) sourceC1661) = raw24331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24331; decide +kernel
    rw [ha]
    exact (canonical24331 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1661 + difference 5 3) (sourceB1661 + difference 3 5) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA1661 + difference 5 3) (sourceB1661 + difference 3 5) sourceC1661) = raw24332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24332; decide +kernel
    rw [ha]
    exact (canonical24332 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1661 + difference 5 4) (sourceB1661 + difference 4 5) sourceC1661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1661 + difference 5 4) (sourceB1661 + difference 4 5) sourceC1661) = raw24333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1661 sourceB1661 sourceC1661 difference raw24333; decide +kernel
    rw [ha]
    exact (canonical24333 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1661 sourceB1661 sourceC1661
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1661, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1408 : Integer.Sparse.reindex keyMap MixedData.row1408 = numericRow1408 := by decide +kernel

theorem numericCheck1408 (x : Master → ℝ) : Integer.Sparse.eval numericRow1408 x =
    (1 : ℝ) * reducedSource1408 x := by
  norm_num [numericRow1408, reducedSource1408, Integer.Sparse.eval, Sparse.eval, nodeValue1288, nodeValue2585, nodeValue2686, nodeValue2771, nodeValue2779, nodeValue4089]

theorem reindexCheck1415 : Integer.Sparse.reindex keyMap MixedData.row1415 = numericRow1415 := by decide +kernel

theorem numericCheck1415 (x : Master → ℝ) : Integer.Sparse.eval numericRow1415 x =
    (1 : ℝ) * reducedSource1415 x := by
  norm_num [numericRow1415, reducedSource1415, Integer.Sparse.eval, Sparse.eval, nodeValue1737, nodeValue1739, nodeValue1753, nodeValue3308, nodeValue4069]

theorem reindexCheck1416 : Integer.Sparse.reindex keyMap MixedData.row1416 = numericRow1416 := by decide +kernel

theorem numericCheck1416 (x : Master → ℝ) : Integer.Sparse.eval numericRow1416 x =
    (1 : ℝ) * reducedSource1416 x := by
  norm_num [numericRow1416, reducedSource1416, Integer.Sparse.eval, Sparse.eval, nodeValue1727, nodeValue3293, nodeValue3305, nodeValue3308, nodeValue3309, nodeValue4069]

theorem reindexCheck1422 : Integer.Sparse.reindex keyMap MixedData.row1422 = numericRow1422 := by decide +kernel

theorem numericCheck1422 (x : Master → ℝ) : Integer.Sparse.eval numericRow1422 x =
    (4 : ℝ) * reducedSource1422 x := by
  norm_num [numericRow1422, reducedSource1422, Integer.Sparse.eval, Sparse.eval, nodeValue4176, nodeValue4178, nodeValue4179, nodeValue4188, nodeValue4545, nodeValue4547, nodeValue4548, nodeValue4556, nodeValue4602, nodeValue4607, nodeValue4608, nodeValue4609, nodeValue4611, nodeValue4612, nodeValue4616, nodeValue4617, nodeValue4620, nodeValue5163, nodeValue5274, nodeValue5291, nodeValue5304]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1408 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1408 (mixedVector B) = 0 := by
  have h1288 : mixedVector B (Sum.inr 1288) = Sparse.eval nodeValue1288 (mixedVector B) := by
    change mixedMoment B node1288 node1288Labels = _
    exact sound1288 B hB hF
  have h2585 : mixedVector B (Sum.inr 2585) = Sparse.eval nodeValue2585 (mixedVector B) := by
    change mixedMoment B node2585 node2585Labels = _
    exact sound2585 B hB hF
  have h2686 : mixedVector B (Sum.inr 2686) = Sparse.eval nodeValue2686 (mixedVector B) := by
    change mixedMoment B node2686 node2686Labels = _
    exact sound2686 B hB hF
  have h2771 : mixedVector B (Sum.inr 2771) = Sparse.eval nodeValue2771 (mixedVector B) := by
    change mixedMoment B node2771 node2771Labels = _
    exact sound2771 B hB hF
  have h2779 : mixedVector B (Sum.inr 2779) = Sparse.eval nodeValue2779 (mixedVector B) := by
    change mixedMoment B node2779 node2779Labels = _
    exact sound2779 B hB hF
  have h4089 : mixedVector B (Sum.inr 4089) = Sparse.eval nodeValue4089 (mixedVector B) := by
    change mixedMoment B node4089 node4089Labels = _
    exact sound4089 B hB hF
  simpa only [sourceForm1647, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1288, h2585, h2686, h2771, h2779, h4089, reducedSource1408] using sourceEq1647 B hB

theorem rowSound1408 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1408 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1408, numericCheck1408, reducedZero1408 B hB hF, mul_zero]

theorem reducedZero1415 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1415 (mixedVector B) = 0 := by
  have h1737 : mixedVector B (Sum.inr 1737) = Sparse.eval nodeValue1737 (mixedVector B) := by
    change mixedMoment B node1737 node1737Labels = _
    exact sound1737 B hB hF
  have h1739 : mixedVector B (Sum.inr 1739) = Sparse.eval nodeValue1739 (mixedVector B) := by
    change mixedMoment B node1739 node1739Labels = _
    exact sound1739 B hB hF
  have h1753 : mixedVector B (Sum.inr 1753) = Sparse.eval nodeValue1753 (mixedVector B) := by
    change mixedMoment B node1753 node1753Labels = _
    exact sound1753 B hB hF
  have h3308 : mixedVector B (Sum.inr 3308) = Sparse.eval nodeValue3308 (mixedVector B) := by
    change mixedMoment B node3308 node3308Labels = _
    exact sound3308 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1654, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1737, h1739, h1753, h3308, h4069, reducedSource1415] using sourceEq1654 B hB

theorem rowSound1415 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1415 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1415, numericCheck1415, reducedZero1415 B hB hF, mul_zero]

theorem reducedZero1416 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1416 (mixedVector B) = 0 := by
  have h1727 : mixedVector B (Sum.inr 1727) = Sparse.eval nodeValue1727 (mixedVector B) := by
    change mixedMoment B node1727 node1727Labels = _
    exact sound1727 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h3308 : mixedVector B (Sum.inr 3308) = Sparse.eval nodeValue3308 (mixedVector B) := by
    change mixedMoment B node3308 node3308Labels = _
    exact sound3308 B hB hF
  have h3309 : mixedVector B (Sum.inr 3309) = Sparse.eval nodeValue3309 (mixedVector B) := by
    change mixedMoment B node3309 node3309Labels = _
    exact sound3309 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1655, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1727, h3293, h3305, h3308, h3309, h4069, reducedSource1416] using sourceEq1655 B hB

theorem rowSound1416 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1416 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1416, numericCheck1416, reducedZero1416 B hB hF, mul_zero]

theorem reducedZero1422 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1422 (mixedVector B) = 0 := by
  have h4176 : mixedVector B (Sum.inr 4176) = Sparse.eval nodeValue4176 (mixedVector B) := by
    change mixedMoment B node4176 node4176Labels = _
    exact sound4176 B hB hF
  have h4178 : mixedVector B (Sum.inr 4178) = Sparse.eval nodeValue4178 (mixedVector B) := by
    change mixedMoment B node4178 node4178Labels = _
    exact sound4178 B hB hF
  have h4179 : mixedVector B (Sum.inr 4179) = Sparse.eval nodeValue4179 (mixedVector B) := by
    change mixedMoment B node4179 node4179Labels = _
    exact sound4179 B hB hF
  have h4188 : mixedVector B (Sum.inr 4188) = Sparse.eval nodeValue4188 (mixedVector B) := by
    change mixedMoment B node4188 node4188Labels = _
    exact sound4188 B hB hF
  have h4545 : mixedVector B (Sum.inr 4545) = Sparse.eval nodeValue4545 (mixedVector B) := by
    change mixedMoment B node4545 node4545Labels = _
    exact sound4545 B hB hF
  have h4547 : mixedVector B (Sum.inr 4547) = Sparse.eval nodeValue4547 (mixedVector B) := by
    change mixedMoment B node4547 node4547Labels = _
    exact sound4547 B hB hF
  have h4548 : mixedVector B (Sum.inr 4548) = Sparse.eval nodeValue4548 (mixedVector B) := by
    change mixedMoment B node4548 node4548Labels = _
    exact sound4548 B hB hF
  have h4556 : mixedVector B (Sum.inr 4556) = Sparse.eval nodeValue4556 (mixedVector B) := by
    change mixedMoment B node4556 node4556Labels = _
    exact sound4556 B hB hF
  have h4602 : mixedVector B (Sum.inr 4602) = Sparse.eval nodeValue4602 (mixedVector B) := by
    change mixedMoment B node4602 node4602Labels = _
    exact sound4602 B hB hF
  have h4607 : mixedVector B (Sum.inr 4607) = Sparse.eval nodeValue4607 (mixedVector B) := by
    change mixedMoment B node4607 node4607Labels = _
    exact sound4607 B hB hF
  have h4608 : mixedVector B (Sum.inr 4608) = Sparse.eval nodeValue4608 (mixedVector B) := by
    change mixedMoment B node4608 node4608Labels = _
    exact sound4608 B hB hF
  have h4609 : mixedVector B (Sum.inr 4609) = Sparse.eval nodeValue4609 (mixedVector B) := by
    change mixedMoment B node4609 node4609Labels = _
    exact sound4609 B hB hF
  have h4611 : mixedVector B (Sum.inr 4611) = Sparse.eval nodeValue4611 (mixedVector B) := by
    change mixedMoment B node4611 node4611Labels = _
    exact sound4611 B hB hF
  have h4612 : mixedVector B (Sum.inr 4612) = Sparse.eval nodeValue4612 (mixedVector B) := by
    change mixedMoment B node4612 node4612Labels = _
    exact sound4612 B hB hF
  have h4616 : mixedVector B (Sum.inr 4616) = Sparse.eval nodeValue4616 (mixedVector B) := by
    change mixedMoment B node4616 node4616Labels = _
    exact sound4616 B hB hF
  have h4617 : mixedVector B (Sum.inr 4617) = Sparse.eval nodeValue4617 (mixedVector B) := by
    change mixedMoment B node4617 node4617Labels = _
    exact sound4617 B hB hF
  have h4620 : mixedVector B (Sum.inr 4620) = Sparse.eval nodeValue4620 (mixedVector B) := by
    change mixedMoment B node4620 node4620Labels = _
    exact sound4620 B hB hF
  have h5163 : mixedVector B (Sum.inr 5163) = Sparse.eval nodeValue5163 (mixedVector B) := by
    change mixedMoment B node5163 node5163Labels = _
    exact sound5163 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  have h5291 : mixedVector B (Sum.inr 5291) = Sparse.eval nodeValue5291 (mixedVector B) := by
    change mixedMoment B node5291 node5291Labels = _
    exact sound5291 B hB hF
  have h5304 : mixedVector B (Sum.inr 5304) = Sparse.eval nodeValue5304 (mixedVector B) := by
    change mixedMoment B node5304 node5304Labels = _
    exact sound5304 B hB hF
  simpa only [sourceForm1661, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4176, h4178, h4179, h4188, h4545, h4547, h4548, h4556, h4602, h4607, h4608, h4609, h4611, h4612, h4616, h4617, h4620, h5163, h5274, h5291, h5304, reducedSource1422] using sourceEq1661 B hB

theorem rowSound1422 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1422 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1422, numericCheck1422, reducedZero1422 B hB hF, mul_zero]

theorem sourceRowsAt1408 : MixedData.sourceRows (1408 : Fin 2425) =
    MixedData.row1408 := by decide +kernel

theorem sourceRowsAt1409 : MixedData.sourceRows (1409 : Fin 2425) =
    MixedData.row1409 := by decide +kernel

theorem sourceRowsAt1410 : MixedData.sourceRows (1410 : Fin 2425) =
    MixedData.row1410 := by decide +kernel

theorem sourceRowsAt1411 : MixedData.sourceRows (1411 : Fin 2425) =
    MixedData.row1411 := by decide +kernel

theorem sourceRowsAt1412 : MixedData.sourceRows (1412 : Fin 2425) =
    MixedData.row1412 := by decide +kernel

theorem sourceRowsAt1413 : MixedData.sourceRows (1413 : Fin 2425) =
    MixedData.row1413 := by decide +kernel

theorem sourceRowsAt1414 : MixedData.sourceRows (1414 : Fin 2425) =
    MixedData.row1414 := by decide +kernel

theorem sourceRowsAt1415 : MixedData.sourceRows (1415 : Fin 2425) =
    MixedData.row1415 := by decide +kernel

theorem sourceRowsAt1416 : MixedData.sourceRows (1416 : Fin 2425) =
    MixedData.row1416 := by decide +kernel

theorem sourceRowsAt1417 : MixedData.sourceRows (1417 : Fin 2425) =
    MixedData.row1417 := by decide +kernel

theorem sourceRowsAt1418 : MixedData.sourceRows (1418 : Fin 2425) =
    MixedData.row1418 := by decide +kernel

theorem sourceRowsAt1419 : MixedData.sourceRows (1419 : Fin 2425) =
    MixedData.row1419 := by decide +kernel

theorem sourceRowsAt1420 : MixedData.sourceRows (1420 : Fin 2425) =
    MixedData.row1420 := by decide +kernel

theorem sourceRowsAt1421 : MixedData.sourceRows (1421 : Fin 2425) =
    MixedData.row1421 := by decide +kernel

theorem sourceRowsAt1422 : MixedData.sourceRows (1422 : Fin 2425) =
    MixedData.row1422 := by decide +kernel

theorem sourceRowsAt1423 : MixedData.sourceRows (1423 : Fin 2425) =
    MixedData.row1423 := by decide +kernel

theorem chunkSound88_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 88) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1408 ∨ k.val = 1409 ∨ k.val = 1410 ∨ k.val = 1411 ∨ k.val = 1412 ∨ k.val = 1413 ∨ k.val = 1414 ∨ k.val = 1415 ∨ k.val = 1416 ∨ k.val = 1417 ∨ k.val = 1418 ∨ k.val = 1419 ∨ k.val = 1420 ∨ k.val = 1421 ∨ k.val = 1422 ∨ k.val = 1423 := by omega
  rcases heq with h1408 | h1409 | h1410 | h1411 | h1412 | h1413 | h1414 | h1415 | h1416 | h1417 | h1418 | h1419 | h1420 | h1421 | h1422 | h1423
  · have he : k = (1408 : Fin 2425) := Fin.ext h1408
    subst k
    rw [sourceRowsAt1408]
    exact rowSound1408 B hB hF
  · have he : k = (1409 : Fin 2425) := Fin.ext h1409
    subst k
    rw [sourceRowsAt1409]
    exact rowSound1409_e B hB hF
  · have he : k = (1410 : Fin 2425) := Fin.ext h1410
    subst k
    rw [sourceRowsAt1410]
    exact rowSound1410_e B hB hF
  · have he : k = (1411 : Fin 2425) := Fin.ext h1411
    subst k
    rw [sourceRowsAt1411]
    exact rowSound1411_e B hB hF
  · have he : k = (1412 : Fin 2425) := Fin.ext h1412
    subst k
    rw [sourceRowsAt1412]
    exact rowSound1412_e B hB hF
  · have he : k = (1413 : Fin 2425) := Fin.ext h1413
    subst k
    rw [sourceRowsAt1413]
    exact rowSound1413_e B hB hF
  · have he : k = (1414 : Fin 2425) := Fin.ext h1414
    subst k
    rw [sourceRowsAt1414]
    exact rowSound1414_e B hB hF
  · have he : k = (1415 : Fin 2425) := Fin.ext h1415
    subst k
    rw [sourceRowsAt1415]
    exact rowSound1415 B hB hF
  · have he : k = (1416 : Fin 2425) := Fin.ext h1416
    subst k
    rw [sourceRowsAt1416]
    exact rowSound1416 B hB hF
  · have he : k = (1417 : Fin 2425) := Fin.ext h1417
    subst k
    rw [sourceRowsAt1417]
    exact rowSound1417_e B hB hF
  · have he : k = (1418 : Fin 2425) := Fin.ext h1418
    subst k
    rw [sourceRowsAt1418]
    exact rowSound1418_e B hB hF
  · have he : k = (1419 : Fin 2425) := Fin.ext h1419
    subst k
    rw [sourceRowsAt1419]
    exact rowSound1419_e B hB hF
  · have he : k = (1420 : Fin 2425) := Fin.ext h1420
    subst k
    rw [sourceRowsAt1420]
    exact rowSound1420_e B hB hF
  · have he : k = (1421 : Fin 2425) := Fin.ext h1421
    subst k
    rw [sourceRowsAt1421]
    exact rowSound1421_e B hB hF
  · have he : k = (1422 : Fin 2425) := Fin.ext h1422
    subst k
    rw [sourceRowsAt1422]
    exact rowSound1422 B hB hF
  · have he : k = (1423 : Fin 2425) := Fin.ext h1423
    subst k
    rw [sourceRowsAt1423]
    exact rowSound1423_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound88_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound88_e_oai
