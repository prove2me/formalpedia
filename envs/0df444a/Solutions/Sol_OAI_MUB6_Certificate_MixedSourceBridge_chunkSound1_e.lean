-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:35:14.622076+00:00
-- url     : https://prove2.me/submissions/8bc5d745-4df2-4dc5-8b36-1e3444dddb80

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E108
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E150
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E171
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5433_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5452_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5482_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5490_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5500_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_reducedZero18_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound16_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound17_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound19_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound20_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound21_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound22_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound23_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound24_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound28_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_SmallPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.EqualityPatterns

theorem pattern2_0 {B : Type*} (f : Fin 2 → B)
    (h10 : f 1 = f 0)
    : ∀ i j, family2.label 0 i = family2.label 0 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family2, label2, raw2, blocks2, eq_comm]

theorem pattern2_1 {B : Type*} (f : Fin 2 → B)
    (h10 : f 1 ≠ f 0)
    : ∀ i j, family2.label 1 i = family2.label 1 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family2, label2, raw2, blocks2, eq_comm]

theorem covers2 {B : Type*} (f : Fin 2 → B) :
    ∃ p, ∀ i j, (family2.label p i = family2.label p j ↔ f i = f j) := by
  classical
  by_cases h10 : f 1 = f 0
  ·
    refine ⟨0, ?_⟩
    apply pattern2_0 f; simp_all [eq_comm]
  ·
    refine ⟨1, ?_⟩
    apply pattern2_1 f; simp_all [eq_comm]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2484 raw2484Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw2484 raw2484Labels = mixedMoment B raw2484step0 raw2484step0Labels := by
      have ha : raw2484step0 = (fun i j => raw2484 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2484step0 raw2484; decide +kernel
      have hl : raw2484step0Labels = raw2484Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2484 raw2484Labels permutation152 permutation4
    mixedMoment B raw2484step0 raw2484step0Labels = mixedMoment B raw2484step1 raw2484step1Labels := by
      have ha : raw2484step1 = raw2484step0 := by apply Matrix.ext; unfold raw2484step1 raw2484step0; decide +kernel
      have hl : raw2484step0Labels = labelEmbedding7 ∘ raw2484step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2484step0 raw2484step0Labels raw2484step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

theorem canonical2485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2485 raw2485Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw2485 raw2485Labels = mixedMoment B raw2485step0 raw2485step0Labels := by
      have ha : raw2485step0 = (fun i j => raw2485 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2485step0 raw2485; decide +kernel
      have hl : raw2485step0Labels = raw2485Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2485 raw2485Labels permutation152 permutation4
    _ = mixedMoment B node3800 node3800Labels := by rfl

theorem canonical2486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2486 raw2486Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw2486 raw2486Labels = mixedMoment B raw2486step0 raw2486step0Labels := by
      have ha : raw2486step0 = (fun i j => raw2486 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2486step0 raw2486; decide +kernel
      have hl : raw2486step0Labels = raw2486Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2486 raw2486Labels permutation164 permutation6
    mixedMoment B raw2486step0 raw2486step0Labels = mixedMoment B raw2486step1 raw2486step1Labels := by
      have ha : raw2486step1 = -raw2486step0 := by apply Matrix.ext; change ∀ i j, raw2486step1 i j = -(raw2486step0 i j); unfold raw2486step1 raw2486step0; decide +kernel
      have hl : raw2486step1Labels = raw2486step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2486step1 raw2486step1Labels = mixedMoment B raw2486step2 raw2486step2Labels := by
      have ha : raw2486step2 = raw2486step1 := by apply Matrix.ext; unfold raw2486step2 raw2486step1; decide +kernel
      have hl : raw2486step1Labels = labelEmbedding1 ∘ raw2486step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2486step1 raw2486step1Labels raw2486step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3805 node3805Labels := by rfl

theorem canonical2511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2511 raw2511Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw2511 raw2511Labels = mixedMoment B raw2511step0 raw2511step0Labels := by
      have ha : raw2511step0 = (fun i j => raw2511 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2511step0 raw2511; decide +kernel
      have hl : raw2511step0Labels = raw2511Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2511 raw2511Labels permutation152 permutation4
    mixedMoment B raw2511step0 raw2511step0Labels = mixedMoment B raw2511step1 raw2511step1Labels := by
      have ha : raw2511step1 = raw2511step0 := by apply Matrix.ext; unfold raw2511step1 raw2511step0; decide +kernel
      have hl : raw2511step0Labels = labelEmbedding7 ∘ raw2511step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2511step0 raw2511step0Labels raw2511step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5423 node5423Labels := by rfl

theorem canonical2512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2512 raw2512Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw2512 raw2512Labels = mixedMoment B raw2512step0 raw2512step0Labels := by
      have ha : raw2512step0 = (fun i j => raw2512 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2512step0 raw2512; decide +kernel
      have hl : raw2512step0Labels = raw2512Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2512 raw2512Labels permutation152 permutation4
    _ = mixedMoment B node3837 node3837Labels := by rfl

theorem canonical2513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2513 raw2513Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw2513 raw2513Labels = mixedMoment B raw2513step0 raw2513step0Labels := by
      have ha : raw2513step0 = (fun i j => raw2513 (permutation662 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2513step0 raw2513; decide +kernel
      have hl : raw2513step0Labels = raw2513Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2513 raw2513Labels permutation662 permutation6
    mixedMoment B raw2513step0 raw2513step0Labels = mixedMoment B raw2513step1 raw2513step1Labels := by
      have ha : raw2513step1 = raw2513step0 := by apply Matrix.ext; unfold raw2513step1 raw2513step0; decide +kernel
      have hl : raw2513step0Labels = labelEmbedding1 ∘ raw2513step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2513step0 raw2513step0Labels raw2513step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3837 node3837Labels := by rfl

theorem canonical2514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2514 raw2514Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw2514 raw2514Labels = mixedMoment B raw2514step0 raw2514step0Labels := by
      have ha : raw2514step0 = (fun i j => raw2514 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2514step0 raw2514; decide +kernel
      have hl : raw2514step0Labels = raw2514Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2514 raw2514Labels permutation152 permutation4
    mixedMoment B raw2514step0 raw2514step0Labels = mixedMoment B raw2514step1 raw2514step1Labels := by
      have ha : raw2514step1 = raw2514step0 := by apply Matrix.ext; unfold raw2514step1 raw2514step0; decide +kernel
      have hl : raw2514step0Labels = labelEmbedding7 ∘ raw2514step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2514step0 raw2514step0Labels raw2514step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical2515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2515 raw2515Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw2515 raw2515Labels = mixedMoment B raw2515step0 raw2515step0Labels := by
      have ha : raw2515step0 = (fun i j => raw2515 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2515step0 raw2515; decide +kernel
      have hl : raw2515step0Labels = raw2515Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2515 raw2515Labels permutation152 permutation4
    _ = mixedMoment B node3838 node3838Labels := by rfl

theorem canonical2516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2516 raw2516Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw2516 raw2516Labels = mixedMoment B raw2516step0 raw2516step0Labels := by
      have ha : raw2516step0 = (fun i j => raw2516 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2516step0 raw2516; decide +kernel
      have hl : raw2516step0Labels = raw2516Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2516 raw2516Labels permutation176 permutation6
    mixedMoment B raw2516step0 raw2516step0Labels = mixedMoment B raw2516step1 raw2516step1Labels := by
      have ha : raw2516step1 = -raw2516step0 := by apply Matrix.ext; change ∀ i j, raw2516step1 i j = -(raw2516step0 i j); unfold raw2516step1 raw2516step0; decide +kernel
      have hl : raw2516step1Labels = raw2516step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2516step1 raw2516step1Labels = mixedMoment B raw2516step2 raw2516step2Labels := by
      have ha : raw2516step2 = raw2516step1 := by apply Matrix.ext; unfold raw2516step2 raw2516step1; decide +kernel
      have hl : raw2516step1Labels = labelEmbedding1 ∘ raw2516step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2516step1 raw2516step1Labels raw2516step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

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

theorem canonical2598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2598 raw2598Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw2598 raw2598Labels = mixedMoment B raw2598step0 raw2598step0Labels := by
      have ha : raw2598step0 = (fun i j => raw2598 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2598step0 raw2598; decide +kernel
      have hl : raw2598step0Labels = raw2598Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2598 raw2598Labels permutation152 permutation4
    mixedMoment B raw2598step0 raw2598step0Labels = mixedMoment B raw2598step1 raw2598step1Labels := by
      have ha : raw2598step1 = raw2598step0 := by apply Matrix.ext; unfold raw2598step1 raw2598step0; decide +kernel
      have hl : raw2598step0Labels = labelEmbedding7 ∘ raw2598step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2598step0 raw2598step0Labels raw2598step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

theorem canonical2599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2599 raw2599Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw2599 raw2599Labels = mixedMoment B raw2599step0 raw2599step0Labels := by
      have ha : raw2599step0 = (fun i j => raw2599 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2599step0 raw2599; decide +kernel
      have hl : raw2599step0Labels = raw2599Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2599 raw2599Labels permutation152 permutation4
    _ = mixedMoment B node3974 node3974Labels := by rfl

theorem canonical2600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2600 raw2600Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw2600 raw2600Labels = mixedMoment B raw2600step0 raw2600step0Labels := by
      have ha : raw2600step0 = (fun i j => raw2600 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2600step0 raw2600; decide +kernel
      have hl : raw2600step0Labels = raw2600Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2600 raw2600Labels permutation688 permutation6
    mixedMoment B raw2600step0 raw2600step0Labels = mixedMoment B raw2600step1 raw2600step1Labels := by
      have ha : raw2600step1 = raw2600step0 := by apply Matrix.ext; unfold raw2600step1 raw2600step0; decide +kernel
      have hl : raw2600step0Labels = labelEmbedding1 ∘ raw2600step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2600step0 raw2600step0Labels raw2600step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3974 node3974Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2909 raw2909Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw2909 raw2909Labels = mixedMoment B raw2909step0 raw2909step0Labels := by
      have hz : ∀ j, raw2909 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2909step0 = (fun i j => raw2909 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2909step0 raw2909; decide +kernel
      have hl : raw2909step0Labels = raw2909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2909 raw2909Labels permutation520 hz
    mixedMoment B raw2909step0 raw2909step0Labels = mixedMoment B raw2909step1 raw2909step1Labels := by
      have hz : ∀ j, raw2909step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2909step1 = (fun i j => raw2909step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2909step1 raw2909step0; decide +kernel
      have hl : raw2909step1Labels = raw2909step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2909step0 raw2909step0Labels permutation104 hz
    mixedMoment B raw2909step1 raw2909step1Labels = mixedMoment B raw2909step2 raw2909step2Labels := by
      have hz : ∀ j, raw2909step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2909step2 = (fun i j => raw2909step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2909step2 raw2909step1; decide +kernel
      have hl : raw2909step2Labels = raw2909step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2909step1 raw2909step1Labels permutation20 hz
    mixedMoment B raw2909step2 raw2909step2Labels = mixedMoment B raw2909step3 raw2909step3Labels := by
      have hz : ∀ i, raw2909step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2909step3 = (fun i j => raw2909step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2909step3 raw2909step2; decide +kernel
      have hl : raw2909step3Labels = (fun j => raw2909step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2909step2 raw2909step2Labels permutation6 hz
    mixedMoment B raw2909step3 raw2909step3Labels = mixedMoment B raw2909step4 raw2909step4Labels := by
      have ha : raw2909step4 = (fun i j => raw2909step3 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2909step4 raw2909step3; decide +kernel
      have hl : raw2909step4Labels = raw2909step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2909step3 raw2909step3Labels permutation6 permutation0
    mixedMoment B raw2909step4 raw2909step4Labels = mixedMoment B raw2909step5 raw2909step5Labels := by
      have ha : raw2909step5 = -raw2909step4 := by apply Matrix.ext; change ∀ i j, raw2909step5 i j = -(raw2909step4 i j); unfold raw2909step5 raw2909step4; decide +kernel
      have hl : raw2909step5Labels = raw2909step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4093 node4093Labels := by rfl

theorem canonical2913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2913 raw2913Labels = mixedMoment B node4097 node4097Labels := by
  calc
    mixedMoment B raw2913 raw2913Labels = mixedMoment B raw2913step0 raw2913step0Labels := by
      have hz : ∀ j, raw2913 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2913step0 = (fun i j => raw2913 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2913step0 raw2913; decide +kernel
      have hl : raw2913step0Labels = raw2913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2913 raw2913Labels permutation520 hz
    mixedMoment B raw2913step0 raw2913step0Labels = mixedMoment B raw2913step1 raw2913step1Labels := by
      have hz : ∀ j, raw2913step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2913step1 = (fun i j => raw2913step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2913step1 raw2913step0; decide +kernel
      have hl : raw2913step1Labels = raw2913step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2913step0 raw2913step0Labels permutation104 hz
    mixedMoment B raw2913step1 raw2913step1Labels = mixedMoment B raw2913step2 raw2913step2Labels := by
      have hz : ∀ j, raw2913step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2913step2 = (fun i j => raw2913step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2913step2 raw2913step1; decide +kernel
      have hl : raw2913step2Labels = raw2913step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2913step1 raw2913step1Labels permutation20 hz
    mixedMoment B raw2913step2 raw2913step2Labels = mixedMoment B raw2913step3 raw2913step3Labels := by
      have hz : ∀ j, raw2913step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw2913step3 = (fun i j => raw2913step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw2913step3 raw2913step2; decide +kernel
      have hl : raw2913step3Labels = raw2913step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2913step2 raw2913step2Labels permutation4 hz
    mixedMoment B raw2913step3 raw2913step3Labels = mixedMoment B raw2913step4 raw2913step4Labels := by
      have hz : ∀ i, raw2913step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2913step4 = (fun i j => raw2913step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2913step4 raw2913step3; decide +kernel
      have hl : raw2913step4Labels = (fun j => raw2913step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2913step3 raw2913step3Labels permutation6 hz
    _ = mixedMoment B node4097 node4097Labels := by rfl

theorem canonical2918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2918 raw2918Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw2918 raw2918Labels = mixedMoment B raw2918step0 raw2918step0Labels := by
      have hz : ∀ j, raw2918 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2918step0 = (fun i j => raw2918 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2918step0 raw2918; decide +kernel
      have hl : raw2918step0Labels = raw2918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2918 raw2918Labels permutation520 hz
    mixedMoment B raw2918step0 raw2918step0Labels = mixedMoment B raw2918step1 raw2918step1Labels := by
      have hz : ∀ j, raw2918step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2918step1 = (fun i j => raw2918step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2918step1 raw2918step0; decide +kernel
      have hl : raw2918step1Labels = raw2918step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2918step0 raw2918step0Labels permutation104 hz
    mixedMoment B raw2918step1 raw2918step1Labels = mixedMoment B raw2918step2 raw2918step2Labels := by
      have hz : ∀ j, raw2918step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2918step2 = (fun i j => raw2918step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2918step2 raw2918step1; decide +kernel
      have hl : raw2918step2Labels = raw2918step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2918step1 raw2918step1Labels permutation20 hz
    mixedMoment B raw2918step2 raw2918step2Labels = mixedMoment B raw2918step3 raw2918step3Labels := by
      have hz : ∀ i, raw2918step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2918step3 = (fun i j => raw2918step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2918step3 raw2918step2; decide +kernel
      have hl : raw2918step3Labels = (fun j => raw2918step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2918step2 raw2918step2Labels permutation6 hz
    _ = mixedMoment B node4093 node4093Labels := by rfl

theorem canonical2923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2923 raw2923Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw2923 raw2923Labels = mixedMoment B raw2923step0 raw2923step0Labels := by
      have hz : ∀ j, raw2923 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2923step0 = (fun i j => raw2923 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2923step0 raw2923; decide +kernel
      have hl : raw2923step0Labels = raw2923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2923 raw2923Labels permutation520 hz
    mixedMoment B raw2923step0 raw2923step0Labels = mixedMoment B raw2923step1 raw2923step1Labels := by
      have hz : ∀ j, raw2923step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2923step1 = (fun i j => raw2923step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2923step1 raw2923step0; decide +kernel
      have hl : raw2923step1Labels = raw2923step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2923step0 raw2923step0Labels permutation104 hz
    mixedMoment B raw2923step1 raw2923step1Labels = mixedMoment B raw2923step2 raw2923step2Labels := by
      have hz : ∀ j, raw2923step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2923step2 = (fun i j => raw2923step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2923step2 raw2923step1; decide +kernel
      have hl : raw2923step2Labels = raw2923step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2923step1 raw2923step1Labels permutation14 hz
    mixedMoment B raw2923step2 raw2923step2Labels = mixedMoment B raw2923step3 raw2923step3Labels := by
      have hz : ∀ i, raw2923step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2923step3 = (fun i j => raw2923step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2923step3 raw2923step2; decide +kernel
      have hl : raw2923step3Labels = (fun j => raw2923step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2923step2 raw2923step2Labels permutation6 hz
    _ = mixedMoment B node4093 node4093Labels := by rfl

theorem canonical2928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2928 raw2928Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw2928 raw2928Labels = mixedMoment B raw2928step0 raw2928step0Labels := by
      have hz : ∀ j, raw2928 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2928step0 = (fun i j => raw2928 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2928step0 raw2928; decide +kernel
      have hl : raw2928step0Labels = raw2928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2928 raw2928Labels permutation520 hz
    mixedMoment B raw2928step0 raw2928step0Labels = mixedMoment B raw2928step1 raw2928step1Labels := by
      have hz : ∀ j, raw2928step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2928step1 = (fun i j => raw2928step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2928step1 raw2928step0; decide +kernel
      have hl : raw2928step1Labels = raw2928step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2928step0 raw2928step0Labels permutation80 hz
    mixedMoment B raw2928step1 raw2928step1Labels = mixedMoment B raw2928step2 raw2928step2Labels := by
      have hz : ∀ j, raw2928step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2928step2 = (fun i j => raw2928step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2928step2 raw2928step1; decide +kernel
      have hl : raw2928step2Labels = raw2928step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2928step1 raw2928step1Labels permutation14 hz
    mixedMoment B raw2928step2 raw2928step2Labels = mixedMoment B raw2928step3 raw2928step3Labels := by
      have hz : ∀ i, raw2928step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2928step3 = (fun i j => raw2928step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2928step3 raw2928step2; decide +kernel
      have hl : raw2928step3Labels = (fun j => raw2928step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2928step2 raw2928step2Labels permutation6 hz
    _ = mixedMoment B node4093 node4093Labels := by rfl

theorem canonical2929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2929 raw2929Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2929 raw2929Labels = mixedMoment B raw2929step0 raw2929step0Labels := by
      have hz : ∀ j, raw2929 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2929step0 = (fun i j => raw2929 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2929step0 raw2929; decide +kernel
      have hl : raw2929step0Labels = raw2929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2929 raw2929Labels permutation434 hz
    mixedMoment B raw2929step0 raw2929step0Labels = mixedMoment B raw2929step1 raw2929step1Labels := by
      have hz : ∀ j, raw2929step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2929step1 = (fun i j => raw2929step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2929step1 raw2929step0; decide +kernel
      have hl : raw2929step1Labels = raw2929step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2929step0 raw2929step0Labels permutation80 hz
    mixedMoment B raw2929step1 raw2929step1Labels = mixedMoment B raw2929step2 raw2929step2Labels := by
      have hz : ∀ j, raw2929step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2929step2 = (fun i j => raw2929step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2929step2 raw2929step1; decide +kernel
      have hl : raw2929step2Labels = raw2929step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2929step1 raw2929step1Labels permutation14 hz
    mixedMoment B raw2929step2 raw2929step2Labels = mixedMoment B raw2929step3 raw2929step3Labels := by
      have hz : ∀ i, raw2929step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2929step3 = (fun i j => raw2929step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2929step3 raw2929step2; decide +kernel
      have hl : raw2929step3Labels = (fun j => raw2929step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2929step2 raw2929step2Labels permutation6 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical2930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2930 raw2930Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2930 raw2930Labels = mixedMoment B raw2930step0 raw2930step0Labels := by
      have hz : ∀ j, raw2930 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2930step0 = (fun i j => raw2930 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2930step0 raw2930; decide +kernel
      have hl : raw2930step0Labels = raw2930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2930 raw2930Labels permutation434 hz
    mixedMoment B raw2930step0 raw2930step0Labels = mixedMoment B raw2930step1 raw2930step1Labels := by
      have hz : ∀ j, raw2930step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2930step1 = (fun i j => raw2930step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2930step1 raw2930step0; decide +kernel
      have hl : raw2930step1Labels = raw2930step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2930step0 raw2930step0Labels permutation80 hz
    mixedMoment B raw2930step1 raw2930step1Labels = mixedMoment B raw2930step2 raw2930step2Labels := by
      have hz : ∀ i, raw2930step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2930step2 = (fun i j => raw2930step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2930step2 raw2930step1; decide +kernel
      have hl : raw2930step2Labels = (fun j => raw2930step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2930step1 raw2930step1Labels permutation6 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical2931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2931 raw2931Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2931 raw2931Labels = mixedMoment B raw2931step0 raw2931step0Labels := by
      have hz : ∀ j, raw2931 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2931step0 = (fun i j => raw2931 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2931step0 raw2931; decide +kernel
      have hl : raw2931step0Labels = raw2931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2931 raw2931Labels permutation434 hz
    mixedMoment B raw2931step0 raw2931step0Labels = mixedMoment B raw2931step1 raw2931step1Labels := by
      have hz : ∀ j, raw2931step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2931step1 = (fun i j => raw2931step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2931step1 raw2931step0; decide +kernel
      have hl : raw2931step1Labels = raw2931step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2931step0 raw2931step0Labels permutation56 hz
    mixedMoment B raw2931step1 raw2931step1Labels = mixedMoment B raw2931step2 raw2931step2Labels := by
      have hz : ∀ i, raw2931step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2931step2 = (fun i j => raw2931step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2931step2 raw2931step1; decide +kernel
      have hl : raw2931step2Labels = (fun j => raw2931step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2931step1 raw2931step1Labels permutation6 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical2932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2932 raw2932Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2932 raw2932Labels = mixedMoment B raw2932step0 raw2932step0Labels := by
      have hz : ∀ j, raw2932 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2932step0 = (fun i j => raw2932 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2932step0 raw2932; decide +kernel
      have hl : raw2932step0Labels = raw2932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2932 raw2932Labels permutation346 hz
    mixedMoment B raw2932step0 raw2932step0Labels = mixedMoment B raw2932step1 raw2932step1Labels := by
      have hz : ∀ j, raw2932step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2932step1 = (fun i j => raw2932step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2932step1 raw2932step0; decide +kernel
      have hl : raw2932step1Labels = raw2932step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2932step0 raw2932step0Labels permutation56 hz
    mixedMoment B raw2932step1 raw2932step1Labels = mixedMoment B raw2932step2 raw2932step2Labels := by
      have hz : ∀ i, raw2932step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2932step2 = (fun i j => raw2932step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2932step2 raw2932step1; decide +kernel
      have hl : raw2932step2Labels = (fun j => raw2932step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2932step1 raw2932step1Labels permutation6 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical2933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2933 raw2933Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw2933 raw2933Labels = mixedMoment B raw2933step0 raw2933step0Labels := by
      have hz : ∀ j, raw2933 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2933step0 = (fun i j => raw2933 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2933step0 raw2933; decide +kernel
      have hl : raw2933step0Labels = raw2933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2933 raw2933Labels permutation434 hz
    mixedMoment B raw2933step0 raw2933step0Labels = mixedMoment B raw2933step1 raw2933step1Labels := by
      have hz : ∀ j, raw2933step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2933step1 = (fun i j => raw2933step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2933step1 raw2933step0; decide +kernel
      have hl : raw2933step1Labels = raw2933step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2933step0 raw2933step0Labels permutation80 hz
    mixedMoment B raw2933step1 raw2933step1Labels = mixedMoment B raw2933step2 raw2933step2Labels := by
      have hz : ∀ j, raw2933step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2933step2 = (fun i j => raw2933step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2933step2 raw2933step1; decide +kernel
      have hl : raw2933step2Labels = raw2933step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2933step1 raw2933step1Labels permutation14 hz
    mixedMoment B raw2933step2 raw2933step2Labels = mixedMoment B raw2933step3 raw2933step3Labels := by
      have hz : ∀ i, raw2933step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2933step3 = (fun i j => raw2933step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2933step3 raw2933step2; decide +kernel
      have hl : raw2933step3Labels = (fun j => raw2933step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2933step2 raw2933step2Labels permutation6 hz
    _ = mixedMoment B node4093 node4093Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3319 raw3319Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw3319 raw3319Labels = mixedMoment B raw3319step0 raw3319step0Labels := by
      have hz : ∀ j, raw3319 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3319step0 = (fun i j => raw3319 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3319step0 raw3319; decide +kernel
      have hl : raw3319step0Labels = raw3319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3319 raw3319Labels permutation434 hz
    mixedMoment B raw3319step0 raw3319step0Labels = mixedMoment B raw3319step1 raw3319step1Labels := by
      have hz : ∀ j, raw3319step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3319step1 = (fun i j => raw3319step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3319step1 raw3319step0; decide +kernel
      have hl : raw3319step1Labels = raw3319step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3319step0 raw3319step0Labels permutation80 hz
    mixedMoment B raw3319step1 raw3319step1Labels = mixedMoment B raw3319step2 raw3319step2Labels := by
      have hz : ∀ i, raw3319step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3319step2 = (fun i j => raw3319step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3319step2 raw3319step1; decide +kernel
      have hl : raw3319step2Labels = (fun j => raw3319step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3319step1 raw3319step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

theorem canonical3320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3320 raw3320Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw3320 raw3320Labels = mixedMoment B raw3320step0 raw3320step0Labels := by
      have hz : ∀ j, raw3320 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3320step0 = (fun i j => raw3320 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3320step0 raw3320; decide +kernel
      have hl : raw3320step0Labels = raw3320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3320 raw3320Labels permutation434 hz
    mixedMoment B raw3320step0 raw3320step0Labels = mixedMoment B raw3320step1 raw3320step1Labels := by
      have hz : ∀ j, raw3320step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3320step1 = (fun i j => raw3320step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3320step1 raw3320step0; decide +kernel
      have hl : raw3320step1Labels = raw3320step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3320step0 raw3320step0Labels permutation56 hz
    mixedMoment B raw3320step1 raw3320step1Labels = mixedMoment B raw3320step2 raw3320step2Labels := by
      have hz : ∀ i, raw3320step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3320step2 = (fun i j => raw3320step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3320step2 raw3320step1; decide +kernel
      have hl : raw3320step2Labels = (fun j => raw3320step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3320step1 raw3320step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

theorem canonical3321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3321 raw3321Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw3321 raw3321Labels = mixedMoment B raw3321step0 raw3321step0Labels := by
      have hz : ∀ j, raw3321 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3321step0 = (fun i j => raw3321 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3321step0 raw3321; decide +kernel
      have hl : raw3321step0Labels = raw3321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3321 raw3321Labels permutation346 hz
    mixedMoment B raw3321step0 raw3321step0Labels = mixedMoment B raw3321step1 raw3321step1Labels := by
      have hz : ∀ j, raw3321step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3321step1 = (fun i j => raw3321step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3321step1 raw3321step0; decide +kernel
      have hl : raw3321step1Labels = raw3321step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3321step0 raw3321step0Labels permutation56 hz
    mixedMoment B raw3321step1 raw3321step1Labels = mixedMoment B raw3321step2 raw3321step2Labels := by
      have hz : ∀ i, raw3321step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3321step2 = (fun i j => raw3321step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3321step2 raw3321step1; decide +kernel
      have hl : raw3321step2Labels = (fun j => raw3321step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3321step1 raw3321step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

theorem canonical3322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3322 raw3322Labels = mixedMoment B node4097 node4097Labels := by
  calc
    mixedMoment B raw3322 raw3322Labels = mixedMoment B raw3322step0 raw3322step0Labels := by
      have hz : ∀ j, raw3322 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3322step0 = (fun i j => raw3322 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3322step0 raw3322; decide +kernel
      have hl : raw3322step0Labels = raw3322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3322 raw3322Labels permutation590 hz
    mixedMoment B raw3322step0 raw3322step0Labels = mixedMoment B raw3322step1 raw3322step1Labels := by
      have hz : ∀ j, raw3322step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3322step1 = (fun i j => raw3322step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3322step1 raw3322step0; decide +kernel
      have hl : raw3322step1Labels = raw3322step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3322step0 raw3322step0Labels permutation104 hz
    mixedMoment B raw3322step1 raw3322step1Labels = mixedMoment B raw3322step2 raw3322step2Labels := by
      have hz : ∀ j, raw3322step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3322step2 = (fun i j => raw3322step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3322step2 raw3322step1; decide +kernel
      have hl : raw3322step2Labels = raw3322step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3322step1 raw3322step1Labels permutation20 hz
    mixedMoment B raw3322step2 raw3322step2Labels = mixedMoment B raw3322step3 raw3322step3Labels := by
      have hz : ∀ j, raw3322step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw3322step3 = (fun i j => raw3322step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw3322step3 raw3322step2; decide +kernel
      have hl : raw3322step3Labels = raw3322step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3322step2 raw3322step2Labels permutation4 hz
    mixedMoment B raw3322step3 raw3322step3Labels = mixedMoment B raw3322step4 raw3322step4Labels := by
      have hz : ∀ i, raw3322step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3322step4 = (fun i j => raw3322step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3322step4 raw3322step3; decide +kernel
      have hl : raw3322step4Labels = (fun j => raw3322step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3322step3 raw3322step3Labels permutation6 hz
    _ = mixedMoment B node4097 node4097Labels := by rfl

theorem canonical3323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3323 raw3323Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw3323 raw3323Labels = mixedMoment B raw3323step0 raw3323step0Labels := by
      have hz : ∀ j, raw3323 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3323step0 = (fun i j => raw3323 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3323step0 raw3323; decide +kernel
      have hl : raw3323step0Labels = raw3323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3323 raw3323Labels permutation434 hz
    mixedMoment B raw3323step0 raw3323step0Labels = mixedMoment B raw3323step1 raw3323step1Labels := by
      have hz : ∀ j, raw3323step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3323step1 = (fun i j => raw3323step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3323step1 raw3323step0; decide +kernel
      have hl : raw3323step1Labels = raw3323step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3323step0 raw3323step0Labels permutation80 hz
    mixedMoment B raw3323step1 raw3323step1Labels = mixedMoment B raw3323step2 raw3323step2Labels := by
      have hz : ∀ i, raw3323step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3323step2 = (fun i j => raw3323step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3323step2 raw3323step1; decide +kernel
      have hl : raw3323step2Labels = (fun j => raw3323step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3323step1 raw3323step1Labels permutation6 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical3324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3324 raw3324Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3324 raw3324Labels = mixedMoment B raw3324step0 raw3324step0Labels := by
      have hz : ∀ j, raw3324 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3324step0 = (fun i j => raw3324 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3324step0 raw3324; decide +kernel
      have hl : raw3324step0Labels = raw3324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3324 raw3324Labels permutation434 hz
    mixedMoment B raw3324step0 raw3324step0Labels = mixedMoment B raw3324step1 raw3324step1Labels := by
      have hz : ∀ i, raw3324step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3324step1 = (fun i j => raw3324step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3324step1 raw3324step0; decide +kernel
      have hl : raw3324step1Labels = (fun j => raw3324step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3324step0 raw3324step0Labels permutation6 hz
    mixedMoment B raw3324step1 raw3324step1Labels = mixedMoment B raw3324step2 raw3324step2Labels := by
      have ha : raw3324step2 = (fun i j => raw3324step1 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3324step2 raw3324step1; decide +kernel
      have hl : raw3324step2Labels = raw3324step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3324step1 raw3324step1Labels permutation38 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical3325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3325 raw3325Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3325 raw3325Labels = mixedMoment B raw3325step0 raw3325step0Labels := by
      have hz : ∀ j, raw3325 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3325step0 = (fun i j => raw3325 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3325step0 raw3325; decide +kernel
      have hl : raw3325step0Labels = raw3325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3325 raw3325Labels permutation346 hz
    mixedMoment B raw3325step0 raw3325step0Labels = mixedMoment B raw3325step1 raw3325step1Labels := by
      have hz : ∀ i, raw3325step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3325step1 = (fun i j => raw3325step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3325step1 raw3325step0; decide +kernel
      have hl : raw3325step1Labels = (fun j => raw3325step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3325step0 raw3325step0Labels permutation6 hz
    mixedMoment B raw3325step1 raw3325step1Labels = mixedMoment B raw3325step2 raw3325step2Labels := by
      have ha : raw3325step2 = (fun i j => raw3325step1 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3325step2 raw3325step1; decide +kernel
      have hl : raw3325step2Labels = raw3325step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3325step1 raw3325step1Labels permutation38 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical3326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3326 raw3326Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw3326 raw3326Labels = mixedMoment B raw3326step0 raw3326step0Labels := by
      have hz : ∀ j, raw3326 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3326step0 = (fun i j => raw3326 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3326step0 raw3326; decide +kernel
      have hl : raw3326step0Labels = raw3326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3326 raw3326Labels permutation590 hz
    mixedMoment B raw3326step0 raw3326step0Labels = mixedMoment B raw3326step1 raw3326step1Labels := by
      have hz : ∀ j, raw3326step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3326step1 = (fun i j => raw3326step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3326step1 raw3326step0; decide +kernel
      have hl : raw3326step1Labels = raw3326step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3326step0 raw3326step0Labels permutation104 hz
    mixedMoment B raw3326step1 raw3326step1Labels = mixedMoment B raw3326step2 raw3326step2Labels := by
      have hz : ∀ j, raw3326step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3326step2 = (fun i j => raw3326step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3326step2 raw3326step1; decide +kernel
      have hl : raw3326step2Labels = raw3326step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3326step1 raw3326step1Labels permutation20 hz
    mixedMoment B raw3326step2 raw3326step2Labels = mixedMoment B raw3326step3 raw3326step3Labels := by
      have hz : ∀ i, raw3326step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3326step3 = (fun i j => raw3326step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3326step3 raw3326step2; decide +kernel
      have hl : raw3326step3Labels = (fun j => raw3326step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3326step2 raw3326step2Labels permutation6 hz
    _ = mixedMoment B node4093 node4093Labels := by rfl

theorem canonical3327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3327 raw3327Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw3327 raw3327Labels = mixedMoment B raw3327step0 raw3327step0Labels := by
      have hz : ∀ j, raw3327 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3327step0 = (fun i j => raw3327 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3327step0 raw3327; decide +kernel
      have hl : raw3327step0Labels = raw3327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3327 raw3327Labels permutation434 hz
    mixedMoment B raw3327step0 raw3327step0Labels = mixedMoment B raw3327step1 raw3327step1Labels := by
      have hz : ∀ j, raw3327step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3327step1 = (fun i j => raw3327step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3327step1 raw3327step0; decide +kernel
      have hl : raw3327step1Labels = raw3327step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3327step0 raw3327step0Labels permutation56 hz
    mixedMoment B raw3327step1 raw3327step1Labels = mixedMoment B raw3327step2 raw3327step2Labels := by
      have hz : ∀ i, raw3327step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3327step2 = (fun i j => raw3327step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3327step2 raw3327step1; decide +kernel
      have hl : raw3327step2Labels = (fun j => raw3327step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3327step1 raw3327step1Labels permutation6 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3328 raw3328Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3328 raw3328Labels = mixedMoment B raw3328step0 raw3328step0Labels := by
      have hz : ∀ j, raw3328 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3328step0 = (fun i j => raw3328 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3328step0 raw3328; decide +kernel
      have hl : raw3328step0Labels = raw3328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3328 raw3328Labels permutation434 hz
    mixedMoment B raw3328step0 raw3328step0Labels = mixedMoment B raw3328step1 raw3328step1Labels := by
      have hz : ∀ i, raw3328step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3328step1 = (fun i j => raw3328step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3328step1 raw3328step0; decide +kernel
      have hl : raw3328step1Labels = (fun j => raw3328step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3328step0 raw3328step0Labels permutation6 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical3329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3329 raw3329Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3329 raw3329Labels = mixedMoment B raw3329step0 raw3329step0Labels := by
      have hz : ∀ j, raw3329 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3329step0 = (fun i j => raw3329 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3329step0 raw3329; decide +kernel
      have hl : raw3329step0Labels = raw3329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3329 raw3329Labels permutation265 hz
    mixedMoment B raw3329step0 raw3329step0Labels = mixedMoment B raw3329step1 raw3329step1Labels := by
      have hz : ∀ i, raw3329step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3329step1 = (fun i j => raw3329step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3329step1 raw3329step0; decide +kernel
      have hl : raw3329step1Labels = (fun j => raw3329step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3329step0 raw3329step0Labels permutation6 hz
    mixedMoment B raw3329step1 raw3329step1Labels = mixedMoment B raw3329step2 raw3329step2Labels := by
      have ha : raw3329step2 = (fun i j => raw3329step1 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3329step2 raw3329step1; decide +kernel
      have hl : raw3329step2Labels = raw3329step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3329step1 raw3329step1Labels permutation38 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical3330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3330 raw3330Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw3330 raw3330Labels = mixedMoment B raw3330step0 raw3330step0Labels := by
      have hz : ∀ j, raw3330 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3330step0 = (fun i j => raw3330 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3330step0 raw3330; decide +kernel
      have hl : raw3330step0Labels = raw3330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3330 raw3330Labels permutation590 hz
    mixedMoment B raw3330step0 raw3330step0Labels = mixedMoment B raw3330step1 raw3330step1Labels := by
      have hz : ∀ j, raw3330step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3330step1 = (fun i j => raw3330step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3330step1 raw3330step0; decide +kernel
      have hl : raw3330step1Labels = raw3330step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3330step0 raw3330step0Labels permutation104 hz
    mixedMoment B raw3330step1 raw3330step1Labels = mixedMoment B raw3330step2 raw3330step2Labels := by
      have hz : ∀ j, raw3330step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3330step2 = (fun i j => raw3330step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3330step2 raw3330step1; decide +kernel
      have hl : raw3330step2Labels = raw3330step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3330step1 raw3330step1Labels permutation14 hz
    mixedMoment B raw3330step2 raw3330step2Labels = mixedMoment B raw3330step3 raw3330step3Labels := by
      have hz : ∀ i, raw3330step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3330step3 = (fun i j => raw3330step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3330step3 raw3330step2; decide +kernel
      have hl : raw3330step3Labels = (fun j => raw3330step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3330step2 raw3330step2Labels permutation6 hz
    _ = mixedMoment B node4093 node4093Labels := by rfl

theorem canonical3331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3331 raw3331Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw3331 raw3331Labels = mixedMoment B raw3331step0 raw3331step0Labels := by
      have hz : ∀ j, raw3331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3331step0 = (fun i j => raw3331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3331step0 raw3331; decide +kernel
      have hl : raw3331step0Labels = raw3331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3331 raw3331Labels permutation346 hz
    mixedMoment B raw3331step0 raw3331step0Labels = mixedMoment B raw3331step1 raw3331step1Labels := by
      have hz : ∀ j, raw3331step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3331step1 = (fun i j => raw3331step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3331step1 raw3331step0; decide +kernel
      have hl : raw3331step1Labels = raw3331step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3331step0 raw3331step0Labels permutation56 hz
    mixedMoment B raw3331step1 raw3331step1Labels = mixedMoment B raw3331step2 raw3331step2Labels := by
      have hz : ∀ i, raw3331step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3331step2 = (fun i j => raw3331step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3331step2 raw3331step1; decide +kernel
      have hl : raw3331step2Labels = (fun j => raw3331step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3331step1 raw3331step1Labels permutation6 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical3332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3332 raw3332Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3332 raw3332Labels = mixedMoment B raw3332step0 raw3332step0Labels := by
      have hz : ∀ j, raw3332 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3332step0 = (fun i j => raw3332 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3332step0 raw3332; decide +kernel
      have hl : raw3332step0Labels = raw3332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3332 raw3332Labels permutation346 hz
    mixedMoment B raw3332step0 raw3332step0Labels = mixedMoment B raw3332step1 raw3332step1Labels := by
      have hz : ∀ i, raw3332step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3332step1 = (fun i j => raw3332step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3332step1 raw3332step0; decide +kernel
      have hl : raw3332step1Labels = (fun j => raw3332step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3332step0 raw3332step0Labels permutation6 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical3333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3333 raw3333Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3333 raw3333Labels = mixedMoment B raw3333step0 raw3333step0Labels := by
      have hz : ∀ j, raw3333 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3333step0 = (fun i j => raw3333 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3333step0 raw3333; decide +kernel
      have hl : raw3333step0Labels = raw3333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3333 raw3333Labels permutation265 hz
    mixedMoment B raw3333step0 raw3333step0Labels = mixedMoment B raw3333step1 raw3333step1Labels := by
      have hz : ∀ i, raw3333step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3333step1 = (fun i j => raw3333step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3333step1 raw3333step0; decide +kernel
      have hl : raw3333step1Labels = (fun j => raw3333step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3333step0 raw3333step0Labels permutation6 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical3334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3334 raw3334Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw3334 raw3334Labels = mixedMoment B raw3334step0 raw3334step0Labels := by
      have hz : ∀ j, raw3334 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3334step0 = (fun i j => raw3334 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3334step0 raw3334; decide +kernel
      have hl : raw3334step0Labels = raw3334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3334 raw3334Labels permutation590 hz
    mixedMoment B raw3334step0 raw3334step0Labels = mixedMoment B raw3334step1 raw3334step1Labels := by
      have hz : ∀ j, raw3334step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3334step1 = (fun i j => raw3334step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3334step1 raw3334step0; decide +kernel
      have hl : raw3334step1Labels = raw3334step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3334step0 raw3334step0Labels permutation80 hz
    mixedMoment B raw3334step1 raw3334step1Labels = mixedMoment B raw3334step2 raw3334step2Labels := by
      have hz : ∀ j, raw3334step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3334step2 = (fun i j => raw3334step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3334step2 raw3334step1; decide +kernel
      have hl : raw3334step2Labels = raw3334step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3334step1 raw3334step1Labels permutation14 hz
    mixedMoment B raw3334step2 raw3334step2Labels = mixedMoment B raw3334step3 raw3334step3Labels := by
      have hz : ∀ i, raw3334step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3334step3 = (fun i j => raw3334step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3334step3 raw3334step2; decide +kernel
      have hl : raw3334step3Labels = (fun j => raw3334step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3334step2 raw3334step2Labels permutation6 hz
    _ = mixedMoment B node4093 node4093Labels := by rfl

theorem canonical3335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3335 raw3335Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw3335 raw3335Labels = mixedMoment B raw3335step0 raw3335step0Labels := by
      have hz : ∀ j, raw3335 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3335step0 = (fun i j => raw3335 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3335step0 raw3335; decide +kernel
      have hl : raw3335step0Labels = raw3335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3335 raw3335Labels permutation434 hz
    mixedMoment B raw3335step0 raw3335step0Labels = mixedMoment B raw3335step1 raw3335step1Labels := by
      have hz : ∀ j, raw3335step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3335step1 = (fun i j => raw3335step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3335step1 raw3335step0; decide +kernel
      have hl : raw3335step1Labels = raw3335step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3335step0 raw3335step0Labels permutation80 hz
    mixedMoment B raw3335step1 raw3335step1Labels = mixedMoment B raw3335step2 raw3335step2Labels := by
      have hz : ∀ j, raw3335step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3335step2 = (fun i j => raw3335step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3335step2 raw3335step1; decide +kernel
      have hl : raw3335step2Labels = raw3335step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3335step1 raw3335step1Labels permutation14 hz
    mixedMoment B raw3335step2 raw3335step2Labels = mixedMoment B raw3335step3 raw3335step3Labels := by
      have hz : ∀ i, raw3335step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3335step3 = (fun i j => raw3335step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3335step3 raw3335step2; decide +kernel
      have hl : raw3335step3Labels = (fun j => raw3335step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3335step2 raw3335step2Labels permutation6 hz
    mixedMoment B raw3335step3 raw3335step3Labels = mixedMoment B raw3335step4 raw3335step4Labels := by
      have ha : raw3335step4 = (fun i j => raw3335step3 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3335step4 raw3335step3; decide +kernel
      have hl : raw3335step4Labels = raw3335step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3335step3 raw3335step3Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical3336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3336 raw3336Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw3336 raw3336Labels = mixedMoment B raw3336step0 raw3336step0Labels := by
      have hz : ∀ j, raw3336 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3336step0 = (fun i j => raw3336 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3336step0 raw3336; decide +kernel
      have hl : raw3336step0Labels = raw3336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3336 raw3336Labels permutation434 hz
    mixedMoment B raw3336step0 raw3336step0Labels = mixedMoment B raw3336step1 raw3336step1Labels := by
      have hz : ∀ j, raw3336step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3336step1 = (fun i j => raw3336step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3336step1 raw3336step0; decide +kernel
      have hl : raw3336step1Labels = raw3336step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3336step0 raw3336step0Labels permutation80 hz
    mixedMoment B raw3336step1 raw3336step1Labels = mixedMoment B raw3336step2 raw3336step2Labels := by
      have hz : ∀ i, raw3336step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3336step2 = (fun i j => raw3336step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3336step2 raw3336step1; decide +kernel
      have hl : raw3336step2Labels = (fun j => raw3336step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3336step1 raw3336step1Labels permutation6 hz
    mixedMoment B raw3336step2 raw3336step2Labels = mixedMoment B raw3336step3 raw3336step3Labels := by
      have ha : raw3336step3 = (fun i j => raw3336step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3336step3 raw3336step2; decide +kernel
      have hl : raw3336step3Labels = raw3336step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3336step2 raw3336step2Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical3337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3337 raw3337Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw3337 raw3337Labels = mixedMoment B raw3337step0 raw3337step0Labels := by
      have hz : ∀ j, raw3337 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3337step0 = (fun i j => raw3337 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3337step0 raw3337; decide +kernel
      have hl : raw3337step0Labels = raw3337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3337 raw3337Labels permutation434 hz
    mixedMoment B raw3337step0 raw3337step0Labels = mixedMoment B raw3337step1 raw3337step1Labels := by
      have hz : ∀ j, raw3337step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3337step1 = (fun i j => raw3337step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3337step1 raw3337step0; decide +kernel
      have hl : raw3337step1Labels = raw3337step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3337step0 raw3337step0Labels permutation56 hz
    mixedMoment B raw3337step1 raw3337step1Labels = mixedMoment B raw3337step2 raw3337step2Labels := by
      have hz : ∀ i, raw3337step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3337step2 = (fun i j => raw3337step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3337step2 raw3337step1; decide +kernel
      have hl : raw3337step2Labels = (fun j => raw3337step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3337step1 raw3337step1Labels permutation6 hz
    mixedMoment B raw3337step2 raw3337step2Labels = mixedMoment B raw3337step3 raw3337step3Labels := by
      have ha : raw3337step3 = (fun i j => raw3337step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3337step3 raw3337step2; decide +kernel
      have hl : raw3337step3Labels = raw3337step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3337step2 raw3337step2Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical3338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3338 raw3338Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw3338 raw3338Labels = mixedMoment B raw3338step0 raw3338step0Labels := by
      have hz : ∀ j, raw3338 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3338step0 = (fun i j => raw3338 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3338step0 raw3338; decide +kernel
      have hl : raw3338step0Labels = raw3338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3338 raw3338Labels permutation346 hz
    mixedMoment B raw3338step0 raw3338step0Labels = mixedMoment B raw3338step1 raw3338step1Labels := by
      have hz : ∀ j, raw3338step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3338step1 = (fun i j => raw3338step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3338step1 raw3338step0; decide +kernel
      have hl : raw3338step1Labels = raw3338step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3338step0 raw3338step0Labels permutation56 hz
    mixedMoment B raw3338step1 raw3338step1Labels = mixedMoment B raw3338step2 raw3338step2Labels := by
      have hz : ∀ i, raw3338step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3338step2 = (fun i j => raw3338step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3338step2 raw3338step1; decide +kernel
      have hl : raw3338step2Labels = (fun j => raw3338step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3338step1 raw3338step1Labels permutation6 hz
    mixedMoment B raw3338step2 raw3338step2Labels = mixedMoment B raw3338step3 raw3338step3Labels := by
      have ha : raw3338step3 = (fun i j => raw3338step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3338step3 raw3338step2; decide +kernel
      have hl : raw3338step3Labels = raw3338step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3338step2 raw3338step2Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical3339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3339 raw3339Labels = mixedMoment B node4094 node4094Labels := by
  calc
    mixedMoment B raw3339 raw3339Labels = mixedMoment B raw3339step0 raw3339step0Labels := by
      have hz : ∀ j, raw3339 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3339step0 = (fun i j => raw3339 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3339step0 raw3339; decide +kernel
      have hl : raw3339step0Labels = raw3339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3339 raw3339Labels permutation590 hz
    mixedMoment B raw3339step0 raw3339step0Labels = mixedMoment B raw3339step1 raw3339step1Labels := by
      have hz : ∀ j, raw3339step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3339step1 = (fun i j => raw3339step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3339step1 raw3339step0; decide +kernel
      have hl : raw3339step1Labels = raw3339step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3339step0 raw3339step0Labels permutation104 hz
    mixedMoment B raw3339step1 raw3339step1Labels = mixedMoment B raw3339step2 raw3339step2Labels := by
      have hz : ∀ j, raw3339step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3339step2 = (fun i j => raw3339step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3339step2 raw3339step1; decide +kernel
      have hl : raw3339step2Labels = raw3339step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3339step1 raw3339step1Labels permutation20 hz
    mixedMoment B raw3339step2 raw3339step2Labels = mixedMoment B raw3339step3 raw3339step3Labels := by
      have hz : ∀ j, raw3339step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw3339step3 = (fun i j => raw3339step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw3339step3 raw3339step2; decide +kernel
      have hl : raw3339step3Labels = raw3339step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3339step2 raw3339step2Labels permutation4 hz
    mixedMoment B raw3339step3 raw3339step3Labels = mixedMoment B raw3339step4 raw3339step4Labels := by
      have hz : ∀ i, raw3339step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3339step4 = (fun i j => raw3339step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3339step4 raw3339step3; decide +kernel
      have hl : raw3339step4Labels = (fun j => raw3339step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3339step3 raw3339step3Labels permutation6 hz
    _ = mixedMoment B node4094 node4094Labels := by rfl

theorem canonical3340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3340 raw3340Labels = mixedMoment B node4094 node4094Labels := by
  calc
    mixedMoment B raw3340 raw3340Labels = mixedMoment B raw3340step0 raw3340step0Labels := by
      have hz : ∀ j, raw3340 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3340step0 = (fun i j => raw3340 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3340step0 raw3340; decide +kernel
      have hl : raw3340step0Labels = raw3340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3340 raw3340Labels permutation520 hz
    mixedMoment B raw3340step0 raw3340step0Labels = mixedMoment B raw3340step1 raw3340step1Labels := by
      have hz : ∀ j, raw3340step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3340step1 = (fun i j => raw3340step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3340step1 raw3340step0; decide +kernel
      have hl : raw3340step1Labels = raw3340step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3340step0 raw3340step0Labels permutation104 hz
    mixedMoment B raw3340step1 raw3340step1Labels = mixedMoment B raw3340step2 raw3340step2Labels := by
      have hz : ∀ j, raw3340step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3340step2 = (fun i j => raw3340step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3340step2 raw3340step1; decide +kernel
      have hl : raw3340step2Labels = raw3340step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3340step1 raw3340step1Labels permutation20 hz
    mixedMoment B raw3340step2 raw3340step2Labels = mixedMoment B raw3340step3 raw3340step3Labels := by
      have hz : ∀ j, raw3340step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw3340step3 = (fun i j => raw3340step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw3340step3 raw3340step2; decide +kernel
      have hl : raw3340step3Labels = raw3340step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3340step2 raw3340step2Labels permutation4 hz
    mixedMoment B raw3340step3 raw3340step3Labels = mixedMoment B raw3340step4 raw3340step4Labels := by
      have hz : ∀ i, raw3340step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3340step4 = (fun i j => raw3340step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3340step4 raw3340step3; decide +kernel
      have hl : raw3340step4Labels = (fun j => raw3340step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3340step3 raw3340step3Labels permutation6 hz
    _ = mixedMoment B node4094 node4094Labels := by rfl

theorem canonical3341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3341 raw3341Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw3341 raw3341Labels = mixedMoment B raw3341step0 raw3341step0Labels := by
      have ha : raw3341step0 = (fun i j => raw3341 (permutation295 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3341step0 raw3341; decide +kernel
      have hl : raw3341step0Labels = raw3341Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3341 raw3341Labels permutation295 permutation3
    mixedMoment B raw3341step0 raw3341step0Labels = mixedMoment B raw3341step1 raw3341step1Labels := by
      have ha : raw3341step1 = raw3341step0 := by apply Matrix.ext; unfold raw3341step1 raw3341step0; decide +kernel
      have hl : raw3341step0Labels = labelEmbedding6 ∘ raw3341step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3341step0 raw3341step0Labels raw3341step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

theorem canonical3342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3342 raw3342Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3342 raw3342Labels = mixedMoment B raw3342step0 raw3342step0Labels := by
      have ha : raw3342step0 = (fun i j => raw3342 (permutation387 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3342step0 raw3342; decide +kernel
      have hl : raw3342step0Labels = raw3342Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3342 raw3342Labels permutation387 permutation4
    mixedMoment B raw3342step0 raw3342step0Labels = mixedMoment B raw3342step1 raw3342step1Labels := by
      have ha : raw3342step1 = -raw3342step0 := by apply Matrix.ext; change ∀ i j, raw3342step1 i j = -(raw3342step0 i j); unfold raw3342step1 raw3342step0; decide +kernel
      have hl : raw3342step1Labels = raw3342step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3342step1 raw3342step1Labels = mixedMoment B raw3342step2 raw3342step2Labels := by
      have ha : raw3342step2 = raw3342step1 := by apply Matrix.ext; unfold raw3342step2 raw3342step1; decide +kernel
      have hl : raw3342step1Labels = labelEmbedding7 ∘ raw3342step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3342step1 raw3342step1Labels raw3342step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical3343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3343 raw3343Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3343 raw3343Labels = mixedMoment B raw3343step0 raw3343step0Labels := by
      have ha : raw3343step0 = (fun i j => raw3343 (permutation473 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3343step0 raw3343; decide +kernel
      have hl : raw3343step0Labels = raw3343Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3343 raw3343Labels permutation473 permutation4
    mixedMoment B raw3343step0 raw3343step0Labels = mixedMoment B raw3343step1 raw3343step1Labels := by
      have ha : raw3343step1 = -raw3343step0 := by apply Matrix.ext; change ∀ i j, raw3343step1 i j = -(raw3343step0 i j); unfold raw3343step1 raw3343step0; decide +kernel
      have hl : raw3343step1Labels = raw3343step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3343step1 raw3343step1Labels = mixedMoment B raw3343step2 raw3343step2Labels := by
      have ha : raw3343step2 = raw3343step1 := by apply Matrix.ext; unfold raw3343step2 raw3343step1; decide +kernel
      have hl : raw3343step1Labels = labelEmbedding7 ∘ raw3343step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3343step1 raw3343step1Labels raw3343step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical3344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3344 raw3344Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3344 raw3344Labels = mixedMoment B raw3344step0 raw3344step0Labels := by
      have hz : ∀ j, raw3344 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3344step0 = (fun i j => raw3344 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3344step0 raw3344; decide +kernel
      have hl : raw3344step0Labels = raw3344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3344 raw3344Labels permutation520 hz
    mixedMoment B raw3344step0 raw3344step0Labels = mixedMoment B raw3344step1 raw3344step1Labels := by
      have ha : raw3344step1 = (fun i j => raw3344step0 (permutation95 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3344step1 raw3344step0; decide +kernel
      have hl : raw3344step1Labels = raw3344step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3344step0 raw3344step0Labels permutation95 permutation4
    mixedMoment B raw3344step1 raw3344step1Labels = mixedMoment B raw3344step2 raw3344step2Labels := by
      have ha : raw3344step2 = -raw3344step1 := by apply Matrix.ext; change ∀ i j, raw3344step2 i j = -(raw3344step1 i j); unfold raw3344step2 raw3344step1; decide +kernel
      have hl : raw3344step2Labels = raw3344step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3344step2 raw3344step2Labels = mixedMoment B raw3344step3 raw3344step3Labels := by
      have ha : raw3344step3 = raw3344step2 := by apply Matrix.ext; unfold raw3344step3 raw3344step2; decide +kernel
      have hl : raw3344step2Labels = labelEmbedding7 ∘ raw3344step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3344step2 raw3344step2Labels raw3344step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5499 node5499Labels := by rfl

theorem canonical3345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3345 raw3345Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3345 raw3345Labels = mixedMoment B raw3345step0 raw3345step0Labels := by
      have hz : ∀ j, raw3345 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3345step0 = (fun i j => raw3345 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3345step0 raw3345; decide +kernel
      have hl : raw3345step0Labels = raw3345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3345 raw3345Labels permutation590 hz
    mixedMoment B raw3345step0 raw3345step0Labels = mixedMoment B raw3345step1 raw3345step1Labels := by
      have ha : raw3345step1 = (fun i j => raw3345step0 (permutation95 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3345step1 raw3345step0; decide +kernel
      have hl : raw3345step1Labels = raw3345step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3345step0 raw3345step0Labels permutation95 permutation4
    mixedMoment B raw3345step1 raw3345step1Labels = mixedMoment B raw3345step2 raw3345step2Labels := by
      have ha : raw3345step2 = -raw3345step1 := by apply Matrix.ext; change ∀ i j, raw3345step2 i j = -(raw3345step1 i j); unfold raw3345step2 raw3345step1; decide +kernel
      have hl : raw3345step2Labels = raw3345step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3345step2 raw3345step2Labels = mixedMoment B raw3345step3 raw3345step3Labels := by
      have ha : raw3345step3 = raw3345step2 := by apply Matrix.ext; unfold raw3345step3 raw3345step2; decide +kernel
      have hl : raw3345step2Labels = labelEmbedding7 ∘ raw3345step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3345step2 raw3345step2Labels raw3345step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5499 node5499Labels := by rfl

theorem canonical3346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3346 raw3346Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw3346 raw3346Labels = mixedMoment B raw3346step0 raw3346step0Labels := by
      have ha : raw3346step0 = (fun i j => raw3346 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3346step0 raw3346; decide +kernel
      have hl : raw3346step0Labels = raw3346Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3346 raw3346Labels permutation182 permutation3
    mixedMoment B raw3346step0 raw3346step0Labels = mixedMoment B raw3346step1 raw3346step1Labels := by
      have ha : raw3346step1 = raw3346step0 := by apply Matrix.ext; unfold raw3346step1 raw3346step0; decide +kernel
      have hl : raw3346step0Labels = labelEmbedding6 ∘ raw3346step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3346step0 raw3346step0Labels raw3346step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

theorem canonical3347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3347 raw3347Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3347 raw3347Labels = mixedMoment B raw3347step0 raw3347step0Labels := by
      have ha : raw3347step0 = (fun i j => raw3347 (permutation383 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3347step0 raw3347; decide +kernel
      have hl : raw3347step0Labels = raw3347Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3347 raw3347Labels permutation383 permutation4
    mixedMoment B raw3347step0 raw3347step0Labels = mixedMoment B raw3347step1 raw3347step1Labels := by
      have ha : raw3347step1 = -raw3347step0 := by apply Matrix.ext; change ∀ i j, raw3347step1 i j = -(raw3347step0 i j); unfold raw3347step1 raw3347step0; decide +kernel
      have hl : raw3347step1Labels = raw3347step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3347step1 raw3347step1Labels = mixedMoment B raw3347step2 raw3347step2Labels := by
      have ha : raw3347step2 = raw3347step1 := by apply Matrix.ext; unfold raw3347step2 raw3347step1; decide +kernel
      have hl : raw3347step1Labels = labelEmbedding7 ∘ raw3347step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3347step1 raw3347step1Labels raw3347step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical3348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3348 raw3348Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3348 raw3348Labels = mixedMoment B raw3348step0 raw3348step0Labels := by
      have ha : raw3348step0 = (fun i j => raw3348 (permutation468 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3348step0 raw3348; decide +kernel
      have hl : raw3348step0Labels = raw3348Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3348 raw3348Labels permutation468 permutation4
    mixedMoment B raw3348step0 raw3348step0Labels = mixedMoment B raw3348step1 raw3348step1Labels := by
      have ha : raw3348step1 = -raw3348step0 := by apply Matrix.ext; change ∀ i j, raw3348step1 i j = -(raw3348step0 i j); unfold raw3348step1 raw3348step0; decide +kernel
      have hl : raw3348step1Labels = raw3348step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3348step1 raw3348step1Labels = mixedMoment B raw3348step2 raw3348step2Labels := by
      have ha : raw3348step2 = raw3348step1 := by apply Matrix.ext; unfold raw3348step2 raw3348step1; decide +kernel
      have hl : raw3348step1Labels = labelEmbedding7 ∘ raw3348step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3348step1 raw3348step1Labels raw3348step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical3349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3349 raw3349Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3349 raw3349Labels = mixedMoment B raw3349step0 raw3349step0Labels := by
      have hz : ∀ j, raw3349 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3349step0 = (fun i j => raw3349 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3349step0 raw3349; decide +kernel
      have hl : raw3349step0Labels = raw3349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3349 raw3349Labels permutation520 hz
    mixedMoment B raw3349step0 raw3349step0Labels = mixedMoment B raw3349step1 raw3349step1Labels := by
      have ha : raw3349step1 = (fun i j => raw3349step0 (permutation93 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3349step1 raw3349step0; decide +kernel
      have hl : raw3349step1Labels = raw3349step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3349step0 raw3349step0Labels permutation93 permutation4
    mixedMoment B raw3349step1 raw3349step1Labels = mixedMoment B raw3349step2 raw3349step2Labels := by
      have ha : raw3349step2 = -raw3349step1 := by apply Matrix.ext; change ∀ i j, raw3349step2 i j = -(raw3349step1 i j); unfold raw3349step2 raw3349step1; decide +kernel
      have hl : raw3349step2Labels = raw3349step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3349step2 raw3349step2Labels = mixedMoment B raw3349step3 raw3349step3Labels := by
      have ha : raw3349step3 = raw3349step2 := by apply Matrix.ext; unfold raw3349step3 raw3349step2; decide +kernel
      have hl : raw3349step2Labels = labelEmbedding7 ∘ raw3349step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3349step2 raw3349step2Labels raw3349step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5499 node5499Labels := by rfl

theorem canonical3350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3350 raw3350Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3350 raw3350Labels = mixedMoment B raw3350step0 raw3350step0Labels := by
      have hz : ∀ j, raw3350 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3350step0 = (fun i j => raw3350 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3350step0 raw3350; decide +kernel
      have hl : raw3350step0Labels = raw3350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3350 raw3350Labels permutation590 hz
    mixedMoment B raw3350step0 raw3350step0Labels = mixedMoment B raw3350step1 raw3350step1Labels := by
      have ha : raw3350step1 = (fun i j => raw3350step0 (permutation93 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3350step1 raw3350step0; decide +kernel
      have hl : raw3350step1Labels = raw3350step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3350step0 raw3350step0Labels permutation93 permutation4
    mixedMoment B raw3350step1 raw3350step1Labels = mixedMoment B raw3350step2 raw3350step2Labels := by
      have ha : raw3350step2 = -raw3350step1 := by apply Matrix.ext; change ∀ i j, raw3350step2 i j = -(raw3350step1 i j); unfold raw3350step2 raw3350step1; decide +kernel
      have hl : raw3350step2Labels = raw3350step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3350step2 raw3350step2Labels = mixedMoment B raw3350step3 raw3350step3Labels := by
      have ha : raw3350step3 = raw3350step2 := by apply Matrix.ext; unfold raw3350step3 raw3350step2; decide +kernel
      have hl : raw3350step2Labels = labelEmbedding7 ∘ raw3350step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3350step2 raw3350step2Labels raw3350step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5499 node5499Labels := by rfl

theorem canonical3351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3351 raw3351Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3351 raw3351Labels = mixedMoment B raw3351step0 raw3351step0Labels := by
      have ha : raw3351step0 = (fun i j => raw3351 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3351step0 raw3351; decide +kernel
      have hl : raw3351step0Labels = raw3351Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3351 raw3351Labels permutation161 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical3352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3352 raw3352Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3352 raw3352Labels = mixedMoment B raw3352step0 raw3352step0Labels := by
      have ha : raw3352step0 = (fun i j => raw3352 (permutation274 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3352step0 raw3352; decide +kernel
      have hl : raw3352step0Labels = raw3352Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3352 raw3352Labels permutation274 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical3353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3353 raw3353Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw3353 raw3353Labels = mixedMoment B raw3353step0 raw3353step0Labels := by
      have ha : raw3353step0 = (fun i j => raw3353 (permutation434 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3353step0 raw3353; decide +kernel
      have hl : raw3353step0Labels = raw3353Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3353 raw3353Labels permutation434 permutation5
    mixedMoment B raw3353step0 raw3353step0Labels = mixedMoment B raw3353step1 raw3353step1Labels := by
      have ha : raw3353step1 = -raw3353step0 := by apply Matrix.ext; change ∀ i j, raw3353step1 i j = -(raw3353step0 i j); unfold raw3353step1 raw3353step0; decide +kernel
      have hl : raw3353step1Labels = raw3353step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3353step1 raw3353step1Labels = mixedMoment B raw3353step2 raw3353step2Labels := by
      have ha : raw3353step2 = raw3353step1 := by apply Matrix.ext; unfold raw3353step2 raw3353step1; decide +kernel
      have hl : raw3353step1Labels = labelEmbedding8 ∘ raw3353step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3353step1 raw3353step1Labels raw3353step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

theorem canonical3354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3354 raw3354Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3354 raw3354Labels = mixedMoment B raw3354step0 raw3354step0Labels := by
      have hz : ∀ j, raw3354 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3354step0 = (fun i j => raw3354 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3354step0 raw3354; decide +kernel
      have hl : raw3354step0Labels = raw3354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3354 raw3354Labels permutation520 hz
    mixedMoment B raw3354step0 raw3354step0Labels = mixedMoment B raw3354step1 raw3354step1Labels := by
      have ha : raw3354step1 = (fun i j => raw3354step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3354step1 raw3354step0; decide +kernel
      have hl : raw3354step1Labels = raw3354step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3354step0 raw3354step0Labels permutation35 permutation2
    _ = mixedMoment B node5499 node5499Labels := by rfl

theorem canonical3355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3355 raw3355Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3355 raw3355Labels = mixedMoment B raw3355step0 raw3355step0Labels := by
      have hz : ∀ j, raw3355 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3355step0 = (fun i j => raw3355 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3355step0 raw3355; decide +kernel
      have hl : raw3355step0Labels = raw3355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3355 raw3355Labels permutation590 hz
    mixedMoment B raw3355step0 raw3355step0Labels = mixedMoment B raw3355step1 raw3355step1Labels := by
      have ha : raw3355step1 = (fun i j => raw3355step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3355step1 raw3355step0; decide +kernel
      have hl : raw3355step1Labels = raw3355step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3355step0 raw3355step0Labels permutation35 permutation2
    _ = mixedMoment B node5499 node5499Labels := by rfl

theorem canonical3356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3356 raw3356Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3356 raw3356Labels = mixedMoment B raw3356step0 raw3356step0Labels := by
      have ha : raw3356step0 = (fun i j => raw3356 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3356step0 raw3356; decide +kernel
      have hl : raw3356step0Labels = raw3356Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3356 raw3356Labels permutation155 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical3357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3357 raw3357Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3357 raw3357Labels = mixedMoment B raw3357step0 raw3357step0Labels := by
      have ha : raw3357step0 = (fun i j => raw3357 (permutation268 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3357step0 raw3357; decide +kernel
      have hl : raw3357step0Labels = raw3357Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3357 raw3357Labels permutation268 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical3358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3358 raw3358Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw3358 raw3358Labels = mixedMoment B raw3358step0 raw3358step0Labels := by
      have ha : raw3358step0 = (fun i j => raw3358 (permutation346 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3358step0 raw3358; decide +kernel
      have hl : raw3358step0Labels = raw3358Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3358 raw3358Labels permutation346 permutation5
    mixedMoment B raw3358step0 raw3358step0Labels = mixedMoment B raw3358step1 raw3358step1Labels := by
      have ha : raw3358step1 = -raw3358step0 := by apply Matrix.ext; change ∀ i j, raw3358step1 i j = -(raw3358step0 i j); unfold raw3358step1 raw3358step0; decide +kernel
      have hl : raw3358step1Labels = raw3358step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3358step1 raw3358step1Labels = mixedMoment B raw3358step2 raw3358step2Labels := by
      have ha : raw3358step2 = raw3358step1 := by apply Matrix.ext; unfold raw3358step2 raw3358step1; decide +kernel
      have hl : raw3358step1Labels = labelEmbedding8 ∘ raw3358step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3358step1 raw3358step1Labels raw3358step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

theorem canonical3359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3359 raw3359Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3359 raw3359Labels = mixedMoment B raw3359step0 raw3359step0Labels := by
      have hz : ∀ j, raw3359 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3359step0 = (fun i j => raw3359 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3359step0 raw3359; decide +kernel
      have hl : raw3359step0Labels = raw3359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3359 raw3359Labels permutation520 hz
    mixedMoment B raw3359step0 raw3359step0Labels = mixedMoment B raw3359step1 raw3359step1Labels := by
      have ha : raw3359step1 = (fun i j => raw3359step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3359step1 raw3359step0; decide +kernel
      have hl : raw3359step1Labels = raw3359step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3359step0 raw3359step0Labels permutation33 permutation2
    _ = mixedMoment B node5499 node5499Labels := by rfl

theorem canonical3360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3360 raw3360Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3360 raw3360Labels = mixedMoment B raw3360step0 raw3360step0Labels := by
      have hz : ∀ j, raw3360 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3360step0 = (fun i j => raw3360 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3360step0 raw3360; decide +kernel
      have hl : raw3360step0Labels = raw3360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3360 raw3360Labels permutation590 hz
    mixedMoment B raw3360step0 raw3360step0Labels = mixedMoment B raw3360step1 raw3360step1Labels := by
      have ha : raw3360step1 = (fun i j => raw3360step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3360step1 raw3360step0; decide +kernel
      have hl : raw3360step1Labels = raw3360step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3360step0 raw3360step0Labels permutation33 permutation2
    _ = mixedMoment B node5499 node5499Labels := by rfl

theorem canonical3361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3361 raw3361Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw3361 raw3361Labels = mixedMoment B raw3361step0 raw3361step0Labels := by
      have ha : raw3361step0 = (fun i j => raw3361 (permutation584 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3361step0 raw3361; decide +kernel
      have hl : raw3361step0Labels = raw3361Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3361 raw3361Labels permutation584 permutation3
    mixedMoment B raw3361step0 raw3361step0Labels = mixedMoment B raw3361step1 raw3361step1Labels := by
      have ha : raw3361step1 = -raw3361step0 := by apply Matrix.ext; change ∀ i j, raw3361step1 i j = -(raw3361step0 i j); unfold raw3361step1 raw3361step0; decide +kernel
      have hl : raw3361step1Labels = raw3361step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3361step1 raw3361step1Labels = mixedMoment B raw3361step2 raw3361step2Labels := by
      have ha : raw3361step2 = raw3361step1 := by apply Matrix.ext; unfold raw3361step2 raw3361step1; decide +kernel
      have hl : raw3361step1Labels = labelEmbedding6 ∘ raw3361step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3361step1 raw3361step1Labels raw3361step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

theorem canonical3362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3362 raw3362Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw3362 raw3362Labels = mixedMoment B raw3362step0 raw3362step0Labels := by
      have ha : raw3362step0 = (fun i j => raw3362 (permutation583 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3362step0 raw3362; decide +kernel
      have hl : raw3362step0Labels = raw3362Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3362 raw3362Labels permutation583 permutation3
    mixedMoment B raw3362step0 raw3362step0Labels = mixedMoment B raw3362step1 raw3362step1Labels := by
      have ha : raw3362step1 = -raw3362step0 := by apply Matrix.ext; change ∀ i j, raw3362step1 i j = -(raw3362step0 i j); unfold raw3362step1 raw3362step0; decide +kernel
      have hl : raw3362step1Labels = raw3362step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3362step1 raw3362step1Labels = mixedMoment B raw3362step2 raw3362step2Labels := by
      have ha : raw3362step2 = raw3362step1 := by apply Matrix.ext; unfold raw3362step2 raw3362step1; decide +kernel
      have hl : raw3362step1Labels = labelEmbedding6 ∘ raw3362step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3362step1 raw3362step1Labels raw3362step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

theorem canonical3363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3363 raw3363Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw3363 raw3363Labels = mixedMoment B raw3363step0 raw3363step0Labels := by
      have ha : raw3363step0 = (fun i j => raw3363 (permutation570 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3363step0 raw3363; decide +kernel
      have hl : raw3363step0Labels = raw3363Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3363 raw3363Labels permutation570 permutation5
    mixedMoment B raw3363step0 raw3363step0Labels = mixedMoment B raw3363step1 raw3363step1Labels := by
      have ha : raw3363step1 = raw3363step0 := by apply Matrix.ext; unfold raw3363step1 raw3363step0; decide +kernel
      have hl : raw3363step0Labels = labelEmbedding8 ∘ raw3363step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3363step0 raw3363step0Labels raw3363step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

theorem canonical3364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3364 raw3364Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw3364 raw3364Labels = mixedMoment B raw3364step0 raw3364step0Labels := by
      have ha : raw3364step0 = (fun i j => raw3364 (permutation569 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3364step0 raw3364; decide +kernel
      have hl : raw3364step0Labels = raw3364Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3364 raw3364Labels permutation569 permutation5
    mixedMoment B raw3364step0 raw3364step0Labels = mixedMoment B raw3364step1 raw3364step1Labels := by
      have ha : raw3364step1 = raw3364step0 := by apply Matrix.ext; unfold raw3364step1 raw3364step0; decide +kernel
      have hl : raw3364step0Labels = labelEmbedding8 ∘ raw3364step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3364step0 raw3364step0Labels raw3364step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

theorem canonical3365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3365 raw3365Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw3365 raw3365Labels = mixedMoment B raw3365step0 raw3365step0Labels := by
      have hz : ∀ j, raw3365 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3365step0 = (fun i j => raw3365 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3365step0 raw3365; decide +kernel
      have hl : raw3365step0Labels = raw3365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3365 raw3365Labels permutation590 hz
    mixedMoment B raw3365step0 raw3365step0Labels = mixedMoment B raw3365step1 raw3365step1Labels := by
      have ha : raw3365step1 = (fun i j => raw3365step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3365step1 raw3365step0; decide +kernel
      have hl : raw3365step1Labels = raw3365step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3365step0 raw3365step0Labels permutation144 permutation3
    mixedMoment B raw3365step1 raw3365step1Labels = mixedMoment B raw3365step2 raw3365step2Labels := by
      have ha : raw3365step2 = -raw3365step1 := by apply Matrix.ext; change ∀ i j, raw3365step2 i j = -(raw3365step1 i j); unfold raw3365step2 raw3365step1; decide +kernel
      have hl : raw3365step2Labels = raw3365step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3365step2 raw3365step2Labels = mixedMoment B raw3365step3 raw3365step3Labels := by
      have ha : raw3365step3 = raw3365step2 := by apply Matrix.ext; unfold raw3365step3 raw3365step2; decide +kernel
      have hl : raw3365step2Labels = labelEmbedding6 ∘ raw3365step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3365step2 raw3365step2Labels raw3365step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5452 node5452Labels := by rfl

theorem canonical3366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3366 raw3366Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw3366 raw3366Labels = mixedMoment B raw3366step0 raw3366step0Labels := by
      have ha : raw3366step0 = (fun i j => raw3366 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3366step0 raw3366; decide +kernel
      have hl : raw3366step0Labels = raw3366Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3366 raw3366Labels permutation682 permutation3
    mixedMoment B raw3366step0 raw3366step0Labels = mixedMoment B raw3366step1 raw3366step1Labels := by
      have ha : raw3366step1 = -raw3366step0 := by apply Matrix.ext; change ∀ i j, raw3366step1 i j = -(raw3366step0 i j); unfold raw3366step1 raw3366step0; decide +kernel
      have hl : raw3366step1Labels = raw3366step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3366step1 raw3366step1Labels = mixedMoment B raw3366step2 raw3366step2Labels := by
      have ha : raw3366step2 = raw3366step1 := by apply Matrix.ext; unfold raw3366step2 raw3366step1; decide +kernel
      have hl : raw3366step1Labels = labelEmbedding6 ∘ raw3366step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3366step1 raw3366step1Labels raw3366step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

theorem canonical3367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3367 raw3367Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw3367 raw3367Labels = mixedMoment B raw3367step0 raw3367step0Labels := by
      have ha : raw3367step0 = (fun i j => raw3367 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3367step0 raw3367; decide +kernel
      have hl : raw3367step0Labels = raw3367Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3367 raw3367Labels permutation681 permutation3
    mixedMoment B raw3367step0 raw3367step0Labels = mixedMoment B raw3367step1 raw3367step1Labels := by
      have ha : raw3367step1 = -raw3367step0 := by apply Matrix.ext; change ∀ i j, raw3367step1 i j = -(raw3367step0 i j); unfold raw3367step1 raw3367step0; decide +kernel
      have hl : raw3367step1Labels = raw3367step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3367step1 raw3367step1Labels = mixedMoment B raw3367step2 raw3367step2Labels := by
      have ha : raw3367step2 = raw3367step1 := by apply Matrix.ext; unfold raw3367step2 raw3367step1; decide +kernel
      have hl : raw3367step1Labels = labelEmbedding6 ∘ raw3367step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3367step1 raw3367step1Labels raw3367step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

theorem canonical3368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3368 raw3368Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw3368 raw3368Labels = mixedMoment B raw3368step0 raw3368step0Labels := by
      have ha : raw3368step0 = (fun i j => raw3368 (permutation666 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3368step0 raw3368; decide +kernel
      have hl : raw3368step0Labels = raw3368Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3368 raw3368Labels permutation666 permutation5
    mixedMoment B raw3368step0 raw3368step0Labels = mixedMoment B raw3368step1 raw3368step1Labels := by
      have ha : raw3368step1 = raw3368step0 := by apply Matrix.ext; unfold raw3368step1 raw3368step0; decide +kernel
      have hl : raw3368step0Labels = labelEmbedding8 ∘ raw3368step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3368step0 raw3368step0Labels raw3368step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

theorem canonical3369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3369 raw3369Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw3369 raw3369Labels = mixedMoment B raw3369step0 raw3369step0Labels := by
      have ha : raw3369step0 = (fun i j => raw3369 (permutation665 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3369step0 raw3369; decide +kernel
      have hl : raw3369step0Labels = raw3369Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3369 raw3369Labels permutation665 permutation5
    mixedMoment B raw3369step0 raw3369step0Labels = mixedMoment B raw3369step1 raw3369step1Labels := by
      have ha : raw3369step1 = raw3369step0 := by apply Matrix.ext; unfold raw3369step1 raw3369step0; decide +kernel
      have hl : raw3369step0Labels = labelEmbedding8 ∘ raw3369step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3369step0 raw3369step0Labels raw3369step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

theorem canonical3370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3370 raw3370Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw3370 raw3370Labels = mixedMoment B raw3370step0 raw3370step0Labels := by
      have hz : ∀ j, raw3370 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3370step0 = (fun i j => raw3370 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3370step0 raw3370; decide +kernel
      have hl : raw3370step0Labels = raw3370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3370 raw3370Labels permutation520 hz
    mixedMoment B raw3370step0 raw3370step0Labels = mixedMoment B raw3370step1 raw3370step1Labels := by
      have ha : raw3370step1 = (fun i j => raw3370step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3370step1 raw3370step0; decide +kernel
      have hl : raw3370step1Labels = raw3370step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3370step0 raw3370step0Labels permutation144 permutation3
    mixedMoment B raw3370step1 raw3370step1Labels = mixedMoment B raw3370step2 raw3370step2Labels := by
      have ha : raw3370step2 = -raw3370step1 := by apply Matrix.ext; change ∀ i j, raw3370step2 i j = -(raw3370step1 i j); unfold raw3370step2 raw3370step1; decide +kernel
      have hl : raw3370step2Labels = raw3370step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3370step2 raw3370step2Labels = mixedMoment B raw3370step3 raw3370step3Labels := by
      have ha : raw3370step3 = raw3370step2 := by apply Matrix.ext; unfold raw3370step3 raw3370step2; decide +kernel
      have hl : raw3370step2Labels = labelEmbedding6 ∘ raw3370step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3370step2 raw3370step2Labels raw3370step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5452 node5452Labels := by rfl

theorem canonical3371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3371 raw3371Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw3371 raw3371Labels = mixedMoment B raw3371step0 raw3371step0Labels := by
      have ha : raw3371step0 = (fun i j => raw3371 (permutation318 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3371step0 raw3371; decide +kernel
      have hl : raw3371step0Labels = raw3371Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3371 raw3371Labels permutation318 permutation5
    mixedMoment B raw3371step0 raw3371step0Labels = mixedMoment B raw3371step1 raw3371step1Labels := by
      have ha : raw3371step1 = -raw3371step0 := by apply Matrix.ext; change ∀ i j, raw3371step1 i j = -(raw3371step0 i j); unfold raw3371step1 raw3371step0; decide +kernel
      have hl : raw3371step1Labels = raw3371step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3371step1 raw3371step1Labels = mixedMoment B raw3371step2 raw3371step2Labels := by
      have ha : raw3371step2 = raw3371step1 := by apply Matrix.ext; unfold raw3371step2 raw3371step1; decide +kernel
      have hl : raw3371step1Labels = labelEmbedding8 ∘ raw3371step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3371step1 raw3371step1Labels raw3371step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical3372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3372 raw3372Labels = mixedMoment B node5500 node5500Labels := by
  calc
    mixedMoment B raw3372 raw3372Labels = mixedMoment B raw3372step0 raw3372step0Labels := by
      have ha : raw3372step0 = (fun i j => raw3372 (permutation367 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3372step0 raw3372; decide +kernel
      have hl : raw3372step0Labels = raw3372Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3372 raw3372Labels permutation367 permutation2
    _ = mixedMoment B node5500 node5500Labels := by rfl

theorem canonical3373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3373 raw3373Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3373 raw3373Labels = mixedMoment B raw3373step0 raw3373step0Labels := by
      have ha : raw3373step0 = (fun i j => raw3373 (permutation464 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3373step0 raw3373; decide +kernel
      have hl : raw3373step0Labels = raw3373Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3373 raw3373Labels permutation464 permutation5
    mixedMoment B raw3373step0 raw3373step0Labels = mixedMoment B raw3373step1 raw3373step1Labels := by
      have ha : raw3373step1 = -raw3373step0 := by apply Matrix.ext; change ∀ i j, raw3373step1 i j = -(raw3373step0 i j); unfold raw3373step1 raw3373step0; decide +kernel
      have hl : raw3373step1Labels = raw3373step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3373step1 raw3373step1Labels = mixedMoment B raw3373step2 raw3373step2Labels := by
      have ha : raw3373step2 = raw3373step1 := by apply Matrix.ext; unfold raw3373step2 raw3373step1; decide +kernel
      have hl : raw3373step1Labels = labelEmbedding8 ∘ raw3373step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3373step1 raw3373step1Labels raw3373step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical3374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3374 raw3374Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3374 raw3374Labels = mixedMoment B raw3374step0 raw3374step0Labels := by
      have hz : ∀ j, raw3374 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3374step0 = (fun i j => raw3374 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3374step0 raw3374; decide +kernel
      have hl : raw3374step0Labels = raw3374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3374 raw3374Labels permutation520 hz
    mixedMoment B raw3374step0 raw3374step0Labels = mixedMoment B raw3374step1 raw3374step1Labels := by
      have ha : raw3374step1 = (fun i j => raw3374step0 (permutation42 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3374step1 raw3374step0; decide +kernel
      have hl : raw3374step1Labels = raw3374step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3374step0 raw3374step0Labels permutation42 permutation4
    mixedMoment B raw3374step1 raw3374step1Labels = mixedMoment B raw3374step2 raw3374step2Labels := by
      have ha : raw3374step2 = raw3374step1 := by apply Matrix.ext; unfold raw3374step2 raw3374step1; decide +kernel
      have hl : raw3374step1Labels = labelEmbedding7 ∘ raw3374step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3374step1 raw3374step1Labels raw3374step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5499 node5499Labels := by rfl

theorem canonical3375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3375 raw3375Labels = mixedMoment B node5497 node5497Labels := by
  calc
    mixedMoment B raw3375 raw3375Labels = mixedMoment B raw3375step0 raw3375step0Labels := by
      have ha : raw3375step0 = (fun i j => raw3375 (permutation188 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3375step0 raw3375; decide +kernel
      have hl : raw3375step0Labels = raw3375Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3375 raw3375Labels permutation188 permutation4
    mixedMoment B raw3375step0 raw3375step0Labels = mixedMoment B raw3375step1 raw3375step1Labels := by
      have ha : raw3375step1 = raw3375step0 := by apply Matrix.ext; unfold raw3375step1 raw3375step0; decide +kernel
      have hl : raw3375step0Labels = labelEmbedding7 ∘ raw3375step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3375step0 raw3375step0Labels raw3375step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5497 node5497Labels := by rfl

theorem canonical3376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3376 raw3376Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3376 raw3376Labels = mixedMoment B raw3376step0 raw3376step0Labels := by
      have hz : ∀ j, raw3376 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3376step0 = (fun i j => raw3376 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3376step0 raw3376; decide +kernel
      have hl : raw3376step0Labels = raw3376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3376 raw3376Labels permutation265 hz
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical3377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3377 raw3377Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3377 raw3377Labels = mixedMoment B raw3377step0 raw3377step0Labels := by
      have hz : ∀ j, raw3377 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3377step0 = (fun i j => raw3377 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3377step0 raw3377; decide +kernel
      have hl : raw3377step0Labels = raw3377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3377 raw3377Labels permutation265 hz
    _ = mixedMoment B node5499 node5499Labels := by rfl

theorem canonical3378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3378 raw3378Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3378 raw3378Labels = mixedMoment B raw3378step0 raw3378step0Labels := by
      have hz : ∀ j, raw3378 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3378step0 = (fun i j => raw3378 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3378step0 raw3378; decide +kernel
      have hl : raw3378step0Labels = raw3378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3378 raw3378Labels permutation265 hz
    mixedMoment B raw3378step0 raw3378step0Labels = mixedMoment B raw3378step1 raw3378step1Labels := by
      have ha : raw3378step1 = (fun i j => raw3378step0 (permutation99 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3378step1 raw3378step0; decide +kernel
      have hl : raw3378step1Labels = raw3378step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3378step0 raw3378step0Labels permutation99 permutation4
    mixedMoment B raw3378step1 raw3378step1Labels = mixedMoment B raw3378step2 raw3378step2Labels := by
      have ha : raw3378step2 = -raw3378step1 := by apply Matrix.ext; change ∀ i j, raw3378step2 i j = -(raw3378step1 i j); unfold raw3378step2 raw3378step1; decide +kernel
      have hl : raw3378step2Labels = raw3378step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3378step2 raw3378step2Labels = mixedMoment B raw3378step3 raw3378step3Labels := by
      have ha : raw3378step3 = raw3378step2 := by apply Matrix.ext; unfold raw3378step3 raw3378step2; decide +kernel
      have hl : raw3378step2Labels = labelEmbedding7 ∘ raw3378step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3378step2 raw3378step2Labels raw3378step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical3379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3379 raw3379Labels = mixedMoment B node5501 node5501Labels := by
  calc
    mixedMoment B raw3379 raw3379Labels = mixedMoment B raw3379step0 raw3379step0Labels := by
      have hz : ∀ j, raw3379 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3379step0 = (fun i j => raw3379 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3379step0 raw3379; decide +kernel
      have hl : raw3379step0Labels = raw3379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3379 raw3379Labels permutation520 hz
    mixedMoment B raw3379step0 raw3379step0Labels = mixedMoment B raw3379step1 raw3379step1Labels := by
      have hz : ∀ j, raw3379step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3379step1 = (fun i j => raw3379step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3379step1 raw3379step0; decide +kernel
      have hl : raw3379step1Labels = raw3379step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3379step0 raw3379step0Labels permutation56 hz
    mixedMoment B raw3379step1 raw3379step1Labels = mixedMoment B raw3379step2 raw3379step2Labels := by
      have ha : raw3379step2 = (fun i j => raw3379step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3379step2 raw3379step1; decide +kernel
      have hl : raw3379step2Labels = raw3379step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3379step1 raw3379step1Labels permutation24 permutation6
    mixedMoment B raw3379step2 raw3379step2Labels = mixedMoment B raw3379step3 raw3379step3Labels := by
      have ha : raw3379step3 = raw3379step2 := by apply Matrix.ext; unfold raw3379step3 raw3379step2; decide +kernel
      have hl : raw3379step2Labels = labelEmbedding9 ∘ raw3379step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3379step2 raw3379step2Labels raw3379step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5501 node5501Labels := by rfl

theorem canonical3380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3380 raw3380Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3380 raw3380Labels = mixedMoment B raw3380step0 raw3380step0Labels := by
      have hz : ∀ j, raw3380 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3380step0 = (fun i j => raw3380 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3380step0 raw3380; decide +kernel
      have hl : raw3380step0Labels = raw3380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3380 raw3380Labels permutation265 hz
    mixedMoment B raw3380step0 raw3380step0Labels = mixedMoment B raw3380step1 raw3380step1Labels := by
      have ha : raw3380step1 = (fun i j => raw3380step0 (permutation99 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3380step1 raw3380step0; decide +kernel
      have hl : raw3380step1Labels = raw3380step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3380step0 raw3380step0Labels permutation99 permutation4
    mixedMoment B raw3380step1 raw3380step1Labels = mixedMoment B raw3380step2 raw3380step2Labels := by
      have ha : raw3380step2 = -raw3380step1 := by apply Matrix.ext; change ∀ i j, raw3380step2 i j = -(raw3380step1 i j); unfold raw3380step2 raw3380step1; decide +kernel
      have hl : raw3380step2Labels = raw3380step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3380step2 raw3380step2Labels = mixedMoment B raw3380step3 raw3380step3Labels := by
      have ha : raw3380step3 = raw3380step2 := by apply Matrix.ext; unfold raw3380step3 raw3380step2; decide +kernel
      have hl : raw3380step2Labels = labelEmbedding7 ∘ raw3380step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3380step2 raw3380step2Labels raw3380step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5499 node5499Labels := by rfl

theorem canonical3381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3381 raw3381Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw3381 raw3381Labels = mixedMoment B raw3381step0 raw3381step0Labels := by
      have ha : raw3381step0 = (fun i j => raw3381 (permutation163 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3381step0 raw3381; decide +kernel
      have hl : raw3381step0Labels = raw3381Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3381 raw3381Labels permutation163 permutation3
    mixedMoment B raw3381step0 raw3381step0Labels = mixedMoment B raw3381step1 raw3381step1Labels := by
      have ha : raw3381step1 = raw3381step0 := by apply Matrix.ext; unfold raw3381step1 raw3381step0; decide +kernel
      have hl : raw3381step0Labels = labelEmbedding6 ∘ raw3381step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3381step0 raw3381step0Labels raw3381step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

theorem canonical3382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3382 raw3382Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw3382 raw3382Labels = mixedMoment B raw3382step0 raw3382step0Labels := by
      have ha : raw3382step0 = (fun i j => raw3382 (permutation310 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3382step0 raw3382; decide +kernel
      have hl : raw3382step0Labels = raw3382Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3382 raw3382Labels permutation310 permutation5
    mixedMoment B raw3382step0 raw3382step0Labels = mixedMoment B raw3382step1 raw3382step1Labels := by
      have ha : raw3382step1 = -raw3382step0 := by apply Matrix.ext; change ∀ i j, raw3382step1 i j = -(raw3382step0 i j); unfold raw3382step1 raw3382step0; decide +kernel
      have hl : raw3382step1Labels = raw3382step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3382step1 raw3382step1Labels = mixedMoment B raw3382step2 raw3382step2Labels := by
      have ha : raw3382step2 = raw3382step1 := by apply Matrix.ext; unfold raw3382step2 raw3382step1; decide +kernel
      have hl : raw3382step1Labels = labelEmbedding8 ∘ raw3382step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3382step1 raw3382step1Labels raw3382step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical3383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3383 raw3383Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw3383 raw3383Labels = mixedMoment B raw3383step0 raw3383step0Labels := by
      have ha : raw3383step0 = (fun i j => raw3383 (permutation409 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3383step0 raw3383; decide +kernel
      have hl : raw3383step0Labels = raw3383Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3383 raw3383Labels permutation409 permutation5
    mixedMoment B raw3383step0 raw3383step0Labels = mixedMoment B raw3383step1 raw3383step1Labels := by
      have ha : raw3383step1 = raw3383step0 := by apply Matrix.ext; unfold raw3383step1 raw3383step0; decide +kernel
      have hl : raw3383step0Labels = labelEmbedding8 ∘ raw3383step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3383step0 raw3383step0Labels raw3383step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

theorem canonical3384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3384 raw3384Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3384 raw3384Labels = mixedMoment B raw3384step0 raw3384step0Labels := by
      have hz : ∀ j, raw3384 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3384step0 = (fun i j => raw3384 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3384step0 raw3384; decide +kernel
      have hl : raw3384step0Labels = raw3384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3384 raw3384Labels permutation520 hz
    mixedMoment B raw3384step0 raw3384step0Labels = mixedMoment B raw3384step1 raw3384step1Labels := by
      have ha : raw3384step1 = (fun i j => raw3384step0 (permutation84 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3384step1 raw3384step0; decide +kernel
      have hl : raw3384step1Labels = raw3384step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3384step0 raw3384step0Labels permutation84 permutation4
    mixedMoment B raw3384step1 raw3384step1Labels = mixedMoment B raw3384step2 raw3384step2Labels := by
      have ha : raw3384step2 = raw3384step1 := by apply Matrix.ext; unfold raw3384step2 raw3384step1; decide +kernel
      have hl : raw3384step1Labels = labelEmbedding7 ∘ raw3384step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3384step1 raw3384step1Labels raw3384step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical3385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3385 raw3385Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3385 raw3385Labels = mixedMoment B raw3385step0 raw3385step0Labels := by
      have ha : raw3385step0 = (fun i j => raw3385 (permutation400 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3385step0 raw3385; decide +kernel
      have hl : raw3385step0Labels = raw3385Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3385 raw3385Labels permutation400 permutation5
    mixedMoment B raw3385step0 raw3385step0Labels = mixedMoment B raw3385step1 raw3385step1Labels := by
      have ha : raw3385step1 = raw3385step0 := by apply Matrix.ext; unfold raw3385step1 raw3385step0; decide +kernel
      have hl : raw3385step0Labels = labelEmbedding8 ∘ raw3385step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3385step0 raw3385step0Labels raw3385step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical3386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3386 raw3386Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3386 raw3386Labels = mixedMoment B raw3386step0 raw3386step0Labels := by
      have ha : raw3386step0 = (fun i j => raw3386 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3386step0 raw3386; decide +kernel
      have hl : raw3386step0Labels = raw3386Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3386 raw3386Labels permutation153 permutation3
    mixedMoment B raw3386step0 raw3386step0Labels = mixedMoment B raw3386step1 raw3386step1Labels := by
      have ha : raw3386step1 = raw3386step0 := by apply Matrix.ext; unfold raw3386step1 raw3386step0; decide +kernel
      have hl : raw3386step0Labels = labelEmbedding6 ∘ raw3386step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3386step0 raw3386step0Labels raw3386step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical3387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3387 raw3387Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw3387 raw3387Labels = mixedMoment B raw3387step0 raw3387step0Labels := by
      have ha : raw3387step0 = (fun i j => raw3387 (permutation266 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3387step0 raw3387; decide +kernel
      have hl : raw3387step0Labels = raw3387Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3387 raw3387Labels permutation266 permutation3
    mixedMoment B raw3387step0 raw3387step0Labels = mixedMoment B raw3387step1 raw3387step1Labels := by
      have ha : raw3387step1 = raw3387step0 := by apply Matrix.ext; unfold raw3387step1 raw3387step0; decide +kernel
      have hl : raw3387step0Labels = labelEmbedding6 ∘ raw3387step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3387step0 raw3387step0Labels raw3387step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical3388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3388 raw3388Labels = mixedMoment B node5497 node5497Labels := by
  calc
    mixedMoment B raw3388 raw3388Labels = mixedMoment B raw3388step0 raw3388step0Labels := by
      have ha : raw3388step0 = (fun i j => raw3388 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3388step0 raw3388; decide +kernel
      have hl : raw3388step0Labels = raw3388Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3388 raw3388Labels permutation178 permutation2
    _ = mixedMoment B node5497 node5497Labels := by rfl

theorem canonical3389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3389 raw3389Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3389 raw3389Labels = mixedMoment B raw3389step0 raw3389step0Labels := by
      have hz : ∀ j, raw3389 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3389step0 = (fun i j => raw3389 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3389step0 raw3389; decide +kernel
      have hl : raw3389step0Labels = raw3389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3389 raw3389Labels permutation520 hz
    mixedMoment B raw3389step0 raw3389step0Labels = mixedMoment B raw3389step1 raw3389step1Labels := by
      have ha : raw3389step1 = (fun i j => raw3389step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3389step1 raw3389step0; decide +kernel
      have hl : raw3389step1Labels = raw3389step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3389step0 raw3389step0Labels permutation127 permutation2
    mixedMoment B raw3389step1 raw3389step1Labels = mixedMoment B raw3389step2 raw3389step2Labels := by
      have ha : raw3389step2 = -raw3389step1 := by apply Matrix.ext; change ∀ i j, raw3389step2 i j = -(raw3389step1 i j); unfold raw3389step2 raw3389step1; decide +kernel
      have hl : raw3389step2Labels = raw3389step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5499 node5499Labels := by rfl

theorem canonical3390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3390 raw3390Labels = mixedMoment B node5500 node5500Labels := by
  calc
    mixedMoment B raw3390 raw3390Labels = mixedMoment B raw3390step0 raw3390step0Labels := by
      have ha : raw3390step0 = (fun i j => raw3390 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3390step0 raw3390; decide +kernel
      have hl : raw3390step0Labels = raw3390Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3390 raw3390Labels permutation157 permutation2
    _ = mixedMoment B node5500 node5500Labels := by rfl

theorem canonical3391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3391 raw3391Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw3391 raw3391Labels = mixedMoment B raw3391step0 raw3391step0Labels := by
      have ha : raw3391step0 = (fun i j => raw3391 (permutation584 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3391step0 raw3391; decide +kernel
      have hl : raw3391step0Labels = raw3391Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3391 raw3391Labels permutation584 permutation3
    mixedMoment B raw3391step0 raw3391step0Labels = mixedMoment B raw3391step1 raw3391step1Labels := by
      have ha : raw3391step1 = -raw3391step0 := by apply Matrix.ext; change ∀ i j, raw3391step1 i j = -(raw3391step0 i j); unfold raw3391step1 raw3391step0; decide +kernel
      have hl : raw3391step1Labels = raw3391step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3391step1 raw3391step1Labels = mixedMoment B raw3391step2 raw3391step2Labels := by
      have ha : raw3391step2 = raw3391step1 := by apply Matrix.ext; unfold raw3391step2 raw3391step1; decide +kernel
      have hl : raw3391step1Labels = labelEmbedding6 ∘ raw3391step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3391step1 raw3391step1Labels raw3391step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical3392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3392 raw3392Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw3392 raw3392Labels = mixedMoment B raw3392step0 raw3392step0Labels := by
      have ha : raw3392step0 = (fun i j => raw3392 (permutation272 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3392step0 raw3392; decide +kernel
      have hl : raw3392step0Labels = raw3392Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3392 raw3392Labels permutation272 permutation3
    mixedMoment B raw3392step0 raw3392step0Labels = mixedMoment B raw3392step1 raw3392step1Labels := by
      have ha : raw3392step1 = raw3392step0 := by apply Matrix.ext; unfold raw3392step1 raw3392step0; decide +kernel
      have hl : raw3392step0Labels = labelEmbedding6 ∘ raw3392step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3392step0 raw3392step0Labels raw3392step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5423 node5423Labels := by rfl

theorem canonical3393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3393 raw3393Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw3393 raw3393Labels = mixedMoment B raw3393step0 raw3393step0Labels := by
      have ha : raw3393step0 = (fun i j => raw3393 (permutation585 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3393step0 raw3393; decide +kernel
      have hl : raw3393step0Labels = raw3393Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3393 raw3393Labels permutation585 permutation3
    mixedMoment B raw3393step0 raw3393step0Labels = mixedMoment B raw3393step1 raw3393step1Labels := by
      have ha : raw3393step1 = -raw3393step0 := by apply Matrix.ext; change ∀ i j, raw3393step1 i j = -(raw3393step0 i j); unfold raw3393step1 raw3393step0; decide +kernel
      have hl : raw3393step1Labels = raw3393step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3393step1 raw3393step1Labels = mixedMoment B raw3393step2 raw3393step2Labels := by
      have ha : raw3393step2 = raw3393step1 := by apply Matrix.ext; unfold raw3393step2 raw3393step1; decide +kernel
      have hl : raw3393step1Labels = labelEmbedding6 ∘ raw3393step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3393step1 raw3393step1Labels raw3393step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical3394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3394 raw3394Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw3394 raw3394Labels = mixedMoment B raw3394step0 raw3394step0Labels := by
      have ha : raw3394step0 = (fun i j => raw3394 (permutation547 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3394step0 raw3394; decide +kernel
      have hl : raw3394step0Labels = raw3394Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3394 raw3394Labels permutation547 permutation5
    mixedMoment B raw3394step0 raw3394step0Labels = mixedMoment B raw3394step1 raw3394step1Labels := by
      have ha : raw3394step1 = raw3394step0 := by apply Matrix.ext; unfold raw3394step1 raw3394step0; decide +kernel
      have hl : raw3394step0Labels = labelEmbedding8 ∘ raw3394step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3394step0 raw3394step0Labels raw3394step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical3395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3395 raw3395Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw3395 raw3395Labels = mixedMoment B raw3395step0 raw3395step0Labels := by
      have ha : raw3395step0 = (fun i j => raw3395 (permutation542 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3395step0 raw3395; decide +kernel
      have hl : raw3395step0Labels = raw3395Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3395 raw3395Labels permutation542 permutation5
    mixedMoment B raw3395step0 raw3395step0Labels = mixedMoment B raw3395step1 raw3395step1Labels := by
      have ha : raw3395step1 = raw3395step0 := by apply Matrix.ext; unfold raw3395step1 raw3395step0; decide +kernel
      have hl : raw3395step0Labels = labelEmbedding8 ∘ raw3395step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3395step0 raw3395step0Labels raw3395step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical3396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3396 raw3396Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw3396 raw3396Labels = mixedMoment B raw3396step0 raw3396step0Labels := by
      have ha : raw3396step0 = (fun i j => raw3396 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3396step0 raw3396; decide +kernel
      have hl : raw3396step0Labels = raw3396Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3396 raw3396Labels permutation158 permutation3
    mixedMoment B raw3396step0 raw3396step0Labels = mixedMoment B raw3396step1 raw3396step1Labels := by
      have ha : raw3396step1 = raw3396step0 := by apply Matrix.ext; unfold raw3396step1 raw3396step0; decide +kernel
      have hl : raw3396step0Labels = labelEmbedding6 ∘ raw3396step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3396step0 raw3396step0Labels raw3396step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

theorem canonical3397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3397 raw3397Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw3397 raw3397Labels = mixedMoment B raw3397step0 raw3397step0Labels := by
      have ha : raw3397step0 = (fun i j => raw3397 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3397step0 raw3397; decide +kernel
      have hl : raw3397step0Labels = raw3397Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3397 raw3397Labels permutation271 permutation3
    mixedMoment B raw3397step0 raw3397step0Labels = mixedMoment B raw3397step1 raw3397step1Labels := by
      have ha : raw3397step1 = raw3397step0 := by apply Matrix.ext; unfold raw3397step1 raw3397step0; decide +kernel
      have hl : raw3397step0Labels = labelEmbedding6 ∘ raw3397step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3397step0 raw3397step0Labels raw3397step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical3398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3398 raw3398Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3398 raw3398Labels = mixedMoment B raw3398step0 raw3398step0Labels := by
      have ha : raw3398step0 = (fun i j => raw3398 (permutation684 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3398step0 raw3398; decide +kernel
      have hl : raw3398step0Labels = raw3398Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3398 raw3398Labels permutation684 permutation3
    mixedMoment B raw3398step0 raw3398step0Labels = mixedMoment B raw3398step1 raw3398step1Labels := by
      have ha : raw3398step1 = -raw3398step0 := by apply Matrix.ext; change ∀ i j, raw3398step1 i j = -(raw3398step0 i j); unfold raw3398step1 raw3398step0; decide +kernel
      have hl : raw3398step1Labels = raw3398step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3398step1 raw3398step1Labels = mixedMoment B raw3398step2 raw3398step2Labels := by
      have ha : raw3398step2 = raw3398step1 := by apply Matrix.ext; unfold raw3398step2 raw3398step1; decide +kernel
      have hl : raw3398step1Labels = labelEmbedding6 ∘ raw3398step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3398step1 raw3398step1Labels raw3398step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical3399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3399 raw3399Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw3399 raw3399Labels = mixedMoment B raw3399step0 raw3399step0Labels := by
      have ha : raw3399step0 = (fun i j => raw3399 (permutation677 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3399step0 raw3399; decide +kernel
      have hl : raw3399step0Labels = raw3399Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3399 raw3399Labels permutation677 permutation3
    mixedMoment B raw3399step0 raw3399step0Labels = mixedMoment B raw3399step1 raw3399step1Labels := by
      have ha : raw3399step1 = -raw3399step0 := by apply Matrix.ext; change ∀ i j, raw3399step1 i j = -(raw3399step0 i j); unfold raw3399step1 raw3399step0; decide +kernel
      have hl : raw3399step1Labels = raw3399step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3399step1 raw3399step1Labels = mixedMoment B raw3399step2 raw3399step2Labels := by
      have ha : raw3399step2 = raw3399step1 := by apply Matrix.ext; unfold raw3399step2 raw3399step1; decide +kernel
      have hl : raw3399step1Labels = labelEmbedding6 ∘ raw3399step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3399step1 raw3399step1Labels raw3399step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

theorem canonical3400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3400 raw3400Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3400 raw3400Labels = mixedMoment B raw3400step0 raw3400step0Labels := by
      have hz : ∀ j, raw3400 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3400step0 = (fun i j => raw3400 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3400step0 raw3400; decide +kernel
      have hl : raw3400step0Labels = raw3400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3400 raw3400Labels permutation520 hz
    mixedMoment B raw3400step0 raw3400step0Labels = mixedMoment B raw3400step1 raw3400step1Labels := by
      have ha : raw3400step1 = (fun i j => raw3400step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3400step1 raw3400step0; decide +kernel
      have hl : raw3400step1Labels = raw3400step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3400step0 raw3400step0Labels permutation151 permutation2
    mixedMoment B raw3400step1 raw3400step1Labels = mixedMoment B raw3400step2 raw3400step2Labels := by
      have ha : raw3400step2 = -raw3400step1 := by apply Matrix.ext; change ∀ i j, raw3400step2 i j = -(raw3400step1 i j); unfold raw3400step2 raw3400step1; decide +kernel
      have hl : raw3400step2Labels = raw3400step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical3431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3431 raw3431Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw3431 raw3431Labels = mixedMoment B raw3431step0 raw3431step0Labels := by
      have hz : ∀ j, raw3431 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3431step0 = (fun i j => raw3431 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3431step0 raw3431; decide +kernel
      have hl : raw3431step0Labels = raw3431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3431 raw3431Labels permutation434 hz
    mixedMoment B raw3431step0 raw3431step0Labels = mixedMoment B raw3431step1 raw3431step1Labels := by
      have hz : ∀ j, raw3431step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3431step1 = (fun i j => raw3431step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3431step1 raw3431step0; decide +kernel
      have hl : raw3431step1Labels = raw3431step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3431step0 raw3431step0Labels permutation80 hz
    mixedMoment B raw3431step1 raw3431step1Labels = mixedMoment B raw3431step2 raw3431step2Labels := by
      have hz : ∀ j, raw3431step1 (permutation8 0) j = 0 := by decide +kernel
      have ha : raw3431step2 = (fun i j => raw3431step1 (permutation8 i.succ) j) := by apply Matrix.ext; unfold raw3431step2 raw3431step1; decide +kernel
      have hl : raw3431step2Labels = raw3431step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3431step1 raw3431step1Labels permutation8 hz
    mixedMoment B raw3431step2 raw3431step2Labels = mixedMoment B raw3431step3 raw3431step3Labels := by
      have hz : ∀ i, raw3431step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3431step3 = (fun i j => raw3431step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3431step3 raw3431step2; decide +kernel
      have hl : raw3431step3Labels = (fun j => raw3431step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3431step2 raw3431step2Labels permutation6 hz
    _ = mixedMoment B node4093 node4093Labels := by rfl

theorem canonical3432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3432 raw3432Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw3432 raw3432Labels = mixedMoment B raw3432step0 raw3432step0Labels := by
      have hz : ∀ j, raw3432 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3432step0 = (fun i j => raw3432 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3432step0 raw3432; decide +kernel
      have hl : raw3432step0Labels = raw3432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3432 raw3432Labels permutation434 hz
    mixedMoment B raw3432step0 raw3432step0Labels = mixedMoment B raw3432step1 raw3432step1Labels := by
      have hz : ∀ j, raw3432step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw3432step1 = (fun i j => raw3432step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw3432step1 raw3432step0; decide +kernel
      have hl : raw3432step1Labels = raw3432step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3432step0 raw3432step0Labels permutation32 hz
    mixedMoment B raw3432step1 raw3432step1Labels = mixedMoment B raw3432step2 raw3432step2Labels := by
      have hz : ∀ i, raw3432step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3432step2 = (fun i j => raw3432step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3432step2 raw3432step1; decide +kernel
      have hl : raw3432step2Labels = (fun j => raw3432step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3432step1 raw3432step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

theorem canonical3433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3433 raw3433Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw3433 raw3433Labels = mixedMoment B raw3433step0 raw3433step0Labels := by
      have hz : ∀ j, raw3433 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3433step0 = (fun i j => raw3433 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3433step0 raw3433; decide +kernel
      have hl : raw3433step0Labels = raw3433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3433 raw3433Labels permutation346 hz
    mixedMoment B raw3433step0 raw3433step0Labels = mixedMoment B raw3433step1 raw3433step1Labels := by
      have hz : ∀ j, raw3433step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw3433step1 = (fun i j => raw3433step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw3433step1 raw3433step0; decide +kernel
      have hl : raw3433step1Labels = raw3433step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3433step0 raw3433step0Labels permutation32 hz
    mixedMoment B raw3433step1 raw3433step1Labels = mixedMoment B raw3433step2 raw3433step2Labels := by
      have hz : ∀ i, raw3433step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3433step2 = (fun i j => raw3433step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3433step2 raw3433step1; decide +kernel
      have hl : raw3433step2Labels = (fun j => raw3433step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3433step1 raw3433step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

theorem canonical3434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3434 raw3434Labels = mixedMoment B node4097 node4097Labels := by
  calc
    mixedMoment B raw3434 raw3434Labels = mixedMoment B raw3434step0 raw3434step0Labels := by
      have hz : ∀ j, raw3434 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3434step0 = (fun i j => raw3434 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3434step0 raw3434; decide +kernel
      have hl : raw3434step0Labels = raw3434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3434 raw3434Labels permutation520 hz
    mixedMoment B raw3434step0 raw3434step0Labels = mixedMoment B raw3434step1 raw3434step1Labels := by
      have hz : ∀ j, raw3434step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3434step1 = (fun i j => raw3434step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3434step1 raw3434step0; decide +kernel
      have hl : raw3434step1Labels = raw3434step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3434step0 raw3434step0Labels permutation104 hz
    mixedMoment B raw3434step1 raw3434step1Labels = mixedMoment B raw3434step2 raw3434step2Labels := by
      have hz : ∀ j, raw3434step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3434step2 = (fun i j => raw3434step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3434step2 raw3434step1; decide +kernel
      have hl : raw3434step2Labels = raw3434step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3434step1 raw3434step1Labels permutation20 hz
    mixedMoment B raw3434step2 raw3434step2Labels = mixedMoment B raw3434step3 raw3434step3Labels := by
      have hz : ∀ j, raw3434step2 (permutation2 0) j = 0 := by decide +kernel
      have ha : raw3434step3 = (fun i j => raw3434step2 (permutation2 i.succ) j) := by apply Matrix.ext; unfold raw3434step3 raw3434step2; decide +kernel
      have hl : raw3434step3Labels = raw3434step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3434step2 raw3434step2Labels permutation2 hz
    mixedMoment B raw3434step3 raw3434step3Labels = mixedMoment B raw3434step4 raw3434step4Labels := by
      have hz : ∀ i, raw3434step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3434step4 = (fun i j => raw3434step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3434step4 raw3434step3; decide +kernel
      have hl : raw3434step4Labels = (fun j => raw3434step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3434step3 raw3434step3Labels permutation6 hz
    _ = mixedMoment B node4097 node4097Labels := by rfl

theorem canonical3435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3435 raw3435Labels = mixedMoment B node4097 node4097Labels := by
  calc
    mixedMoment B raw3435 raw3435Labels = mixedMoment B raw3435step0 raw3435step0Labels := by
      have hz : ∀ j, raw3435 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3435step0 = (fun i j => raw3435 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3435step0 raw3435; decide +kernel
      have hl : raw3435step0Labels = raw3435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3435 raw3435Labels permutation590 hz
    mixedMoment B raw3435step0 raw3435step0Labels = mixedMoment B raw3435step1 raw3435step1Labels := by
      have hz : ∀ j, raw3435step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3435step1 = (fun i j => raw3435step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3435step1 raw3435step0; decide +kernel
      have hl : raw3435step1Labels = raw3435step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3435step0 raw3435step0Labels permutation104 hz
    mixedMoment B raw3435step1 raw3435step1Labels = mixedMoment B raw3435step2 raw3435step2Labels := by
      have hz : ∀ j, raw3435step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3435step2 = (fun i j => raw3435step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3435step2 raw3435step1; decide +kernel
      have hl : raw3435step2Labels = raw3435step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3435step1 raw3435step1Labels permutation20 hz
    mixedMoment B raw3435step2 raw3435step2Labels = mixedMoment B raw3435step3 raw3435step3Labels := by
      have hz : ∀ j, raw3435step2 (permutation2 0) j = 0 := by decide +kernel
      have ha : raw3435step3 = (fun i j => raw3435step2 (permutation2 i.succ) j) := by apply Matrix.ext; unfold raw3435step3 raw3435step2; decide +kernel
      have hl : raw3435step3Labels = raw3435step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3435step2 raw3435step2Labels permutation2 hz
    mixedMoment B raw3435step3 raw3435step3Labels = mixedMoment B raw3435step4 raw3435step4Labels := by
      have hz : ∀ i, raw3435step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3435step4 = (fun i j => raw3435step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3435step4 raw3435step3; decide +kernel
      have hl : raw3435step4Labels = (fun j => raw3435step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3435step3 raw3435step3Labels permutation6 hz
    _ = mixedMoment B node4097 node4097Labels := by rfl

theorem canonical3436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3436 raw3436Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3436 raw3436Labels = mixedMoment B raw3436step0 raw3436step0Labels := by
      have hz : ∀ j, raw3436 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3436step0 = (fun i j => raw3436 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3436step0 raw3436; decide +kernel
      have hl : raw3436step0Labels = raw3436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3436 raw3436Labels permutation434 hz
    mixedMoment B raw3436step0 raw3436step0Labels = mixedMoment B raw3436step1 raw3436step1Labels := by
      have hz : ∀ i, raw3436step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3436step1 = (fun i j => raw3436step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3436step1 raw3436step0; decide +kernel
      have hl : raw3436step1Labels = (fun j => raw3436step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3436step0 raw3436step0Labels permutation6 hz
    mixedMoment B raw3436step1 raw3436step1Labels = mixedMoment B raw3436step2 raw3436step2Labels := by
      have ha : raw3436step2 = (fun i j => raw3436step1 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3436step2 raw3436step1; decide +kernel
      have hl : raw3436step2Labels = raw3436step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3436step1 raw3436step1Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical3437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3437 raw3437Labels = mixedMoment B node4095 node4095Labels := by
  calc
    mixedMoment B raw3437 raw3437Labels = mixedMoment B raw3437step0 raw3437step0Labels := by
      have hz : ∀ i, raw3437 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3437step0 = (fun i j => raw3437 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3437step0 raw3437; decide +kernel
      have hl : raw3437step0Labels = (fun j => raw3437Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3437 raw3437Labels permutation6 hz
    mixedMoment B raw3437step0 raw3437step0Labels = mixedMoment B raw3437step1 raw3437step1Labels := by
      have ha : raw3437step1 = (fun i j => raw3437step0 (permutation158 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3437step1 raw3437step0; decide +kernel
      have hl : raw3437step1Labels = raw3437step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3437step0 raw3437step0Labels permutation158 permutation0
    _ = mixedMoment B node4095 node4095Labels := by rfl

theorem canonical3438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3438 raw3438Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw3438 raw3438Labels = mixedMoment B raw3438step0 raw3438step0Labels := by
      have hz : ∀ j, raw3438 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3438step0 = (fun i j => raw3438 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3438step0 raw3438; decide +kernel
      have hl : raw3438step0Labels = raw3438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3438 raw3438Labels permutation520 hz
    mixedMoment B raw3438step0 raw3438step0Labels = mixedMoment B raw3438step1 raw3438step1Labels := by
      have hz : ∀ j, raw3438step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3438step1 = (fun i j => raw3438step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3438step1 raw3438step0; decide +kernel
      have hl : raw3438step1Labels = raw3438step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3438step0 raw3438step0Labels permutation104 hz
    mixedMoment B raw3438step1 raw3438step1Labels = mixedMoment B raw3438step2 raw3438step2Labels := by
      have hz : ∀ i, raw3438step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3438step2 = (fun i j => raw3438step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3438step2 raw3438step1; decide +kernel
      have hl : raw3438step2Labels = (fun j => raw3438step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3438step1 raw3438step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

theorem canonical3439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3439 raw3439Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw3439 raw3439Labels = mixedMoment B raw3439step0 raw3439step0Labels := by
      have hz : ∀ j, raw3439 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3439step0 = (fun i j => raw3439 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3439step0 raw3439; decide +kernel
      have hl : raw3439step0Labels = raw3439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3439 raw3439Labels permutation590 hz
    mixedMoment B raw3439step0 raw3439step0Labels = mixedMoment B raw3439step1 raw3439step1Labels := by
      have hz : ∀ j, raw3439step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3439step1 = (fun i j => raw3439step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3439step1 raw3439step0; decide +kernel
      have hl : raw3439step1Labels = raw3439step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3439step0 raw3439step0Labels permutation104 hz
    mixedMoment B raw3439step1 raw3439step1Labels = mixedMoment B raw3439step2 raw3439step2Labels := by
      have hz : ∀ i, raw3439step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3439step2 = (fun i j => raw3439step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3439step2 raw3439step1; decide +kernel
      have hl : raw3439step2Labels = (fun j => raw3439step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3439step1 raw3439step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

theorem canonical3440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3440 raw3440Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3440 raw3440Labels = mixedMoment B raw3440step0 raw3440step0Labels := by
      have hz : ∀ j, raw3440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3440step0 = (fun i j => raw3440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3440step0 raw3440; decide +kernel
      have hl : raw3440step0Labels = raw3440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3440 raw3440Labels permutation346 hz
    mixedMoment B raw3440step0 raw3440step0Labels = mixedMoment B raw3440step1 raw3440step1Labels := by
      have hz : ∀ i, raw3440step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3440step1 = (fun i j => raw3440step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3440step1 raw3440step0; decide +kernel
      have hl : raw3440step1Labels = (fun j => raw3440step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3440step0 raw3440step0Labels permutation6 hz
    mixedMoment B raw3440step1 raw3440step1Labels = mixedMoment B raw3440step2 raw3440step2Labels := by
      have ha : raw3440step2 = (fun i j => raw3440step1 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3440step2 raw3440step1; decide +kernel
      have hl : raw3440step2Labels = raw3440step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3440step1 raw3440step1Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical3441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3441 raw3441Labels = mixedMoment B node4095 node4095Labels := by
  calc
    mixedMoment B raw3441 raw3441Labels = mixedMoment B raw3441step0 raw3441step0Labels := by
      have hz : ∀ i, raw3441 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3441step0 = (fun i j => raw3441 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3441step0 raw3441; decide +kernel
      have hl : raw3441step0Labels = (fun j => raw3441Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3441 raw3441Labels permutation6 hz
    _ = mixedMoment B node4095 node4095Labels := by rfl

theorem canonical3442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3442 raw3442Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw3442 raw3442Labels = mixedMoment B raw3442step0 raw3442step0Labels := by
      have hz : ∀ j, raw3442 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3442step0 = (fun i j => raw3442 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3442step0 raw3442; decide +kernel
      have hl : raw3442step0Labels = raw3442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3442 raw3442Labels permutation520 hz
    mixedMoment B raw3442step0 raw3442step0Labels = mixedMoment B raw3442step1 raw3442step1Labels := by
      have hz : ∀ j, raw3442step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3442step1 = (fun i j => raw3442step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3442step1 raw3442step0; decide +kernel
      have hl : raw3442step1Labels = raw3442step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3442step0 raw3442step0Labels permutation80 hz
    mixedMoment B raw3442step1 raw3442step1Labels = mixedMoment B raw3442step2 raw3442step2Labels := by
      have hz : ∀ i, raw3442step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3442step2 = (fun i j => raw3442step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3442step2 raw3442step1; decide +kernel
      have hl : raw3442step2Labels = (fun j => raw3442step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3442step1 raw3442step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

theorem canonical3443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3443 raw3443Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw3443 raw3443Labels = mixedMoment B raw3443step0 raw3443step0Labels := by
      have hz : ∀ j, raw3443 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3443step0 = (fun i j => raw3443 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3443step0 raw3443; decide +kernel
      have hl : raw3443step0Labels = raw3443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3443 raw3443Labels permutation590 hz
    mixedMoment B raw3443step0 raw3443step0Labels = mixedMoment B raw3443step1 raw3443step1Labels := by
      have hz : ∀ j, raw3443step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3443step1 = (fun i j => raw3443step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3443step1 raw3443step0; decide +kernel
      have hl : raw3443step1Labels = raw3443step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3443step0 raw3443step0Labels permutation80 hz
    mixedMoment B raw3443step1 raw3443step1Labels = mixedMoment B raw3443step2 raw3443step2Labels := by
      have hz : ∀ i, raw3443step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3443step2 = (fun i j => raw3443step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3443step2 raw3443step1; decide +kernel
      have hl : raw3443step2Labels = (fun j => raw3443step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3443step1 raw3443step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

theorem canonical3444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3444 raw3444Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw3444 raw3444Labels = mixedMoment B raw3444step0 raw3444step0Labels := by
      have hz : ∀ j, raw3444 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3444step0 = (fun i j => raw3444 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3444step0 raw3444; decide +kernel
      have hl : raw3444step0Labels = raw3444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3444 raw3444Labels permutation434 hz
    mixedMoment B raw3444step0 raw3444step0Labels = mixedMoment B raw3444step1 raw3444step1Labels := by
      have hz : ∀ j, raw3444step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3444step1 = (fun i j => raw3444step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3444step1 raw3444step0; decide +kernel
      have hl : raw3444step1Labels = raw3444step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3444step0 raw3444step0Labels permutation80 hz
    mixedMoment B raw3444step1 raw3444step1Labels = mixedMoment B raw3444step2 raw3444step2Labels := by
      have hz : ∀ i, raw3444step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3444step2 = (fun i j => raw3444step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3444step2 raw3444step1; decide +kernel
      have hl : raw3444step2Labels = (fun j => raw3444step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3444step1 raw3444step1Labels permutation6 hz
    mixedMoment B raw3444step2 raw3444step2Labels = mixedMoment B raw3444step3 raw3444step3Labels := by
      have ha : raw3444step3 = (fun i j => raw3444step2 (permutation15 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3444step3 raw3444step2; decide +kernel
      have hl : raw3444step3Labels = raw3444step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3444step2 raw3444step2Labels permutation15 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical3445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3445 raw3445Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3445 raw3445Labels = mixedMoment B raw3445step0 raw3445step0Labels := by
      have hz : ∀ j, raw3445 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3445step0 = (fun i j => raw3445 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3445step0 raw3445; decide +kernel
      have hl : raw3445step0Labels = raw3445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3445 raw3445Labels permutation434 hz
    mixedMoment B raw3445step0 raw3445step0Labels = mixedMoment B raw3445step1 raw3445step1Labels := by
      have hz : ∀ i, raw3445step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3445step1 = (fun i j => raw3445step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3445step1 raw3445step0; decide +kernel
      have hl : raw3445step1Labels = (fun j => raw3445step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3445step0 raw3445step0Labels permutation6 hz
    mixedMoment B raw3445step1 raw3445step1Labels = mixedMoment B raw3445step2 raw3445step2Labels := by
      have ha : raw3445step2 = (fun i j => raw3445step1 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3445step2 raw3445step1; decide +kernel
      have hl : raw3445step2Labels = raw3445step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3445step1 raw3445step1Labels permutation122 permutation0
    mixedMoment B raw3445step2 raw3445step2Labels = mixedMoment B raw3445step3 raw3445step3Labels := by
      have ha : raw3445step3 = -raw3445step2 := by apply Matrix.ext; change ∀ i j, raw3445step3 i j = -(raw3445step2 i j); unfold raw3445step3 raw3445step2; decide +kernel
      have hl : raw3445step3Labels = raw3445step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical3446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3446 raw3446Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3446 raw3446Labels = mixedMoment B raw3446step0 raw3446step0Labels := by
      have hz : ∀ j, raw3446 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3446step0 = (fun i j => raw3446 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3446step0 raw3446; decide +kernel
      have hl : raw3446step0Labels = raw3446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3446 raw3446Labels permutation346 hz
    mixedMoment B raw3446step0 raw3446step0Labels = mixedMoment B raw3446step1 raw3446step1Labels := by
      have hz : ∀ i, raw3446step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3446step1 = (fun i j => raw3446step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3446step1 raw3446step0; decide +kernel
      have hl : raw3446step1Labels = (fun j => raw3446step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3446step0 raw3446step0Labels permutation6 hz
    mixedMoment B raw3446step1 raw3446step1Labels = mixedMoment B raw3446step2 raw3446step2Labels := by
      have ha : raw3446step2 = (fun i j => raw3446step1 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3446step2 raw3446step1; decide +kernel
      have hl : raw3446step2Labels = raw3446step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3446step1 raw3446step1Labels permutation122 permutation0
    mixedMoment B raw3446step2 raw3446step2Labels = mixedMoment B raw3446step3 raw3446step3Labels := by
      have ha : raw3446step3 = -raw3446step2 := by apply Matrix.ext; change ∀ i j, raw3446step3 i j = -(raw3446step2 i j); unfold raw3446step3 raw3446step2; decide +kernel
      have hl : raw3446step3Labels = raw3446step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical3447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3447 raw3447Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw3447 raw3447Labels = mixedMoment B raw3447step0 raw3447step0Labels := by
      have hz : ∀ j, raw3447 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3447step0 = (fun i j => raw3447 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3447step0 raw3447; decide +kernel
      have hl : raw3447step0Labels = raw3447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3447 raw3447Labels permutation590 hz
    mixedMoment B raw3447step0 raw3447step0Labels = mixedMoment B raw3447step1 raw3447step1Labels := by
      have hz : ∀ j, raw3447step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3447step1 = (fun i j => raw3447step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3447step1 raw3447step0; decide +kernel
      have hl : raw3447step1Labels = raw3447step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3447step0 raw3447step0Labels permutation104 hz
    mixedMoment B raw3447step1 raw3447step1Labels = mixedMoment B raw3447step2 raw3447step2Labels := by
      have hz : ∀ j, raw3447step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3447step2 = (fun i j => raw3447step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3447step2 raw3447step1; decide +kernel
      have hl : raw3447step2Labels = raw3447step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3447step1 raw3447step1Labels permutation20 hz
    mixedMoment B raw3447step2 raw3447step2Labels = mixedMoment B raw3447step3 raw3447step3Labels := by
      have hz : ∀ i, raw3447step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3447step3 = (fun i j => raw3447step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3447step3 raw3447step2; decide +kernel
      have hl : raw3447step3Labels = (fun j => raw3447step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3447step2 raw3447step2Labels permutation6 hz
    mixedMoment B raw3447step3 raw3447step3Labels = mixedMoment B raw3447step4 raw3447step4Labels := by
      have ha : raw3447step4 = (fun i j => raw3447step3 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3447step4 raw3447step3; decide +kernel
      have hl : raw3447step4Labels = raw3447step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3447step3 raw3447step3Labels permutation6 permutation0
    mixedMoment B raw3447step4 raw3447step4Labels = mixedMoment B raw3447step5 raw3447step5Labels := by
      have ha : raw3447step5 = -raw3447step4 := by apply Matrix.ext; change ∀ i j, raw3447step5 i j = -(raw3447step4 i j); unfold raw3447step5 raw3447step4; decide +kernel
      have hl : raw3447step5Labels = raw3447step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4093 node4093Labels := by rfl

theorem canonical3448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3448 raw3448Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw3448 raw3448Labels = mixedMoment B raw3448step0 raw3448step0Labels := by
      have hz : ∀ j, raw3448 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3448step0 = (fun i j => raw3448 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3448step0 raw3448; decide +kernel
      have hl : raw3448step0Labels = raw3448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3448 raw3448Labels permutation434 hz
    mixedMoment B raw3448step0 raw3448step0Labels = mixedMoment B raw3448step1 raw3448step1Labels := by
      have hz : ∀ j, raw3448step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3448step1 = (fun i j => raw3448step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3448step1 raw3448step0; decide +kernel
      have hl : raw3448step1Labels = raw3448step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3448step0 raw3448step0Labels permutation80 hz
    mixedMoment B raw3448step1 raw3448step1Labels = mixedMoment B raw3448step2 raw3448step2Labels := by
      have hz : ∀ i, raw3448step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3448step2 = (fun i j => raw3448step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3448step2 raw3448step1; decide +kernel
      have hl : raw3448step2Labels = (fun j => raw3448step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3448step1 raw3448step1Labels permutation6 hz
    mixedMoment B raw3448step2 raw3448step2Labels = mixedMoment B raw3448step3 raw3448step3Labels := by
      have ha : raw3448step3 = (fun i j => raw3448step2 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3448step3 raw3448step2; decide +kernel
      have hl : raw3448step3Labels = raw3448step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3448step2 raw3448step2Labels permutation14 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical3449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3449 raw3449Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3449 raw3449Labels = mixedMoment B raw3449step0 raw3449step0Labels := by
      have hz : ∀ j, raw3449 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3449step0 = (fun i j => raw3449 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3449step0 raw3449; decide +kernel
      have hl : raw3449step0Labels = raw3449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3449 raw3449Labels permutation434 hz
    mixedMoment B raw3449step0 raw3449step0Labels = mixedMoment B raw3449step1 raw3449step1Labels := by
      have hz : ∀ i, raw3449step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3449step1 = (fun i j => raw3449step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3449step1 raw3449step0; decide +kernel
      have hl : raw3449step1Labels = (fun j => raw3449step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3449step0 raw3449step0Labels permutation6 hz
    mixedMoment B raw3449step1 raw3449step1Labels = mixedMoment B raw3449step2 raw3449step2Labels := by
      have ha : raw3449step2 = (fun i j => raw3449step1 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3449step2 raw3449step1; decide +kernel
      have hl : raw3449step2Labels = raw3449step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3449step1 raw3449step1Labels permutation146 permutation0
    mixedMoment B raw3449step2 raw3449step2Labels = mixedMoment B raw3449step3 raw3449step3Labels := by
      have ha : raw3449step3 = -raw3449step2 := by apply Matrix.ext; change ∀ i j, raw3449step3 i j = -(raw3449step2 i j); unfold raw3449step3 raw3449step2; decide +kernel
      have hl : raw3449step3Labels = raw3449step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical3450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3450 raw3450Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3450 raw3450Labels = mixedMoment B raw3450step0 raw3450step0Labels := by
      have hz : ∀ j, raw3450 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3450step0 = (fun i j => raw3450 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3450step0 raw3450; decide +kernel
      have hl : raw3450step0Labels = raw3450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3450 raw3450Labels permutation346 hz
    mixedMoment B raw3450step0 raw3450step0Labels = mixedMoment B raw3450step1 raw3450step1Labels := by
      have hz : ∀ i, raw3450step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3450step1 = (fun i j => raw3450step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3450step1 raw3450step0; decide +kernel
      have hl : raw3450step1Labels = (fun j => raw3450step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3450step0 raw3450step0Labels permutation6 hz
    mixedMoment B raw3450step1 raw3450step1Labels = mixedMoment B raw3450step2 raw3450step2Labels := by
      have ha : raw3450step2 = (fun i j => raw3450step1 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3450step2 raw3450step1; decide +kernel
      have hl : raw3450step2Labels = raw3450step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3450step1 raw3450step1Labels permutation146 permutation0
    mixedMoment B raw3450step2 raw3450step2Labels = mixedMoment B raw3450step3 raw3450step3Labels := by
      have ha : raw3450step3 = -raw3450step2 := by apply Matrix.ext; change ∀ i j, raw3450step3 i j = -(raw3450step2 i j); unfold raw3450step3 raw3450step2; decide +kernel
      have hl : raw3450step3Labels = raw3450step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

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

theorem canonical3511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3511 raw3511Labels = mixedMoment B node2285 node2285Labels := by
  calc
    mixedMoment B raw3511 raw3511Labels = mixedMoment B raw3511step0 raw3511step0Labels := by
      have hz : ∀ j, raw3511 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3511step0 = (fun i j => raw3511 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3511step0 raw3511; decide +kernel
      have hl : raw3511step0Labels = raw3511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3511 raw3511Labels permutation434 hz
    mixedMoment B raw3511step0 raw3511step0Labels = mixedMoment B raw3511step1 raw3511step1Labels := by
      have hz : ∀ j, raw3511step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3511step1 = (fun i j => raw3511step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3511step1 raw3511step0; decide +kernel
      have hl : raw3511step1Labels = raw3511step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3511step0 raw3511step0Labels permutation80 hz
    mixedMoment B raw3511step1 raw3511step1Labels = mixedMoment B raw3511step2 raw3511step2Labels := by
      have hz : ∀ j, raw3511step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3511step2 = (fun i j => raw3511step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3511step2 raw3511step1; decide +kernel
      have hl : raw3511step2Labels = raw3511step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3511step1 raw3511step1Labels permutation14 hz
    _ = mixedMoment B node2285 node2285Labels := by rfl

theorem canonical3512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3512 raw3512Labels = mixedMoment B node2063 node2063Labels := by
  calc
    mixedMoment B raw3512 raw3512Labels = mixedMoment B raw3512step0 raw3512step0Labels := by
      have hz : ∀ j, raw3512 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3512step0 = (fun i j => raw3512 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3512step0 raw3512; decide +kernel
      have hl : raw3512step0Labels = raw3512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3512 raw3512Labels permutation434 hz
    mixedMoment B raw3512step0 raw3512step0Labels = mixedMoment B raw3512step1 raw3512step1Labels := by
      have hz : ∀ j, raw3512step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3512step1 = (fun i j => raw3512step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3512step1 raw3512step0; decide +kernel
      have hl : raw3512step1Labels = raw3512step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3512step0 raw3512step0Labels permutation80 hz
    mixedMoment B raw3512step1 raw3512step1Labels = mixedMoment B raw3512step2 raw3512step2Labels := by
      have ha : raw3512step2 = (fun i j => raw3512step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3512step2 raw3512step1; decide +kernel
      have hl : raw3512step2Labels = raw3512step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3512step1 raw3512step1Labels permutation22 permutation4
    mixedMoment B raw3512step2 raw3512step2Labels = mixedMoment B raw3512step3 raw3512step3Labels := by
      have ha : raw3512step3 = -raw3512step2 := by apply Matrix.ext; change ∀ i j, raw3512step3 i j = -(raw3512step2 i j); unfold raw3512step3 raw3512step2; decide +kernel
      have hl : raw3512step3Labels = raw3512step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2063 node2063Labels := by rfl

theorem canonical3513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3513 raw3513Labels = mixedMoment B node2063 node2063Labels := by
  calc
    mixedMoment B raw3513 raw3513Labels = mixedMoment B raw3513step0 raw3513step0Labels := by
      have hz : ∀ j, raw3513 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3513step0 = (fun i j => raw3513 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3513step0 raw3513; decide +kernel
      have hl : raw3513step0Labels = raw3513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3513 raw3513Labels permutation434 hz
    mixedMoment B raw3513step0 raw3513step0Labels = mixedMoment B raw3513step1 raw3513step1Labels := by
      have hz : ∀ j, raw3513step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3513step1 = (fun i j => raw3513step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3513step1 raw3513step0; decide +kernel
      have hl : raw3513step1Labels = raw3513step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3513step0 raw3513step0Labels permutation56 hz
    mixedMoment B raw3513step1 raw3513step1Labels = mixedMoment B raw3513step2 raw3513step2Labels := by
      have ha : raw3513step2 = (fun i j => raw3513step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3513step2 raw3513step1; decide +kernel
      have hl : raw3513step2Labels = raw3513step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3513step1 raw3513step1Labels permutation22 permutation4
    mixedMoment B raw3513step2 raw3513step2Labels = mixedMoment B raw3513step3 raw3513step3Labels := by
      have ha : raw3513step3 = -raw3513step2 := by apply Matrix.ext; change ∀ i j, raw3513step3 i j = -(raw3513step2 i j); unfold raw3513step3 raw3513step2; decide +kernel
      have hl : raw3513step3Labels = raw3513step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2063 node2063Labels := by rfl

theorem canonical3514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3514 raw3514Labels = mixedMoment B node2063 node2063Labels := by
  calc
    mixedMoment B raw3514 raw3514Labels = mixedMoment B raw3514step0 raw3514step0Labels := by
      have hz : ∀ j, raw3514 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3514step0 = (fun i j => raw3514 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3514step0 raw3514; decide +kernel
      have hl : raw3514step0Labels = raw3514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3514 raw3514Labels permutation346 hz
    mixedMoment B raw3514step0 raw3514step0Labels = mixedMoment B raw3514step1 raw3514step1Labels := by
      have hz : ∀ j, raw3514step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3514step1 = (fun i j => raw3514step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3514step1 raw3514step0; decide +kernel
      have hl : raw3514step1Labels = raw3514step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3514step0 raw3514step0Labels permutation56 hz
    mixedMoment B raw3514step1 raw3514step1Labels = mixedMoment B raw3514step2 raw3514step2Labels := by
      have ha : raw3514step2 = (fun i j => raw3514step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3514step2 raw3514step1; decide +kernel
      have hl : raw3514step2Labels = raw3514step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3514step1 raw3514step1Labels permutation22 permutation4
    mixedMoment B raw3514step2 raw3514step2Labels = mixedMoment B raw3514step3 raw3514step3Labels := by
      have ha : raw3514step3 = -raw3514step2 := by apply Matrix.ext; change ∀ i j, raw3514step3 i j = -(raw3514step2 i j); unfold raw3514step3 raw3514step2; decide +kernel
      have hl : raw3514step3Labels = raw3514step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2063 node2063Labels := by rfl

theorem canonical3515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3515 raw3515Labels = mixedMoment B node1092 node1092Labels := by
  calc
    mixedMoment B raw3515 raw3515Labels = mixedMoment B raw3515step0 raw3515step0Labels := by
      have hz : ∀ j, raw3515 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3515step0 = (fun i j => raw3515 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3515step0 raw3515; decide +kernel
      have hl : raw3515step0Labels = raw3515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3515 raw3515Labels permutation434 hz
    mixedMoment B raw3515step0 raw3515step0Labels = mixedMoment B raw3515step1 raw3515step1Labels := by
      have hz : ∀ j, raw3515step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3515step1 = (fun i j => raw3515step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3515step1 raw3515step0; decide +kernel
      have hl : raw3515step1Labels = raw3515step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3515step0 raw3515step0Labels permutation80 hz
    mixedMoment B raw3515step1 raw3515step1Labels = mixedMoment B raw3515step2 raw3515step2Labels := by
      have hz : ∀ j, raw3515step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3515step2 = (fun i j => raw3515step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3515step2 raw3515step1; decide +kernel
      have hl : raw3515step2Labels = raw3515step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3515step1 raw3515step1Labels permutation14 hz
    mixedMoment B raw3515step2 raw3515step2Labels = mixedMoment B raw3515step3 raw3515step3Labels := by
      have ha : raw3515step3 = (fun i j => raw3515step2 (permutation4 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3515step3 raw3515step2; decide +kernel
      have hl : raw3515step3Labels = raw3515step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3515step2 raw3515step2Labels permutation4 permutation4
    mixedMoment B raw3515step3 raw3515step3Labels = mixedMoment B raw3515step4 raw3515step4Labels := by
      have ha : raw3515step4 = -raw3515step3 := by apply Matrix.ext; change ∀ i j, raw3515step4 i j = -(raw3515step3 i j); unfold raw3515step4 raw3515step3; decide +kernel
      have hl : raw3515step4Labels = raw3515step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1092 node1092Labels := by rfl

theorem canonical3516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3516 raw3516Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw3516 raw3516Labels = mixedMoment B raw3516step0 raw3516step0Labels := by
      have hz : ∀ j, raw3516 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3516step0 = (fun i j => raw3516 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3516step0 raw3516; decide +kernel
      have hl : raw3516step0Labels = raw3516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3516 raw3516Labels permutation434 hz
    mixedMoment B raw3516step0 raw3516step0Labels = mixedMoment B raw3516step1 raw3516step1Labels := by
      have hz : ∀ j, raw3516step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3516step1 = (fun i j => raw3516step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3516step1 raw3516step0; decide +kernel
      have hl : raw3516step1Labels = raw3516step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3516step0 raw3516step0Labels permutation80 hz
    mixedMoment B raw3516step1 raw3516step1Labels = mixedMoment B raw3516step2 raw3516step2Labels := by
      have hz : ∀ j, raw3516step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3516step2 = (fun i j => raw3516step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3516step2 raw3516step1; decide +kernel
      have hl : raw3516step2Labels = raw3516step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3516step1 raw3516step1Labels permutation14 hz
    mixedMoment B raw3516step2 raw3516step2Labels = mixedMoment B raw3516step3 raw3516step3Labels := by
      have ha : raw3516step3 = (fun i j => raw3516step2 (permutation4 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3516step3 raw3516step2; decide +kernel
      have hl : raw3516step3Labels = raw3516step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3516step2 raw3516step2Labels permutation4 permutation4
    mixedMoment B raw3516step3 raw3516step3Labels = mixedMoment B raw3516step4 raw3516step4Labels := by
      have ha : raw3516step4 = -raw3516step3 := by apply Matrix.ext; change ∀ i j, raw3516step4 i j = -(raw3516step3 i j); unfold raw3516step4 raw3516step3; decide +kernel
      have hl : raw3516step4Labels = raw3516step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2294 node2294Labels := by rfl

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

theorem canonical3518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3518 raw3518Labels = mixedMoment B node1067 node1067Labels := by
  calc
    mixedMoment B raw3518 raw3518Labels = mixedMoment B raw3518step0 raw3518step0Labels := by
      have hz : ∀ j, raw3518 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3518step0 = (fun i j => raw3518 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3518step0 raw3518; decide +kernel
      have hl : raw3518step0Labels = raw3518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3518 raw3518Labels permutation434 hz
    mixedMoment B raw3518step0 raw3518step0Labels = mixedMoment B raw3518step1 raw3518step1Labels := by
      have hz : ∀ j, raw3518step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3518step1 = (fun i j => raw3518step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3518step1 raw3518step0; decide +kernel
      have hl : raw3518step1Labels = raw3518step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3518step0 raw3518step0Labels permutation80 hz
    mixedMoment B raw3518step1 raw3518step1Labels = mixedMoment B raw3518step2 raw3518step2Labels := by
      have ha : raw3518step2 = (fun i j => raw3518step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3518step2 raw3518step1; decide +kernel
      have hl : raw3518step2Labels = raw3518step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3518step1 raw3518step1Labels permutation10 permutation2
    _ = mixedMoment B node1067 node1067Labels := by rfl

theorem canonical3519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3519 raw3519Labels = mixedMoment B node1067 node1067Labels := by
  calc
    mixedMoment B raw3519 raw3519Labels = mixedMoment B raw3519step0 raw3519step0Labels := by
      have hz : ∀ j, raw3519 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3519step0 = (fun i j => raw3519 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3519step0 raw3519; decide +kernel
      have hl : raw3519step0Labels = raw3519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3519 raw3519Labels permutation434 hz
    mixedMoment B raw3519step0 raw3519step0Labels = mixedMoment B raw3519step1 raw3519step1Labels := by
      have hz : ∀ j, raw3519step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3519step1 = (fun i j => raw3519step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3519step1 raw3519step0; decide +kernel
      have hl : raw3519step1Labels = raw3519step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3519step0 raw3519step0Labels permutation56 hz
    mixedMoment B raw3519step1 raw3519step1Labels = mixedMoment B raw3519step2 raw3519step2Labels := by
      have ha : raw3519step2 = (fun i j => raw3519step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3519step2 raw3519step1; decide +kernel
      have hl : raw3519step2Labels = raw3519step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3519step1 raw3519step1Labels permutation10 permutation2
    _ = mixedMoment B node1067 node1067Labels := by rfl

theorem canonical3520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3520 raw3520Labels = mixedMoment B node1067 node1067Labels := by
  calc
    mixedMoment B raw3520 raw3520Labels = mixedMoment B raw3520step0 raw3520step0Labels := by
      have hz : ∀ j, raw3520 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3520step0 = (fun i j => raw3520 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3520step0 raw3520; decide +kernel
      have hl : raw3520step0Labels = raw3520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3520 raw3520Labels permutation346 hz
    mixedMoment B raw3520step0 raw3520step0Labels = mixedMoment B raw3520step1 raw3520step1Labels := by
      have hz : ∀ j, raw3520step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3520step1 = (fun i j => raw3520step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3520step1 raw3520step0; decide +kernel
      have hl : raw3520step1Labels = raw3520step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3520step0 raw3520step0Labels permutation56 hz
    mixedMoment B raw3520step1 raw3520step1Labels = mixedMoment B raw3520step2 raw3520step2Labels := by
      have ha : raw3520step2 = (fun i j => raw3520step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3520step2 raw3520step1; decide +kernel
      have hl : raw3520step2Labels = raw3520step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3520step1 raw3520step1Labels permutation10 permutation2
    _ = mixedMoment B node1067 node1067Labels := by rfl

theorem canonical3521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3521 raw3521Labels = mixedMoment B node1092 node1092Labels := by
  calc
    mixedMoment B raw3521 raw3521Labels = mixedMoment B raw3521step0 raw3521step0Labels := by
      have hz : ∀ j, raw3521 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3521step0 = (fun i j => raw3521 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3521step0 raw3521; decide +kernel
      have hl : raw3521step0Labels = raw3521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3521 raw3521Labels permutation434 hz
    mixedMoment B raw3521step0 raw3521step0Labels = mixedMoment B raw3521step1 raw3521step1Labels := by
      have hz : ∀ j, raw3521step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3521step1 = (fun i j => raw3521step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3521step1 raw3521step0; decide +kernel
      have hl : raw3521step1Labels = raw3521step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3521step0 raw3521step0Labels permutation80 hz
    mixedMoment B raw3521step1 raw3521step1Labels = mixedMoment B raw3521step2 raw3521step2Labels := by
      have hz : ∀ j, raw3521step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3521step2 = (fun i j => raw3521step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3521step2 raw3521step1; decide +kernel
      have hl : raw3521step2Labels = raw3521step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3521step1 raw3521step1Labels permutation14 hz
    _ = mixedMoment B node1092 node1092Labels := by rfl

theorem canonical3522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3522 raw3522Labels = mixedMoment B node1069 node1069Labels := by
  calc
    mixedMoment B raw3522 raw3522Labels = mixedMoment B raw3522step0 raw3522step0Labels := by
      have hz : ∀ j, raw3522 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3522step0 = (fun i j => raw3522 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3522step0 raw3522; decide +kernel
      have hl : raw3522step0Labels = raw3522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3522 raw3522Labels permutation434 hz
    mixedMoment B raw3522step0 raw3522step0Labels = mixedMoment B raw3522step1 raw3522step1Labels := by
      have hz : ∀ j, raw3522step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3522step1 = (fun i j => raw3522step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3522step1 raw3522step0; decide +kernel
      have hl : raw3522step1Labels = raw3522step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3522step0 raw3522step0Labels permutation80 hz
    mixedMoment B raw3522step1 raw3522step1Labels = mixedMoment B raw3522step2 raw3522step2Labels := by
      have hz : ∀ j, raw3522step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3522step2 = (fun i j => raw3522step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3522step2 raw3522step1; decide +kernel
      have hl : raw3522step2Labels = raw3522step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3522step1 raw3522step1Labels permutation14 hz
    _ = mixedMoment B node1069 node1069Labels := by rfl

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

theorem canonical660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw660 raw660Labels = mixedMoment B node4093 node4093Labels := by
  calc
    _ = mixedMoment B node4093 node4093Labels := by rfl

theorem canonical661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw661 raw661Labels = mixedMoment B node5 node5Labels := by
  calc
    _ = mixedMoment B node5 node5Labels := by rfl

theorem canonical662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw662 raw662Labels = mixedMoment B node4094 node4094Labels := by
  calc
    _ = mixedMoment B node4094 node4094Labels := by rfl

theorem canonical663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw663 raw663Labels = mixedMoment B node6 node6Labels := by
  calc
    _ = mixedMoment B node6 node6Labels := by rfl

theorem canonical664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw664 raw664Labels = mixedMoment B node4096 node4096Labels := by
  calc
    _ = mixedMoment B node4096 node4096Labels := by rfl

theorem canonical665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw665 raw665Labels = mixedMoment B node7 node7Labels := by
  calc
    _ = mixedMoment B node7 node7Labels := by rfl

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

theorem sum_fin_two {R : Type*} [AddCommMonoid R] (f : Fin 2 → R) :
    ∑ i, f i = f 0 + f 1 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

theorem sum_fin_six {R : Type*} [AddCommMonoid R] (f : Fin 6 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) = _
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

theorem groupedColumns_family2_0 {p : ℕ} (A : Matrix (Fin p) (Fin 2) ℤ) :
    groupedColumns A (EqualityPatterns.family2.label 0) =
      (fun i (_ : Fin 1) => A i 0 + A i 1) := by
  change groupedColumns A (fun _ : Fin 2 => (0 : Fin 1)) = _
  ext i b
  have hb : b = 0 := Subsingleton.elim _ _
  subst b
  simp [groupedColumns, Fin.sum_univ_succ]

theorem groupedColumns_family2_1 {p : ℕ} (A : Matrix (Fin p) (Fin 2) ℤ) :
    groupedColumns A (EqualityPatterns.family2.label 1) = A := by
  change groupedColumns A (fun j : Fin 2 => j) = _
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

/-- The two equality patterns for the sampled column indices. -/
theorem single_label_two {p : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (A : Matrix (Fin p) (Fin 2) ℤ) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      (1 / 6 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family2.label 0)) +
      (5 / 6 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family2.label 1)) := by
  have h := mixedMoment_single_label_partition B hB A
    EqualityPatterns.family2 EqualityPatterns.covers2
  rw [sum_fin_two] at h
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family2,
    EqualityPatterns.blocks2, Nat.descFactorial] at h
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7978 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7978 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7978 = injectiveMoment H raw7978step0 := by
      have hz : ∀ j, raw7978 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7978step0 = (fun i j => raw7978 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7978 permutation2 hz
    injectiveMoment H raw7978step0 = injectiveMoment H raw7978step1 := by
      have hz : ∀ j, raw7978step0 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7978step1 = (fun i j => raw7978step0 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7978step0 permutation0 hz
    injectiveMoment H raw7978step1 = injectiveMoment H raw7978step2 := by
      have hz : ∀ i, raw7978step1 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7978step2 = (fun i j => raw7978step1 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7978step1 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

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

theorem canonical7735 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7735 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7735 = injectiveMoment H raw7735step0 := by
      have hz : ∀ j, raw7735 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7735step0 = (fun i j => raw7735 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7735 permutation7 hz
    _ = injectiveMoment H node5 := by rfl

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

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Single5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5 node5Labels = Sparse.eval singlePairValue5 (familyPairVector B) := by
  have hp := single_label_two B hB node5
  have hl : node5Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node5 (EqualityPatterns.family2.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node5 (EqualityPatterns.family2.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family2_0]
      apply Matrix.ext
      unfold node5 PairSemantics.raw7979
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node5 (EqualityPatterns.family2.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node5 (EqualityPatterns.family2.label 1) = PairSemantics.raw5199 := by
      rw [groupedColumns_family2_1]
      apply Matrix.ext
      unfold node5 PairSemantics.raw5199
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5199 hH).trans (PairSemantics.sound11 hH)
  rw [hm0, hm1] at hp
  norm_num [singlePairValue5, PairSemantics.value0, PairSemantics.value11, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Single6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node6 node6Labels = Sparse.eval singlePairValue6 (familyPairVector B) := by
  have hp := single_label_two B hB node6
  have hl : node6Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node6 (EqualityPatterns.family2.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node6 (EqualityPatterns.family2.label 0) = PairSemantics.raw7978 := by
      rw [groupedColumns_family2_0]
      apply Matrix.ext; unfold node6 PairSemantics.raw7978; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7978 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node6 (EqualityPatterns.family2.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node6 (EqualityPatterns.family2.label 1) = PairSemantics.raw5210 := by
      rw [groupedColumns_family2_1]
      apply Matrix.ext; unfold node6 PairSemantics.raw5210; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5210 hH).trans (PairSemantics.sound4 hH)
  rw [hm0, hm1] at hp
  norm_num [singlePairValue6, PairSemantics.value0, PairSemantics.value4, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

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

theorem canonical7678 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7678 = injectiveMoment H node65 := by
  rfl

end MUB6.Certificate.PairSemantics

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

theorem canonical7709 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7709 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7709 = injectiveMoment H raw7709step0 := by
      have hz : ∀ j, raw7709 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw7709step0 = (fun i j => raw7709 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7709 permutation5 hz
    _ = injectiveMoment H node5 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound1
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound65 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node65 = Sparse.eval value65 (momentVector H) := by
  have heq : pivotMatrix65 = (fun u v => node65 (pivotPermutation65 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node65 = injectiveMoment H pivotMatrix65 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix65 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix65 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix65 (0 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (0 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix65 (1 : Fin 3)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (1 : Fin 3) = raw7709 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7709 hH).trans (sound5 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix65 (2 : Fin 3)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (2 : Fin 3) = raw7735 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7735 hH).trans (sound5 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node65 + (injectiveMoment H (mergeFirst pivotMatrix65 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix65 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix65 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value65, value11, value5, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Single7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node7 node7Labels = Sparse.eval singlePairValue7 (familyPairVector B) := by
  have hp := single_label_two B hB node7
  have hl : node7Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node7 (EqualityPatterns.family2.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node7 (EqualityPatterns.family2.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family2_0]
      apply Matrix.ext; unfold node7 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node7 (EqualityPatterns.family2.label 1)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node7 (EqualityPatterns.family2.label 1) = PairSemantics.raw7678 := by
      rw [groupedColumns_family2_1]
      apply Matrix.ext; unfold node7 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  rw [hm0, hm1] at hp
  norm_num [singlePairValue7, PairSemantics.value0, PairSemantics.value65, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4093 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4093 node4093Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node5 node5Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw660 singletonSmall4093
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4093) = raw660Labels := by decide +kernel
  rw [hl, canonical660 B hB] at h
  have hc0 : mixedMoment B raw660 (Fin.cases (0 : Fin 1) singletonSmall4093) =
      mixedMoment B node5 node5Labels := by
    have ha : raw660 = raw661 := by apply Matrix.ext; unfold raw660 raw661; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4093 = raw661Labels := by decide +kernel
    rw [ha, hj, canonical661 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton4094 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4094 node4094Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node6 node6Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw662 singletonSmall4094
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4094) = raw662Labels := by decide +kernel
  rw [hl, canonical662 B hB] at h
  have hc0 : mixedMoment B raw662 (Fin.cases (0 : Fin 1) singletonSmall4094) =
      mixedMoment B node6 node6Labels := by
    have ha : raw662 = raw663 := by apply Matrix.ext; unfold raw662 raw663; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4094 = raw663Labels := by decide +kernel
    rw [ha, hj, canonical663 B hB]
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

theorem singleton4096 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4096 node4096Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node7 node7Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw664 singletonSmall4096
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4096) = raw664Labels := by decide +kernel
  rw [hl, canonical664 B hB] at h
  have hc0 : mixedMoment B raw664 (Fin.cases (0 : Fin 1) singletonSmall4096) =
      mixedMoment B node7 node7Labels := by
    have ha : raw664 = raw665 := by apply Matrix.ext; unfold raw664 raw665; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4096 = raw665Labels := by decide +kernel
    rw [ha, hj, canonical665 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
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

theorem singleton5405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5405 node5405Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3800 node3800Labels + mixedMoment B node3805 node3805Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2484 singletonSmall5405
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5405) = raw2484Labels := by decide +kernel
  rw [hl, canonical2484 B hB] at h
  have hc0 : mixedMoment B raw2484 (Fin.cases (0 : Fin 2) singletonSmall5405) =
      mixedMoment B node3800 node3800Labels := by
    have ha : raw2484 = raw2485 := by apply Matrix.ext; unfold raw2484 raw2485; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5405 = raw2485Labels := by decide +kernel
    rw [ha, hj, canonical2485 B hB]
  have hc1 : mixedMoment B raw2484 (Fin.cases (1 : Fin 2) singletonSmall5405) =
      mixedMoment B node3805 node3805Labels := by
    have ha : raw2484 = raw2486 := by apply Matrix.ext; unfold raw2484 raw2486; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5405 = raw2486Labels := by decide +kernel
    rw [ha, hj, canonical2486 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5423 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5423 node5423Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3837 node3837Labels + mixedMoment B node3837 node3837Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2511 singletonSmall5423
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5423) = raw2511Labels := by decide +kernel
  rw [hl, canonical2511 B hB] at h
  have hc0 : mixedMoment B raw2511 (Fin.cases (0 : Fin 2) singletonSmall5423) =
      mixedMoment B node3837 node3837Labels := by
    have ha : raw2511 = raw2512 := by apply Matrix.ext; unfold raw2511 raw2512; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5423 = raw2512Labels := by decide +kernel
    rw [ha, hj, canonical2512 B hB]
  have hc1 : mixedMoment B raw2511 (Fin.cases (1 : Fin 2) singletonSmall5423) =
      mixedMoment B node3837 node3837Labels := by
    have ha : raw2511 = raw2513 := by apply Matrix.ext; unfold raw2511 raw2513; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5423 = raw2513Labels := by decide +kernel
    rw [ha, hj, canonical2513 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5424 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5424 node5424Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3838 node3838Labels + mixedMoment B node3843 node3843Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2514 singletonSmall5424
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5424) = raw2514Labels := by decide +kernel
  rw [hl, canonical2514 B hB] at h
  have hc0 : mixedMoment B raw2514 (Fin.cases (0 : Fin 2) singletonSmall5424) =
      mixedMoment B node3838 node3838Labels := by
    have ha : raw2514 = raw2515 := by apply Matrix.ext; unfold raw2514 raw2515; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5424 = raw2515Labels := by decide +kernel
    rw [ha, hj, canonical2515 B hB]
  have hc1 : mixedMoment B raw2514 (Fin.cases (1 : Fin 2) singletonSmall5424) =
      mixedMoment B node3843 node3843Labels := by
    have ha : raw2514 = raw2516 := by apply Matrix.ext; unfold raw2514 raw2516; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5424 = raw2516Labels := by decide +kernel
    rw [ha, hj, canonical2516 B hB]
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

theorem singleton5478 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5478 node5478Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3974 node3974Labels + mixedMoment B node3974 node3974Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2598 singletonSmall5478
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5478) = raw2598Labels := by decide +kernel
  rw [hl, canonical2598 B hB] at h
  have hc0 : mixedMoment B raw2598 (Fin.cases (0 : Fin 2) singletonSmall5478) =
      mixedMoment B node3974 node3974Labels := by
    have ha : raw2598 = raw2599 := by apply Matrix.ext; unfold raw2598 raw2599; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5478 = raw2599Labels := by decide +kernel
    rw [ha, hj, canonical2599 B hB]
  have hc1 : mixedMoment B raw2598 (Fin.cases (1 : Fin 2) singletonSmall5478) =
      mixedMoment B node3974 node3974Labels := by
    have ha : raw2598 = raw2600 := by apply Matrix.ext; unfold raw2598 raw2600; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5478 = raw2600Labels := by decide +kernel
    rw [ha, hj, canonical2600 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5477 node5477Labels = 0 := by
  exact mixedMoment_alpha B hF node5477 node5477Labels 2 permutation152
    (by decide +kernel)

theorem zero5489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5489 node5489Labels = 0 := by
  exact mixedMoment_alpha B hF node5489 node5489Labels 2 permutation152
    (by decide +kernel)

theorem zero5497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5497 node5497Labels = 0 := by
  exact mixedMoment_alpha B hF node5497 node5497Labels 0 permutation499
    (by decide +kernel)

theorem zero5499 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5499 node5499Labels = 0 := by
  exact mixedMoment_order_one B hB node5499 node5499Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5501 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5501 node5501Labels = 0 := by
  exact mixedMoment_order_one B hB node5501 node5501Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2294 node2294Labels = Sparse.eval nodeValue2294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2294) = mixedMoment B node2294 node2294Labels := rfl
  simpa [nodeValue2294, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5 node5Labels = Sparse.eval nodeValue5 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue5 (familyPairVector B) := singlePair5 B _hB
    _ = _ := by norm_num [singlePairValue5, nodeValue5, Sparse.eval, mixedVector]

theorem sound6 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node6 node6Labels = Sparse.eval nodeValue6 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue6 (familyPairVector B) := singlePair6 B _hB
    _ = _ := by norm_num [singlePairValue6, nodeValue6, Sparse.eval, mixedVector]

theorem sound7 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node7 node7Labels = Sparse.eval nodeValue7 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue7 (familyPairVector B) := singlePair7 B _hB
    _ = _ := by norm_num [singlePairValue7, nodeValue7, Sparse.eval, mixedVector]

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

theorem sound1067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1067 node1067Labels = Sparse.eval nodeValue1067 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1067) = mixedMoment B node1067 node1067Labels := rfl
  simpa [nodeValue1067, Sparse.eval] using hc.symm

theorem sound1069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1069 node1069Labels = Sparse.eval nodeValue1069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1069) = mixedMoment B node1069 node1069Labels := rfl
  simpa [nodeValue1069, Sparse.eval] using hc.symm

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

theorem sound1092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1092 node1092Labels = Sparse.eval nodeValue1092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1092) = mixedMoment B node1092 node1092Labels := rfl
  simpa [nodeValue1092, Sparse.eval] using hc.symm

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

theorem sound2063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2063 node2063Labels = Sparse.eval nodeValue2063 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2063) = mixedMoment B node2063 node2063Labels := rfl
  simpa [nodeValue2063, Sparse.eval] using hc.symm

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

theorem sound2285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2285 node2285Labels = Sparse.eval nodeValue2285 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2285) = mixedMoment B node2285 node2285Labels := rfl
  simpa [nodeValue2285, Sparse.eval] using hc.symm

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

theorem sound3800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3800 node3800Labels = Sparse.eval nodeValue3800 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3800) = mixedMoment B node3800 node3800Labels := rfl
  simpa [nodeValue3800, Sparse.eval] using hc.symm

theorem sound3805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3805 node3805Labels = Sparse.eval nodeValue3805 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3805) = mixedMoment B node3805 node3805Labels := rfl
  simpa [nodeValue3805, Sparse.eval] using hc.symm

theorem sound3837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3837 node3837Labels = Sparse.eval nodeValue3837 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3837) = mixedMoment B node3837 node3837Labels := rfl
  simpa [nodeValue3837, Sparse.eval] using hc.symm

theorem sound3838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3838 node3838Labels = Sparse.eval nodeValue3838 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3838) = mixedMoment B node3838 node3838Labels := rfl
  simpa [nodeValue3838, Sparse.eval] using hc.symm

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

theorem sound3843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3843 node3843Labels = Sparse.eval nodeValue3843 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3843) = mixedMoment B node3843 node3843Labels := rfl
  simpa [nodeValue3843, Sparse.eval] using hc.symm

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

theorem sound3974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3974 node3974Labels = Sparse.eval nodeValue3974 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3974) = mixedMoment B node3974 node3974Labels := rfl
  simpa [nodeValue3974, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4095 node4095Labels = 0 := by
  exact mixedMoment_alpha B hF node4095 node4095Labels 0 permutation499
    (by decide +kernel)

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

theorem sound4083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4083 node4083Labels = Sparse.eval nodeValue4083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4083) = mixedMoment B node4083 node4083Labels := rfl
  simpa [nodeValue4083, Sparse.eval] using hc.symm

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

theorem sound4091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4091 node4091Labels = Sparse.eval nodeValue4091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4091) = mixedMoment B node4091 node4091Labels := rfl
  simpa [nodeValue4091, Sparse.eval] using hc.symm

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

theorem sound4093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4093 node4093Labels = Sparse.eval nodeValue4093 (mixedVector B) := by
  have h := singleton4093 B _hB
  rw [sound5 B _hB _hF] at h
  norm_num [nodeValue4093, nodeValue5, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4094 node4094Labels = Sparse.eval nodeValue4094 (mixedVector B) := by
  have h := singleton4094 B _hB
  rw [sound6 B _hB _hF] at h
  norm_num [nodeValue4094, nodeValue6, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4095 node4095Labels = Sparse.eval nodeValue4095 (mixedVector B) := by
  simpa only [nodeValue4095, Sparse.eval_nil] using zero4095 B _hB _hF

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

theorem zero4097 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4097 node4097Labels = 0 := by
  exact mixedMoment_order_one B hB node4097 node4097Labels 0
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

theorem sound4096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4096 node4096Labels = Sparse.eval nodeValue4096 (mixedVector B) := by
  have h := singleton4096 B _hB
  rw [sound7 B _hB _hF] at h
  norm_num [nodeValue4096, nodeValue7, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4097 node4097Labels = Sparse.eval nodeValue4097 (mixedVector B) := by
  simpa only [nodeValue4097, Sparse.eval_nil] using zero4097 B _hB _hF

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

theorem sound5405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5405 node5405Labels = Sparse.eval nodeValue5405 (mixedVector B) := by
  have h := singleton5405 B _hB
  rw [sound3800 B _hB _hF, sound3805 B _hB _hF] at h
  norm_num [nodeValue5405, nodeValue3800, nodeValue3805, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5423 node5423Labels = Sparse.eval nodeValue5423 (mixedVector B) := by
  have h := singleton5423 B _hB
  rw [sound3837 B _hB _hF] at h
  norm_num [nodeValue5423, nodeValue3837, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5424 node5424Labels = Sparse.eval nodeValue5424 (mixedVector B) := by
  have h := singleton5424 B _hB
  rw [sound3838 B _hB _hF, sound3843 B _hB _hF] at h
  norm_num [nodeValue5424, nodeValue3838, nodeValue3843, Sparse.eval] at h ⊢
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

theorem sound5477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5477 node5477Labels = Sparse.eval nodeValue5477 (mixedVector B) := by
  simpa only [nodeValue5477, Sparse.eval_nil] using zero5477 B _hB _hF

theorem sound5478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5478 node5478Labels = Sparse.eval nodeValue5478 (mixedVector B) := by
  have h := singleton5478 B _hB
  rw [sound3974 B _hB _hF] at h
  norm_num [nodeValue5478, nodeValue3974, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5489 node5489Labels = Sparse.eval nodeValue5489 (mixedVector B) := by
  simpa only [nodeValue5489, Sparse.eval_nil] using zero5489 B _hB _hF

theorem sound5497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5497 node5497Labels = Sparse.eval nodeValue5497 (mixedVector B) := by
  simpa only [nodeValue5497, Sparse.eval_nil] using zero5497 B _hB _hF

theorem sound5499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5499 node5499Labels = Sparse.eval nodeValue5499 (mixedVector B) := by
  simpa only [nodeValue5499, Sparse.eval_nil] using zero5499 B _hB _hF

theorem sound5501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5501 node5501Labels = Sparse.eval nodeValue5501 (mixedVector B) := by
  simpa only [nodeValue5501, Sparse.eval_nil] using zero5501 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources0
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq25 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm25 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA25 + difference 0 1) (sourceB25 + difference 1 0) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA25 + difference 0 1) (sourceB25 + difference 1 0) sourceC25) = raw3319 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3319; decide +kernel
    rw [ha]
    exact (canonical3319 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA25 + difference 0 2) (sourceB25 + difference 2 0) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA25 + difference 0 2) (sourceB25 + difference 2 0) sourceC25) = raw3320 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3320; decide +kernel
    rw [ha]
    exact (canonical3320 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA25 + difference 0 3) (sourceB25 + difference 3 0) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA25 + difference 0 3) (sourceB25 + difference 3 0) sourceC25) = raw3321 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3321; decide +kernel
    rw [ha]
    exact (canonical3321 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA25 + difference 0 4) (sourceB25 + difference 4 0) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4097) := by
    have ha : (tripleCharges (sourceA25 + difference 0 4) (sourceB25 + difference 4 0) sourceC25) = raw2913 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw2913; decide +kernel
    rw [ha]
    exact (canonical2913 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA25 + difference 0 5) (sourceB25 + difference 5 0) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4097) := by
    have ha : (tripleCharges (sourceA25 + difference 0 5) (sourceB25 + difference 5 0) sourceC25) = raw3322 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3322; decide +kernel
    rw [ha]
    exact (canonical3322 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA25 + difference 1 0) (sourceB25 + difference 0 1) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA25 + difference 1 0) (sourceB25 + difference 0 1) sourceC25) = raw3323 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3323; decide +kernel
    rw [ha]
    exact (canonical3323 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA25 + difference 1 2) (sourceB25 + difference 2 1) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA25 + difference 1 2) (sourceB25 + difference 2 1) sourceC25) = raw3324 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3324; decide +kernel
    rw [ha]
    exact (canonical3324 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA25 + difference 1 3) (sourceB25 + difference 3 1) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA25 + difference 1 3) (sourceB25 + difference 3 1) sourceC25) = raw3325 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3325; decide +kernel
    rw [ha]
    exact (canonical3325 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA25 + difference 1 4) (sourceB25 + difference 4 1) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA25 + difference 1 4) (sourceB25 + difference 4 1) sourceC25) = raw2918 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw2918; decide +kernel
    rw [ha]
    exact (canonical2918 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA25 + difference 1 5) (sourceB25 + difference 5 1) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA25 + difference 1 5) (sourceB25 + difference 5 1) sourceC25) = raw3326 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3326; decide +kernel
    rw [ha]
    exact (canonical3326 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA25 + difference 2 0) (sourceB25 + difference 0 2) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA25 + difference 2 0) (sourceB25 + difference 0 2) sourceC25) = raw3327 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3327; decide +kernel
    rw [ha]
    exact (canonical3327 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA25 + difference 2 1) (sourceB25 + difference 1 2) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA25 + difference 2 1) (sourceB25 + difference 1 2) sourceC25) = raw3328 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3328; decide +kernel
    rw [ha]
    exact (canonical3328 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA25 + difference 2 3) (sourceB25 + difference 3 2) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA25 + difference 2 3) (sourceB25 + difference 3 2) sourceC25) = raw3329 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3329; decide +kernel
    rw [ha]
    exact (canonical3329 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA25 + difference 2 4) (sourceB25 + difference 4 2) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA25 + difference 2 4) (sourceB25 + difference 4 2) sourceC25) = raw2923 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw2923; decide +kernel
    rw [ha]
    exact (canonical2923 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA25 + difference 2 5) (sourceB25 + difference 5 2) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA25 + difference 2 5) (sourceB25 + difference 5 2) sourceC25) = raw3330 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3330; decide +kernel
    rw [ha]
    exact (canonical3330 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA25 + difference 3 0) (sourceB25 + difference 0 3) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA25 + difference 3 0) (sourceB25 + difference 0 3) sourceC25) = raw3331 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3331; decide +kernel
    rw [ha]
    exact (canonical3331 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA25 + difference 3 1) (sourceB25 + difference 1 3) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA25 + difference 3 1) (sourceB25 + difference 1 3) sourceC25) = raw3332 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3332; decide +kernel
    rw [ha]
    exact (canonical3332 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA25 + difference 3 2) (sourceB25 + difference 2 3) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA25 + difference 3 2) (sourceB25 + difference 2 3) sourceC25) = raw3333 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3333; decide +kernel
    rw [ha]
    exact (canonical3333 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA25 + difference 3 4) (sourceB25 + difference 4 3) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA25 + difference 3 4) (sourceB25 + difference 4 3) sourceC25) = raw2928 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw2928; decide +kernel
    rw [ha]
    exact (canonical2928 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA25 + difference 3 5) (sourceB25 + difference 5 3) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA25 + difference 3 5) (sourceB25 + difference 5 3) sourceC25) = raw3334 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3334; decide +kernel
    rw [ha]
    exact (canonical3334 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA25 + difference 4 0) (sourceB25 + difference 0 4) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA25 + difference 4 0) (sourceB25 + difference 0 4) sourceC25) = raw3335 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3335; decide +kernel
    rw [ha]
    exact (canonical3335 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA25 + difference 4 1) (sourceB25 + difference 1 4) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA25 + difference 4 1) (sourceB25 + difference 1 4) sourceC25) = raw3336 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3336; decide +kernel
    rw [ha]
    exact (canonical3336 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA25 + difference 4 2) (sourceB25 + difference 2 4) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA25 + difference 4 2) (sourceB25 + difference 2 4) sourceC25) = raw3337 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3337; decide +kernel
    rw [ha]
    exact (canonical3337 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA25 + difference 4 3) (sourceB25 + difference 3 4) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA25 + difference 4 3) (sourceB25 + difference 3 4) sourceC25) = raw3338 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3338; decide +kernel
    rw [ha]
    exact (canonical3338 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA25 + difference 4 5) (sourceB25 + difference 5 4) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4094) := by
    have ha : (tripleCharges (sourceA25 + difference 4 5) (sourceB25 + difference 5 4) sourceC25) = raw3339 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3339; decide +kernel
    rw [ha]
    exact (canonical3339 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA25 + difference 5 0) (sourceB25 + difference 0 5) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA25 + difference 5 0) (sourceB25 + difference 0 5) sourceC25) = raw2929 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw2929; decide +kernel
    rw [ha]
    exact (canonical2929 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA25 + difference 5 1) (sourceB25 + difference 1 5) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA25 + difference 5 1) (sourceB25 + difference 1 5) sourceC25) = raw2930 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw2930; decide +kernel
    rw [ha]
    exact (canonical2930 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA25 + difference 5 2) (sourceB25 + difference 2 5) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA25 + difference 5 2) (sourceB25 + difference 2 5) sourceC25) = raw2931 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw2931; decide +kernel
    rw [ha]
    exact (canonical2931 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA25 + difference 5 3) (sourceB25 + difference 3 5) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA25 + difference 5 3) (sourceB25 + difference 3 5) sourceC25) = raw2932 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw2932; decide +kernel
    rw [ha]
    exact (canonical2932 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA25 + difference 5 4) (sourceB25 + difference 4 5) sourceC25) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4094) := by
    have ha : (tripleCharges (sourceA25 + difference 5 4) (sourceB25 + difference 4 5) sourceC25) = raw3340 := by
      apply Matrix.ext; unfold tripleCharges sourceA25 sourceB25 sourceC25 difference raw3340; decide +kernel
    rw [ha]
    exact (canonical3340 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA25 sourceB25 sourceC25
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm25, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq26 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm26 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA26 + difference 0 1) (sourceB26 + difference 1 0) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA26 + difference 0 1) (sourceB26 + difference 1 0) sourceC26) = raw3341 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3341; decide +kernel
    rw [ha]
    exact (canonical3341 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA26 + difference 0 2) (sourceB26 + difference 2 0) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA26 + difference 0 2) (sourceB26 + difference 2 0) sourceC26) = raw3342 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3342; decide +kernel
    rw [ha]
    exact (canonical3342 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA26 + difference 0 3) (sourceB26 + difference 3 0) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA26 + difference 0 3) (sourceB26 + difference 3 0) sourceC26) = raw3343 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3343; decide +kernel
    rw [ha]
    exact (canonical3343 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA26 + difference 0 4) (sourceB26 + difference 4 0) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA26 + difference 0 4) (sourceB26 + difference 4 0) sourceC26) = raw3344 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3344; decide +kernel
    rw [ha]
    exact (canonical3344 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA26 + difference 0 5) (sourceB26 + difference 5 0) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA26 + difference 0 5) (sourceB26 + difference 5 0) sourceC26) = raw3345 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3345; decide +kernel
    rw [ha]
    exact (canonical3345 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA26 + difference 1 0) (sourceB26 + difference 0 1) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA26 + difference 1 0) (sourceB26 + difference 0 1) sourceC26) = raw3346 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3346; decide +kernel
    rw [ha]
    exact (canonical3346 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA26 + difference 1 2) (sourceB26 + difference 2 1) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA26 + difference 1 2) (sourceB26 + difference 2 1) sourceC26) = raw3347 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3347; decide +kernel
    rw [ha]
    exact (canonical3347 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA26 + difference 1 3) (sourceB26 + difference 3 1) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA26 + difference 1 3) (sourceB26 + difference 3 1) sourceC26) = raw3348 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3348; decide +kernel
    rw [ha]
    exact (canonical3348 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA26 + difference 1 4) (sourceB26 + difference 4 1) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA26 + difference 1 4) (sourceB26 + difference 4 1) sourceC26) = raw3349 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3349; decide +kernel
    rw [ha]
    exact (canonical3349 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA26 + difference 1 5) (sourceB26 + difference 5 1) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA26 + difference 1 5) (sourceB26 + difference 5 1) sourceC26) = raw3350 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3350; decide +kernel
    rw [ha]
    exact (canonical3350 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA26 + difference 2 0) (sourceB26 + difference 0 2) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA26 + difference 2 0) (sourceB26 + difference 0 2) sourceC26) = raw3351 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3351; decide +kernel
    rw [ha]
    exact (canonical3351 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA26 + difference 2 1) (sourceB26 + difference 1 2) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA26 + difference 2 1) (sourceB26 + difference 1 2) sourceC26) = raw3352 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3352; decide +kernel
    rw [ha]
    exact (canonical3352 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA26 + difference 2 3) (sourceB26 + difference 3 2) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA26 + difference 2 3) (sourceB26 + difference 3 2) sourceC26) = raw3353 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3353; decide +kernel
    rw [ha]
    exact (canonical3353 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA26 + difference 2 4) (sourceB26 + difference 4 2) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA26 + difference 2 4) (sourceB26 + difference 4 2) sourceC26) = raw3354 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3354; decide +kernel
    rw [ha]
    exact (canonical3354 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA26 + difference 2 5) (sourceB26 + difference 5 2) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA26 + difference 2 5) (sourceB26 + difference 5 2) sourceC26) = raw3355 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3355; decide +kernel
    rw [ha]
    exact (canonical3355 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA26 + difference 3 0) (sourceB26 + difference 0 3) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA26 + difference 3 0) (sourceB26 + difference 0 3) sourceC26) = raw3356 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3356; decide +kernel
    rw [ha]
    exact (canonical3356 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA26 + difference 3 1) (sourceB26 + difference 1 3) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA26 + difference 3 1) (sourceB26 + difference 1 3) sourceC26) = raw3357 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3357; decide +kernel
    rw [ha]
    exact (canonical3357 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA26 + difference 3 2) (sourceB26 + difference 2 3) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA26 + difference 3 2) (sourceB26 + difference 2 3) sourceC26) = raw3358 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3358; decide +kernel
    rw [ha]
    exact (canonical3358 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA26 + difference 3 4) (sourceB26 + difference 4 3) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA26 + difference 3 4) (sourceB26 + difference 4 3) sourceC26) = raw3359 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3359; decide +kernel
    rw [ha]
    exact (canonical3359 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA26 + difference 3 5) (sourceB26 + difference 5 3) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA26 + difference 3 5) (sourceB26 + difference 5 3) sourceC26) = raw3360 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3360; decide +kernel
    rw [ha]
    exact (canonical3360 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA26 + difference 4 0) (sourceB26 + difference 0 4) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA26 + difference 4 0) (sourceB26 + difference 0 4) sourceC26) = raw3361 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3361; decide +kernel
    rw [ha]
    exact (canonical3361 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA26 + difference 4 1) (sourceB26 + difference 1 4) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA26 + difference 4 1) (sourceB26 + difference 1 4) sourceC26) = raw3362 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3362; decide +kernel
    rw [ha]
    exact (canonical3362 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA26 + difference 4 2) (sourceB26 + difference 2 4) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA26 + difference 4 2) (sourceB26 + difference 2 4) sourceC26) = raw3363 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3363; decide +kernel
    rw [ha]
    exact (canonical3363 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA26 + difference 4 3) (sourceB26 + difference 3 4) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA26 + difference 4 3) (sourceB26 + difference 3 4) sourceC26) = raw3364 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3364; decide +kernel
    rw [ha]
    exact (canonical3364 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA26 + difference 4 5) (sourceB26 + difference 5 4) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA26 + difference 4 5) (sourceB26 + difference 5 4) sourceC26) = raw3365 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3365; decide +kernel
    rw [ha]
    exact (canonical3365 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA26 + difference 5 0) (sourceB26 + difference 0 5) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA26 + difference 5 0) (sourceB26 + difference 0 5) sourceC26) = raw3366 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3366; decide +kernel
    rw [ha]
    exact (canonical3366 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA26 + difference 5 1) (sourceB26 + difference 1 5) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA26 + difference 5 1) (sourceB26 + difference 1 5) sourceC26) = raw3367 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3367; decide +kernel
    rw [ha]
    exact (canonical3367 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA26 + difference 5 2) (sourceB26 + difference 2 5) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA26 + difference 5 2) (sourceB26 + difference 2 5) sourceC26) = raw3368 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3368; decide +kernel
    rw [ha]
    exact (canonical3368 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA26 + difference 5 3) (sourceB26 + difference 3 5) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA26 + difference 5 3) (sourceB26 + difference 3 5) sourceC26) = raw3369 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3369; decide +kernel
    rw [ha]
    exact (canonical3369 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA26 + difference 5 4) (sourceB26 + difference 4 5) sourceC26) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA26 + difference 5 4) (sourceB26 + difference 4 5) sourceC26) = raw3370 := by
      apply Matrix.ext; unfold tripleCharges sourceA26 sourceB26 sourceC26 difference raw3370; decide +kernel
    rw [ha]
    exact (canonical3370 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA26 sourceB26 sourceC26
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm26, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq27 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm27 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA27 + difference 0 1) (sourceB27 + difference 1 0) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA27 + difference 0 1) (sourceB27 + difference 1 0) sourceC27) = raw3371 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3371; decide +kernel
    rw [ha]
    exact (canonical3371 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA27 + difference 0 2) (sourceB27 + difference 2 0) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5500) := by
    have ha : (tripleCharges (sourceA27 + difference 0 2) (sourceB27 + difference 2 0) sourceC27) = raw3372 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3372; decide +kernel
    rw [ha]
    exact (canonical3372 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA27 + difference 0 3) (sourceB27 + difference 3 0) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA27 + difference 0 3) (sourceB27 + difference 3 0) sourceC27) = raw3373 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3373; decide +kernel
    rw [ha]
    exact (canonical3373 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA27 + difference 0 4) (sourceB27 + difference 4 0) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA27 + difference 0 4) (sourceB27 + difference 4 0) sourceC27) = raw3374 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3374; decide +kernel
    rw [ha]
    exact (canonical3374 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA27 + difference 0 5) (sourceB27 + difference 5 0) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5497) := by
    have ha : (tripleCharges (sourceA27 + difference 0 5) (sourceB27 + difference 5 0) sourceC27) = raw3375 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3375; decide +kernel
    rw [ha]
    exact (canonical3375 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA27 + difference 1 0) (sourceB27 + difference 0 1) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA27 + difference 1 0) (sourceB27 + difference 0 1) sourceC27) = raw3376 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3376; decide +kernel
    rw [ha]
    exact (canonical3376 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA27 + difference 1 2) (sourceB27 + difference 2 1) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA27 + difference 1 2) (sourceB27 + difference 2 1) sourceC27) = raw3377 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3377; decide +kernel
    rw [ha]
    exact (canonical3377 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA27 + difference 1 3) (sourceB27 + difference 3 1) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA27 + difference 1 3) (sourceB27 + difference 3 1) sourceC27) = raw3378 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3378; decide +kernel
    rw [ha]
    exact (canonical3378 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA27 + difference 1 4) (sourceB27 + difference 4 1) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5501) := by
    have ha : (tripleCharges (sourceA27 + difference 1 4) (sourceB27 + difference 4 1) sourceC27) = raw3379 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3379; decide +kernel
    rw [ha]
    exact (canonical3379 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA27 + difference 1 5) (sourceB27 + difference 5 1) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA27 + difference 1 5) (sourceB27 + difference 5 1) sourceC27) = raw3380 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3380; decide +kernel
    rw [ha]
    exact (canonical3380 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA27 + difference 2 0) (sourceB27 + difference 0 2) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA27 + difference 2 0) (sourceB27 + difference 0 2) sourceC27) = raw3381 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3381; decide +kernel
    rw [ha]
    exact (canonical3381 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA27 + difference 2 1) (sourceB27 + difference 1 2) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA27 + difference 2 1) (sourceB27 + difference 1 2) sourceC27) = raw3382 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3382; decide +kernel
    rw [ha]
    exact (canonical3382 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA27 + difference 2 3) (sourceB27 + difference 3 2) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA27 + difference 2 3) (sourceB27 + difference 3 2) sourceC27) = raw3383 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3383; decide +kernel
    rw [ha]
    exact (canonical3383 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA27 + difference 2 4) (sourceB27 + difference 4 2) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA27 + difference 2 4) (sourceB27 + difference 4 2) sourceC27) = raw3384 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3384; decide +kernel
    rw [ha]
    exact (canonical3384 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA27 + difference 2 5) (sourceB27 + difference 5 2) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA27 + difference 2 5) (sourceB27 + difference 5 2) sourceC27) = raw3385 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3385; decide +kernel
    rw [ha]
    exact (canonical3385 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA27 + difference 3 0) (sourceB27 + difference 0 3) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA27 + difference 3 0) (sourceB27 + difference 0 3) sourceC27) = raw3386 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3386; decide +kernel
    rw [ha]
    exact (canonical3386 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA27 + difference 3 1) (sourceB27 + difference 1 3) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA27 + difference 3 1) (sourceB27 + difference 1 3) sourceC27) = raw3387 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3387; decide +kernel
    rw [ha]
    exact (canonical3387 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA27 + difference 3 2) (sourceB27 + difference 2 3) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5497) := by
    have ha : (tripleCharges (sourceA27 + difference 3 2) (sourceB27 + difference 2 3) sourceC27) = raw3388 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3388; decide +kernel
    rw [ha]
    exact (canonical3388 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA27 + difference 3 4) (sourceB27 + difference 4 3) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA27 + difference 3 4) (sourceB27 + difference 4 3) sourceC27) = raw3389 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3389; decide +kernel
    rw [ha]
    exact (canonical3389 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA27 + difference 3 5) (sourceB27 + difference 5 3) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5500) := by
    have ha : (tripleCharges (sourceA27 + difference 3 5) (sourceB27 + difference 5 3) sourceC27) = raw3390 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3390; decide +kernel
    rw [ha]
    exact (canonical3390 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA27 + difference 4 0) (sourceB27 + difference 0 4) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA27 + difference 4 0) (sourceB27 + difference 0 4) sourceC27) = raw3391 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3391; decide +kernel
    rw [ha]
    exact (canonical3391 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA27 + difference 4 1) (sourceB27 + difference 1 4) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA27 + difference 4 1) (sourceB27 + difference 1 4) sourceC27) = raw3392 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3392; decide +kernel
    rw [ha]
    exact (canonical3392 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA27 + difference 4 2) (sourceB27 + difference 2 4) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA27 + difference 4 2) (sourceB27 + difference 2 4) sourceC27) = raw3393 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3393; decide +kernel
    rw [ha]
    exact (canonical3393 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA27 + difference 4 3) (sourceB27 + difference 3 4) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA27 + difference 4 3) (sourceB27 + difference 3 4) sourceC27) = raw3394 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3394; decide +kernel
    rw [ha]
    exact (canonical3394 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA27 + difference 4 5) (sourceB27 + difference 5 4) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA27 + difference 4 5) (sourceB27 + difference 5 4) sourceC27) = raw3395 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3395; decide +kernel
    rw [ha]
    exact (canonical3395 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA27 + difference 5 0) (sourceB27 + difference 0 5) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA27 + difference 5 0) (sourceB27 + difference 0 5) sourceC27) = raw3396 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3396; decide +kernel
    rw [ha]
    exact (canonical3396 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA27 + difference 5 1) (sourceB27 + difference 1 5) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA27 + difference 5 1) (sourceB27 + difference 1 5) sourceC27) = raw3397 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3397; decide +kernel
    rw [ha]
    exact (canonical3397 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA27 + difference 5 2) (sourceB27 + difference 2 5) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA27 + difference 5 2) (sourceB27 + difference 2 5) sourceC27) = raw3398 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3398; decide +kernel
    rw [ha]
    exact (canonical3398 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA27 + difference 5 3) (sourceB27 + difference 3 5) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA27 + difference 5 3) (sourceB27 + difference 3 5) sourceC27) = raw3399 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3399; decide +kernel
    rw [ha]
    exact (canonical3399 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA27 + difference 5 4) (sourceB27 + difference 4 5) sourceC27) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA27 + difference 5 4) (sourceB27 + difference 4 5) sourceC27) = raw3400 := by
      apply Matrix.ext; unfold tripleCharges sourceA27 sourceB27 sourceC27 difference raw3400; decide +kernel
    rw [ha]
    exact (canonical3400 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA27 sourceB27 sourceC27
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm27, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq29 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm29 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA29 + difference 0 1) (sourceB29 + difference 1 0) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA29 + difference 0 1) (sourceB29 + difference 1 0) sourceC29) = raw3431 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3431; decide +kernel
    rw [ha]
    exact (canonical3431 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA29 + difference 0 2) (sourceB29 + difference 2 0) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA29 + difference 0 2) (sourceB29 + difference 2 0) sourceC29) = raw3432 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3432; decide +kernel
    rw [ha]
    exact (canonical3432 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA29 + difference 0 3) (sourceB29 + difference 3 0) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA29 + difference 0 3) (sourceB29 + difference 3 0) sourceC29) = raw3433 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3433; decide +kernel
    rw [ha]
    exact (canonical3433 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA29 + difference 0 4) (sourceB29 + difference 4 0) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4097) := by
    have ha : (tripleCharges (sourceA29 + difference 0 4) (sourceB29 + difference 4 0) sourceC29) = raw3434 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3434; decide +kernel
    rw [ha]
    exact (canonical3434 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA29 + difference 0 5) (sourceB29 + difference 5 0) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4097) := by
    have ha : (tripleCharges (sourceA29 + difference 0 5) (sourceB29 + difference 5 0) sourceC29) = raw3435 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3435; decide +kernel
    rw [ha]
    exact (canonical3435 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA29 + difference 1 0) (sourceB29 + difference 0 1) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA29 + difference 1 0) (sourceB29 + difference 0 1) sourceC29) = raw2933 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw2933; decide +kernel
    rw [ha]
    exact (canonical2933 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA29 + difference 1 2) (sourceB29 + difference 2 1) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA29 + difference 1 2) (sourceB29 + difference 2 1) sourceC29) = raw3320 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3320; decide +kernel
    rw [ha]
    exact (canonical3320 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA29 + difference 1 3) (sourceB29 + difference 3 1) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA29 + difference 1 3) (sourceB29 + difference 3 1) sourceC29) = raw3321 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3321; decide +kernel
    rw [ha]
    exact (canonical3321 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA29 + difference 1 4) (sourceB29 + difference 4 1) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4097) := by
    have ha : (tripleCharges (sourceA29 + difference 1 4) (sourceB29 + difference 4 1) sourceC29) = raw2913 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw2913; decide +kernel
    rw [ha]
    exact (canonical2913 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA29 + difference 1 5) (sourceB29 + difference 5 1) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4097) := by
    have ha : (tripleCharges (sourceA29 + difference 1 5) (sourceB29 + difference 5 1) sourceC29) = raw3322 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3322; decide +kernel
    rw [ha]
    exact (canonical3322 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA29 + difference 2 0) (sourceB29 + difference 0 2) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA29 + difference 2 0) (sourceB29 + difference 0 2) sourceC29) = raw3328 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3328; decide +kernel
    rw [ha]
    exact (canonical3328 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA29 + difference 2 1) (sourceB29 + difference 1 2) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA29 + difference 2 1) (sourceB29 + difference 1 2) sourceC29) = raw3436 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3436; decide +kernel
    rw [ha]
    exact (canonical3436 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA29 + difference 2 3) (sourceB29 + difference 3 2) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4095) := by
    have ha : (tripleCharges (sourceA29 + difference 2 3) (sourceB29 + difference 3 2) sourceC29) = raw3437 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3437; decide +kernel
    rw [ha]
    exact (canonical3437 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA29 + difference 2 4) (sourceB29 + difference 4 2) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA29 + difference 2 4) (sourceB29 + difference 4 2) sourceC29) = raw3438 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3438; decide +kernel
    rw [ha]
    exact (canonical3438 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA29 + difference 2 5) (sourceB29 + difference 5 2) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA29 + difference 2 5) (sourceB29 + difference 5 2) sourceC29) = raw3439 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3439; decide +kernel
    rw [ha]
    exact (canonical3439 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA29 + difference 3 0) (sourceB29 + difference 0 3) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA29 + difference 3 0) (sourceB29 + difference 0 3) sourceC29) = raw3332 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3332; decide +kernel
    rw [ha]
    exact (canonical3332 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA29 + difference 3 1) (sourceB29 + difference 1 3) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA29 + difference 3 1) (sourceB29 + difference 1 3) sourceC29) = raw3440 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3440; decide +kernel
    rw [ha]
    exact (canonical3440 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA29 + difference 3 2) (sourceB29 + difference 2 3) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4095) := by
    have ha : (tripleCharges (sourceA29 + difference 3 2) (sourceB29 + difference 2 3) sourceC29) = raw3441 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3441; decide +kernel
    rw [ha]
    exact (canonical3441 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA29 + difference 3 4) (sourceB29 + difference 4 3) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA29 + difference 3 4) (sourceB29 + difference 4 3) sourceC29) = raw3442 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3442; decide +kernel
    rw [ha]
    exact (canonical3442 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA29 + difference 3 5) (sourceB29 + difference 5 3) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA29 + difference 3 5) (sourceB29 + difference 5 3) sourceC29) = raw3443 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3443; decide +kernel
    rw [ha]
    exact (canonical3443 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA29 + difference 4 0) (sourceB29 + difference 0 4) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA29 + difference 4 0) (sourceB29 + difference 0 4) sourceC29) = raw3336 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3336; decide +kernel
    rw [ha]
    exact (canonical3336 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA29 + difference 4 1) (sourceB29 + difference 1 4) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA29 + difference 4 1) (sourceB29 + difference 1 4) sourceC29) = raw3444 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3444; decide +kernel
    rw [ha]
    exact (canonical3444 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA29 + difference 4 2) (sourceB29 + difference 2 4) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA29 + difference 4 2) (sourceB29 + difference 2 4) sourceC29) = raw3445 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3445; decide +kernel
    rw [ha]
    exact (canonical3445 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA29 + difference 4 3) (sourceB29 + difference 3 4) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA29 + difference 4 3) (sourceB29 + difference 3 4) sourceC29) = raw3446 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3446; decide +kernel
    rw [ha]
    exact (canonical3446 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA29 + difference 4 5) (sourceB29 + difference 5 4) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA29 + difference 4 5) (sourceB29 + difference 5 4) sourceC29) = raw3447 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3447; decide +kernel
    rw [ha]
    exact (canonical3447 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA29 + difference 5 0) (sourceB29 + difference 0 5) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA29 + difference 5 0) (sourceB29 + difference 0 5) sourceC29) = raw2930 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw2930; decide +kernel
    rw [ha]
    exact (canonical2930 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA29 + difference 5 1) (sourceB29 + difference 1 5) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA29 + difference 5 1) (sourceB29 + difference 1 5) sourceC29) = raw3448 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3448; decide +kernel
    rw [ha]
    exact (canonical3448 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA29 + difference 5 2) (sourceB29 + difference 2 5) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA29 + difference 5 2) (sourceB29 + difference 2 5) sourceC29) = raw3449 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3449; decide +kernel
    rw [ha]
    exact (canonical3449 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA29 + difference 5 3) (sourceB29 + difference 3 5) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA29 + difference 5 3) (sourceB29 + difference 3 5) sourceC29) = raw3450 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw3450; decide +kernel
    rw [ha]
    exact (canonical3450 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA29 + difference 5 4) (sourceB29 + difference 4 5) sourceC29) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA29 + difference 5 4) (sourceB29 + difference 4 5) sourceC29) = raw2909 := by
      apply Matrix.ext; unfold tripleCharges sourceA29 sourceB29 sourceC29 difference raw2909; decide +kernel
    rw [ha]
    exact (canonical2909 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA29 sourceB29 sourceC29
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm29, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources1
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq32 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm32 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA32 + difference 0 0) (sourceB32 + difference 0 0) sourceC32) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2285) := by
    have ha : (tripleCharges (sourceA32 + difference 0 0) (sourceB32 + difference 0 0) sourceC32) = raw3511 := by
      apply Matrix.ext; unfold tripleCharges sourceA32 sourceB32 sourceC32 difference raw3511; decide +kernel
    rw [ha]
    exact (canonical3511 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA32 + difference 0 1) (sourceB32 + difference 1 0) sourceC32) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2063) := by
    have ha : (tripleCharges (sourceA32 + difference 0 1) (sourceB32 + difference 1 0) sourceC32) = raw3512 := by
      apply Matrix.ext; unfold tripleCharges sourceA32 sourceB32 sourceC32 difference raw3512; decide +kernel
    rw [ha]
    exact (canonical3512 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA32 + difference 0 2) (sourceB32 + difference 2 0) sourceC32) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2063) := by
    have ha : (tripleCharges (sourceA32 + difference 0 2) (sourceB32 + difference 2 0) sourceC32) = raw3513 := by
      apply Matrix.ext; unfold tripleCharges sourceA32 sourceB32 sourceC32 difference raw3513; decide +kernel
    rw [ha]
    exact (canonical3513 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA32 + difference 0 3) (sourceB32 + difference 3 0) sourceC32) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2063) := by
    have ha : (tripleCharges (sourceA32 + difference 0 3) (sourceB32 + difference 3 0) sourceC32) = raw3514 := by
      apply Matrix.ext; unfold tripleCharges sourceA32 sourceB32 sourceC32 difference raw3514; decide +kernel
    rw [ha]
    exact (canonical3514 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA32 + difference 0 4) (sourceB32 + difference 4 0) sourceC32) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1092) := by
    have ha : (tripleCharges (sourceA32 + difference 0 4) (sourceB32 + difference 4 0) sourceC32) = raw3515 := by
      apply Matrix.ext; unfold tripleCharges sourceA32 sourceB32 sourceC32 difference raw3515; decide +kernel
    rw [ha]
    exact (canonical3515 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA32 + difference 0 5) (sourceB32 + difference 5 0) sourceC32) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2294) := by
    have ha : (tripleCharges (sourceA32 + difference 0 5) (sourceB32 + difference 5 0) sourceC32) = raw3516 := by
      apply Matrix.ext; unfold tripleCharges sourceA32 sourceB32 sourceC32 difference raw3516; decide +kernel
    rw [ha]
    exact (canonical3516 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA32 + sourceB32) sourceC32) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA32 + sourceB32) sourceC32) = raw3517 := by
      apply Matrix.ext; unfold doubleCharges sourceA32 sourceB32 sourceC32 raw3517; decide +kernel
    rw [ha]
    exact (canonical3517 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA32 sourceB32 sourceC32
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm32, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq33 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm33 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA33 + difference 0 0) (sourceB33 + difference 0 0) sourceC33) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2285) := by
    have ha : (tripleCharges (sourceA33 + difference 0 0) (sourceB33 + difference 0 0) sourceC33) = raw3511 := by
      apply Matrix.ext; unfold tripleCharges sourceA33 sourceB33 sourceC33 difference raw3511; decide +kernel
    rw [ha]
    exact (canonical3511 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA33 + difference 1 0) (sourceB33 + difference 0 1) sourceC33) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1067) := by
    have ha : (tripleCharges (sourceA33 + difference 1 0) (sourceB33 + difference 0 1) sourceC33) = raw3518 := by
      apply Matrix.ext; unfold tripleCharges sourceA33 sourceB33 sourceC33 difference raw3518; decide +kernel
    rw [ha]
    exact (canonical3518 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA33 + difference 2 0) (sourceB33 + difference 0 2) sourceC33) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1067) := by
    have ha : (tripleCharges (sourceA33 + difference 2 0) (sourceB33 + difference 0 2) sourceC33) = raw3519 := by
      apply Matrix.ext; unfold tripleCharges sourceA33 sourceB33 sourceC33 difference raw3519; decide +kernel
    rw [ha]
    exact (canonical3519 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA33 + difference 3 0) (sourceB33 + difference 0 3) sourceC33) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1067) := by
    have ha : (tripleCharges (sourceA33 + difference 3 0) (sourceB33 + difference 0 3) sourceC33) = raw3520 := by
      apply Matrix.ext; unfold tripleCharges sourceA33 sourceB33 sourceC33 difference raw3520; decide +kernel
    rw [ha]
    exact (canonical3520 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA33 + difference 4 0) (sourceB33 + difference 0 4) sourceC33) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1092) := by
    have ha : (tripleCharges (sourceA33 + difference 4 0) (sourceB33 + difference 0 4) sourceC33) = raw3521 := by
      apply Matrix.ext; unfold tripleCharges sourceA33 sourceB33 sourceC33 difference raw3521; decide +kernel
    rw [ha]
    exact (canonical3521 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA33 + difference 5 0) (sourceB33 + difference 0 5) sourceC33) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1069) := by
    have ha : (tripleCharges (sourceA33 + difference 5 0) (sourceB33 + difference 0 5) sourceC33) = raw3522 := by
      apply Matrix.ext; unfold tripleCharges sourceA33 sourceB33 sourceC33 difference raw3522; decide +kernel
    rw [ha]
    exact (canonical3522 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA33 + sourceB33) sourceC33) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA33 + sourceB33) sourceC33) = raw3517 := by
      apply Matrix.ext; unfold doubleCharges sourceA33 sourceB33 sourceC33 raw3517; decide +kernel
    rw [ha]
    exact (canonical3517 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA33 sourceB33 sourceC33
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm33, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck18 : Integer.Sparse.reindex keyMap MixedData.row18 = numericRow18 := by decide +kernel

theorem numericCheck18 (x : Master → ℝ) : Integer.Sparse.eval numericRow18 x =
    (17280 : ℝ) * reducedSource18 x := by
  norm_num [numericRow18, reducedSource18, Integer.Sparse.eval, Sparse.eval, nodeValue5257, nodeValue5258, nodeValue5259, nodeValue5271, nodeValue5292, nodeValue5424, nodeValue5428, nodeValue5434, nodeValue5439, nodeValue5472, nodeValue5473, nodeValue5477, nodeValue5478, nodeValue5482, nodeValue5483, nodeValue5485, nodeValue5486, nodeValue5489, nodeValue5490, nodeValue5491, nodeValue5492, nodeValue5493, nodeValue5499, nodeValue5500, nodeValue5501]
  ring

theorem reindexCheck25 : Integer.Sparse.reindex keyMap MixedData.row25 = numericRow25 := by decide +kernel

theorem numericCheck25 (x : Master → ℝ) : Integer.Sparse.eval numericRow25 x =
    (40 : ℝ) * reducedSource25 x := by
  norm_num [numericRow25, reducedSource25, Integer.Sparse.eval, Sparse.eval, nodeValue4083, nodeValue4084, nodeValue4091, nodeValue4092, nodeValue4093, nodeValue4094, nodeValue4096, nodeValue4097]
  ring

theorem reindexCheck26 : Integer.Sparse.reindex keyMap MixedData.row26 = numericRow26 := by decide +kernel

theorem numericCheck26 (x : Master → ℝ) : Integer.Sparse.eval numericRow26 x =
    (2160 : ℝ) * reducedSource26 x := by
  norm_num [numericRow26, reducedSource26, Integer.Sparse.eval, Sparse.eval, nodeValue5405, nodeValue5452, nodeValue5482, nodeValue5489, nodeValue5499]
  ring

theorem reindexCheck27 : Integer.Sparse.reindex keyMap MixedData.row27 = numericRow27 := by decide +kernel

theorem numericCheck27 (x : Master → ℝ) : Integer.Sparse.eval numericRow27 x =
    (1080 : ℝ) * reducedSource27 x := by
  norm_num [numericRow27, reducedSource27, Integer.Sparse.eval, Sparse.eval, nodeValue5423, nodeValue5424, nodeValue5433, nodeValue5477, nodeValue5478, nodeValue5482, nodeValue5490, nodeValue5497, nodeValue5499, nodeValue5500, nodeValue5501]
  ring

theorem reindexCheck29 : Integer.Sparse.reindex keyMap MixedData.row29 = numericRow29 := by decide +kernel

theorem numericCheck29 (x : Master → ℝ) : Integer.Sparse.eval numericRow29 x =
    (90 : ℝ) * reducedSource29 x := by
  norm_num [numericRow29, reducedSource29, Integer.Sparse.eval, Sparse.eval, nodeValue4091, nodeValue4092, nodeValue4093, nodeValue4095, nodeValue4096, nodeValue4097]
  ring

theorem reindexCheck30 : Integer.Sparse.reindex keyMap MixedData.row30 = numericRow30 := by decide +kernel

theorem numericCheck30 (x : Master → ℝ) : Integer.Sparse.eval numericRow30 x =
    (1 : ℝ) * reducedSource30 x := by
  norm_num [numericRow30, reducedSource30, Integer.Sparse.eval, Sparse.eval, nodeValue1092, nodeValue2063, nodeValue2285, nodeValue2294, nodeValue4085]

theorem reindexCheck31 : Integer.Sparse.reindex keyMap MixedData.row31 = numericRow31 := by decide +kernel

theorem numericCheck31 (x : Master → ℝ) : Integer.Sparse.eval numericRow31 x =
    (1 : ℝ) * reducedSource31 x := by
  norm_num [numericRow31, reducedSource31, Integer.Sparse.eval, Sparse.eval, nodeValue1067, nodeValue1069, nodeValue1092, nodeValue2285, nodeValue4085]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem rowSound18 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row18 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck18, numericCheck18, reducedZero18_e B hB hF, mul_zero]

theorem reducedZero25 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource25 (mixedVector B) = 0 := by
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  have h4093 : mixedVector B (Sum.inr 4093) = Sparse.eval nodeValue4093 (mixedVector B) := by
    change mixedMoment B node4093 node4093Labels = _
    exact sound4093 B hB hF
  have h4094 : mixedVector B (Sum.inr 4094) = Sparse.eval nodeValue4094 (mixedVector B) := by
    change mixedMoment B node4094 node4094Labels = _
    exact sound4094 B hB hF
  have h4096 : mixedVector B (Sum.inr 4096) = Sparse.eval nodeValue4096 (mixedVector B) := by
    change mixedMoment B node4096 node4096Labels = _
    exact sound4096 B hB hF
  have h4097 : mixedVector B (Sum.inr 4097) = Sparse.eval nodeValue4097 (mixedVector B) := by
    change mixedMoment B node4097 node4097Labels = _
    exact sound4097 B hB hF
  simpa only [sourceForm25, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4083, h4084, h4091, h4092, h4093, h4094, h4096, h4097, reducedSource25] using sourceEq25 B hB

theorem rowSound25 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row25 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck25, numericCheck25, reducedZero25 B hB hF, mul_zero]

theorem reducedZero26 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource26 (mixedVector B) = 0 := by
  have h5405 : mixedVector B (Sum.inr 5405) = Sparse.eval nodeValue5405 (mixedVector B) := by
    change mixedMoment B node5405 node5405Labels = _
    exact sound5405 B hB hF
  have h5452 : mixedVector B (Sum.inr 5452) = Sparse.eval nodeValue5452 (mixedVector B) := by
    change mixedMoment B node5452 node5452Labels = _
    exact sound5452_e B hB hF
  have h5482 : mixedVector B (Sum.inr 5482) = Sparse.eval nodeValue5482 (mixedVector B) := by
    change mixedMoment B node5482 node5482Labels = _
    exact sound5482_e B hB hF
  have h5489 : mixedVector B (Sum.inr 5489) = Sparse.eval nodeValue5489 (mixedVector B) := by
    change mixedMoment B node5489 node5489Labels = _
    exact sound5489 B hB hF
  have h5499 : mixedVector B (Sum.inr 5499) = Sparse.eval nodeValue5499 (mixedVector B) := by
    change mixedMoment B node5499 node5499Labels = _
    exact sound5499 B hB hF
  simpa only [sourceForm26, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5405, h5452, h5482, h5489, h5499, reducedSource26] using sourceEq26 B hB

theorem rowSound26 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row26 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck26, numericCheck26, reducedZero26 B hB hF, mul_zero]

theorem reducedZero27 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource27 (mixedVector B) = 0 := by
  have h5423 : mixedVector B (Sum.inr 5423) = Sparse.eval nodeValue5423 (mixedVector B) := by
    change mixedMoment B node5423 node5423Labels = _
    exact sound5423 B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433_e B hB hF
  have h5477 : mixedVector B (Sum.inr 5477) = Sparse.eval nodeValue5477 (mixedVector B) := by
    change mixedMoment B node5477 node5477Labels = _
    exact sound5477 B hB hF
  have h5478 : mixedVector B (Sum.inr 5478) = Sparse.eval nodeValue5478 (mixedVector B) := by
    change mixedMoment B node5478 node5478Labels = _
    exact sound5478 B hB hF
  have h5482 : mixedVector B (Sum.inr 5482) = Sparse.eval nodeValue5482 (mixedVector B) := by
    change mixedMoment B node5482 node5482Labels = _
    exact sound5482_e B hB hF
  have h5490 : mixedVector B (Sum.inr 5490) = Sparse.eval nodeValue5490 (mixedVector B) := by
    change mixedMoment B node5490 node5490Labels = _
    exact sound5490_e B hB hF
  have h5497 : mixedVector B (Sum.inr 5497) = Sparse.eval nodeValue5497 (mixedVector B) := by
    change mixedMoment B node5497 node5497Labels = _
    exact sound5497 B hB hF
  have h5499 : mixedVector B (Sum.inr 5499) = Sparse.eval nodeValue5499 (mixedVector B) := by
    change mixedMoment B node5499 node5499Labels = _
    exact sound5499 B hB hF
  have h5500 : mixedVector B (Sum.inr 5500) = Sparse.eval nodeValue5500 (mixedVector B) := by
    change mixedMoment B node5500 node5500Labels = _
    exact sound5500_e B hB hF
  have h5501 : mixedVector B (Sum.inr 5501) = Sparse.eval nodeValue5501 (mixedVector B) := by
    change mixedMoment B node5501 node5501Labels = _
    exact sound5501 B hB hF
  simpa only [sourceForm27, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5423, h5424, h5433, h5477, h5478, h5482, h5490, h5497, h5499, h5500, h5501, reducedSource27] using sourceEq27 B hB

theorem rowSound27 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row27 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck27, numericCheck27, reducedZero27 B hB hF, mul_zero]

theorem reducedZero29 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource29 (mixedVector B) = 0 := by
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  have h4093 : mixedVector B (Sum.inr 4093) = Sparse.eval nodeValue4093 (mixedVector B) := by
    change mixedMoment B node4093 node4093Labels = _
    exact sound4093 B hB hF
  have h4095 : mixedVector B (Sum.inr 4095) = Sparse.eval nodeValue4095 (mixedVector B) := by
    change mixedMoment B node4095 node4095Labels = _
    exact sound4095 B hB hF
  have h4096 : mixedVector B (Sum.inr 4096) = Sparse.eval nodeValue4096 (mixedVector B) := by
    change mixedMoment B node4096 node4096Labels = _
    exact sound4096 B hB hF
  have h4097 : mixedVector B (Sum.inr 4097) = Sparse.eval nodeValue4097 (mixedVector B) := by
    change mixedMoment B node4097 node4097Labels = _
    exact sound4097 B hB hF
  simpa only [sourceForm29, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4091, h4092, h4093, h4095, h4096, h4097, reducedSource29] using sourceEq29 B hB

theorem rowSound29 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row29 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck29, numericCheck29, reducedZero29 B hB hF, mul_zero]

theorem reducedZero30 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource30 (mixedVector B) = 0 := by
  have h1092 : mixedVector B (Sum.inr 1092) = Sparse.eval nodeValue1092 (mixedVector B) := by
    change mixedMoment B node1092 node1092Labels = _
    exact sound1092 B hB hF
  have h2063 : mixedVector B (Sum.inr 2063) = Sparse.eval nodeValue2063 (mixedVector B) := by
    change mixedMoment B node2063 node2063Labels = _
    exact sound2063 B hB hF
  have h2285 : mixedVector B (Sum.inr 2285) = Sparse.eval nodeValue2285 (mixedVector B) := by
    change mixedMoment B node2285 node2285Labels = _
    exact sound2285 B hB hF
  have h2294 : mixedVector B (Sum.inr 2294) = Sparse.eval nodeValue2294 (mixedVector B) := by
    change mixedMoment B node2294 node2294Labels = _
    exact sound2294 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm32, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1092, h2063, h2285, h2294, h4085, reducedSource30] using sourceEq32 B hB

theorem rowSound30 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row30 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck30, numericCheck30, reducedZero30 B hB hF, mul_zero]

theorem reducedZero31 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource31 (mixedVector B) = 0 := by
  have h1067 : mixedVector B (Sum.inr 1067) = Sparse.eval nodeValue1067 (mixedVector B) := by
    change mixedMoment B node1067 node1067Labels = _
    exact sound1067 B hB hF
  have h1069 : mixedVector B (Sum.inr 1069) = Sparse.eval nodeValue1069 (mixedVector B) := by
    change mixedMoment B node1069 node1069Labels = _
    exact sound1069 B hB hF
  have h1092 : mixedVector B (Sum.inr 1092) = Sparse.eval nodeValue1092 (mixedVector B) := by
    change mixedMoment B node1092 node1092Labels = _
    exact sound1092 B hB hF
  have h2285 : mixedVector B (Sum.inr 2285) = Sparse.eval nodeValue2285 (mixedVector B) := by
    change mixedMoment B node2285 node2285Labels = _
    exact sound2285 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm33, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1067, h1069, h1092, h2285, h4085, reducedSource31] using sourceEq33 B hB

theorem rowSound31 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row31 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck31, numericCheck31, reducedZero31 B hB hF, mul_zero]

theorem sourceRowsAt16 : MixedData.sourceRows (16 : Fin 2425) =
    MixedData.row16 := by decide +kernel

theorem sourceRowsAt17 : MixedData.sourceRows (17 : Fin 2425) =
    MixedData.row17 := by decide +kernel

theorem sourceRowsAt18 : MixedData.sourceRows (18 : Fin 2425) =
    MixedData.row18 := by decide +kernel

theorem sourceRowsAt19 : MixedData.sourceRows (19 : Fin 2425) =
    MixedData.row19 := by decide +kernel

theorem sourceRowsAt20 : MixedData.sourceRows (20 : Fin 2425) =
    MixedData.row20 := by decide +kernel

theorem sourceRowsAt21 : MixedData.sourceRows (21 : Fin 2425) =
    MixedData.row21 := by decide +kernel

theorem sourceRowsAt22 : MixedData.sourceRows (22 : Fin 2425) =
    MixedData.row22 := by decide +kernel

theorem sourceRowsAt23 : MixedData.sourceRows (23 : Fin 2425) =
    MixedData.row23 := by decide +kernel

theorem sourceRowsAt24 : MixedData.sourceRows (24 : Fin 2425) =
    MixedData.row24 := by decide +kernel

theorem sourceRowsAt25 : MixedData.sourceRows (25 : Fin 2425) =
    MixedData.row25 := by decide +kernel

theorem sourceRowsAt26 : MixedData.sourceRows (26 : Fin 2425) =
    MixedData.row26 := by decide +kernel

theorem sourceRowsAt27 : MixedData.sourceRows (27 : Fin 2425) =
    MixedData.row27 := by decide +kernel

theorem sourceRowsAt28 : MixedData.sourceRows (28 : Fin 2425) =
    MixedData.row28 := by decide +kernel

theorem sourceRowsAt29 : MixedData.sourceRows (29 : Fin 2425) =
    MixedData.row29 := by decide +kernel

theorem sourceRowsAt30 : MixedData.sourceRows (30 : Fin 2425) =
    MixedData.row30 := by decide +kernel

theorem sourceRowsAt31 : MixedData.sourceRows (31 : Fin 2425) =
    MixedData.row31 := by decide +kernel

theorem chunkSound1_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 1) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 16 ∨ k.val = 17 ∨ k.val = 18 ∨ k.val = 19 ∨ k.val = 20 ∨ k.val = 21 ∨ k.val = 22 ∨ k.val = 23 ∨ k.val = 24 ∨ k.val = 25 ∨ k.val = 26 ∨ k.val = 27 ∨ k.val = 28 ∨ k.val = 29 ∨ k.val = 30 ∨ k.val = 31 := by omega
  rcases heq with h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31
  · have he : k = (16 : Fin 2425) := Fin.ext h16
    subst k
    rw [sourceRowsAt16]
    exact rowSound16_e B hB hF
  · have he : k = (17 : Fin 2425) := Fin.ext h17
    subst k
    rw [sourceRowsAt17]
    exact rowSound17_e B hB hF
  · have he : k = (18 : Fin 2425) := Fin.ext h18
    subst k
    rw [sourceRowsAt18]
    exact rowSound18 B hB hF
  · have he : k = (19 : Fin 2425) := Fin.ext h19
    subst k
    rw [sourceRowsAt19]
    exact rowSound19_e B hB hF
  · have he : k = (20 : Fin 2425) := Fin.ext h20
    subst k
    rw [sourceRowsAt20]
    exact rowSound20_e B hB hF
  · have he : k = (21 : Fin 2425) := Fin.ext h21
    subst k
    rw [sourceRowsAt21]
    exact rowSound21_e B hB hF
  · have he : k = (22 : Fin 2425) := Fin.ext h22
    subst k
    rw [sourceRowsAt22]
    exact rowSound22_e B hB hF
  · have he : k = (23 : Fin 2425) := Fin.ext h23
    subst k
    rw [sourceRowsAt23]
    exact rowSound23_e B hB hF
  · have he : k = (24 : Fin 2425) := Fin.ext h24
    subst k
    rw [sourceRowsAt24]
    exact rowSound24_e B hB hF
  · have he : k = (25 : Fin 2425) := Fin.ext h25
    subst k
    rw [sourceRowsAt25]
    exact rowSound25 B hB hF
  · have he : k = (26 : Fin 2425) := Fin.ext h26
    subst k
    rw [sourceRowsAt26]
    exact rowSound26 B hB hF
  · have he : k = (27 : Fin 2425) := Fin.ext h27
    subst k
    rw [sourceRowsAt27]
    exact rowSound27 B hB hF
  · have he : k = (28 : Fin 2425) := Fin.ext h28
    subst k
    rw [sourceRowsAt28]
    exact rowSound28_e B hB hF
  · have he : k = (29 : Fin 2425) := Fin.ext h29
    subst k
    rw [sourceRowsAt29]
    exact rowSound29 B hB hF
  · have he : k = (30 : Fin 2425) := Fin.ext h30
    subst k
    rw [sourceRowsAt30]
    exact rowSound30 B hB hF
  · have he : k = (31 : Fin 2425) := Fin.ext h31
    subst k
    rw [sourceRowsAt31]
    exact rowSound31 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1_e_oai
