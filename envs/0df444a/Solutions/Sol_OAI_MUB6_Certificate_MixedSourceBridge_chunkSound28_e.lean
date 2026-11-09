-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:06:11.108386+00:00
-- url     : https://prove2.me/submissions/a6f9d3b9-0cd7-46eb-b61f-1b53111155b6

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E127
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound448_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound452_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound453_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound454_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound456_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound462_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound463_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1743 raw1743Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw1743 raw1743Labels = mixedMoment B raw1743step0 raw1743step0Labels := by
      have ha : raw1743step0 = (fun i j => raw1743 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1743step0 raw1743; decide +kernel
      have hl : raw1743step0Labels = raw1743Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1743 raw1743Labels permutation32 permutation4
    mixedMoment B raw1743step0 raw1743step0Labels = mixedMoment B raw1743step1 raw1743step1Labels := by
      have ha : raw1743step1 = raw1743step0 := by apply Matrix.ext; unfold raw1743step1 raw1743step0; decide +kernel
      have hl : raw1743step0Labels = labelEmbedding7 ∘ raw1743step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1743step0 raw1743step0Labels raw1743step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical1744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1744 raw1744Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw1744 raw1744Labels = mixedMoment B raw1744step0 raw1744step0Labels := by
      have ha : raw1744step0 = (fun i j => raw1744 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1744step0 raw1744; decide +kernel
      have hl : raw1744step0Labels = raw1744Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1744 raw1744Labels permutation32 permutation4
    _ = mixedMoment B node2025 node2025Labels := by rfl

theorem canonical1745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1745 raw1745Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw1745 raw1745Labels = mixedMoment B raw1745step0 raw1745step0Labels := by
      have ha : raw1745step0 = (fun i j => raw1745 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1745step0 raw1745; decide +kernel
      have hl : raw1745step0Labels = raw1745Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1745 raw1745Labels permutation32 permutation6
    mixedMoment B raw1745step0 raw1745step0Labels = mixedMoment B raw1745step1 raw1745step1Labels := by
      have ha : raw1745step1 = -raw1745step0 := by apply Matrix.ext; change ∀ i j, raw1745step1 i j = -(raw1745step0 i j); unfold raw1745step1 raw1745step0; decide +kernel
      have hl : raw1745step1Labels = raw1745step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1745step1 raw1745step1Labels = mixedMoment B raw1745step2 raw1745step2Labels := by
      have ha : raw1745step2 = raw1745step1 := by apply Matrix.ext; unfold raw1745step2 raw1745step1; decide +kernel
      have hl : raw1745step1Labels = labelEmbedding1 ∘ raw1745step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1745step1 raw1745step1Labels raw1745step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

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

theorem canonical2280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2280 raw2280Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw2280 raw2280Labels = mixedMoment B raw2280step0 raw2280step0Labels := by
      have ha : raw2280step0 = (fun i j => raw2280 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2280step0 raw2280; decide +kernel
      have hl : raw2280step0Labels = raw2280Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2280 raw2280Labels permutation32 permutation4
    mixedMoment B raw2280step0 raw2280step0Labels = mixedMoment B raw2280step1 raw2280step1Labels := by
      have ha : raw2280step1 = raw2280step0 := by apply Matrix.ext; unfold raw2280step1 raw2280step0; decide +kernel
      have hl : raw2280step0Labels = labelEmbedding7 ∘ raw2280step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2280step0 raw2280step0Labels raw2280step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical2281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2281 raw2281Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw2281 raw2281Labels = mixedMoment B raw2281step0 raw2281step0Labels := by
      have ha : raw2281step0 = (fun i j => raw2281 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2281step0 raw2281; decide +kernel
      have hl : raw2281step0Labels = raw2281Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2281 raw2281Labels permutation32 permutation4
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical2282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2282 raw2282Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw2282 raw2282Labels = mixedMoment B raw2282step0 raw2282step0Labels := by
      have ha : raw2282step0 = (fun i j => raw2282 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2282step0 raw2282; decide +kernel
      have hl : raw2282step0Labels = raw2282Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2282 raw2282Labels permutation32 permutation6
    mixedMoment B raw2282step0 raw2282step0Labels = mixedMoment B raw2282step1 raw2282step1Labels := by
      have ha : raw2282step1 = -raw2282step0 := by apply Matrix.ext; change ∀ i j, raw2282step1 i j = -(raw2282step0 i j); unfold raw2282step1 raw2282step0; decide +kernel
      have hl : raw2282step1Labels = raw2282step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2282step1 raw2282step1Labels = mixedMoment B raw2282step2 raw2282step2Labels := by
      have ha : raw2282step2 = raw2282step1 := by apply Matrix.ext; unfold raw2282step2 raw2282step1; decide +kernel
      have hl : raw2282step1Labels = labelEmbedding1 ∘ raw2282step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2282step1 raw2282step1Labels raw2282step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

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

theorem canonical2322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2322 raw2322Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw2322 raw2322Labels = mixedMoment B raw2322step0 raw2322step0Labels := by
      have ha : raw2322step0 = (fun i j => raw2322 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2322step0 raw2322; decide +kernel
      have hl : raw2322step0Labels = raw2322Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2322 raw2322Labels permutation8 permutation4
    mixedMoment B raw2322step0 raw2322step0Labels = mixedMoment B raw2322step1 raw2322step1Labels := by
      have ha : raw2322step1 = raw2322step0 := by apply Matrix.ext; unfold raw2322step1 raw2322step0; decide +kernel
      have hl : raw2322step0Labels = labelEmbedding7 ∘ raw2322step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2322step0 raw2322step0Labels raw2322step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

theorem canonical2323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2323 raw2323Labels = mixedMoment B node2784 node2784Labels := by
  calc
    mixedMoment B raw2323 raw2323Labels = mixedMoment B raw2323step0 raw2323step0Labels := by
      have ha : raw2323step0 = (fun i j => raw2323 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2323step0 raw2323; decide +kernel
      have hl : raw2323step0Labels = raw2323Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2323 raw2323Labels permutation8 permutation4
    _ = mixedMoment B node2784 node2784Labels := by rfl

theorem canonical2324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2324 raw2324Labels = mixedMoment B node3623 node3623Labels := by
  calc
    mixedMoment B raw2324 raw2324Labels = mixedMoment B raw2324step0 raw2324step0Labels := by
      have ha : raw2324step0 = (fun i j => raw2324 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2324step0 raw2324; decide +kernel
      have hl : raw2324step0Labels = raw2324Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2324 raw2324Labels permutation8 permutation6
    mixedMoment B raw2324step0 raw2324step0Labels = mixedMoment B raw2324step1 raw2324step1Labels := by
      have ha : raw2324step1 = -raw2324step0 := by apply Matrix.ext; change ∀ i j, raw2324step1 i j = -(raw2324step0 i j); unfold raw2324step1 raw2324step0; decide +kernel
      have hl : raw2324step1Labels = raw2324step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2324step1 raw2324step1Labels = mixedMoment B raw2324step2 raw2324step2Labels := by
      have ha : raw2324step2 = raw2324step1 := by apply Matrix.ext; unfold raw2324step2 raw2324step1; decide +kernel
      have hl : raw2324step1Labels = labelEmbedding1 ∘ raw2324step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2324step1 raw2324step1Labels raw2324step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3623 node3623Labels := by rfl

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

theorem canonical282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw282 raw282Labels = mixedMoment B node2784 node2784Labels := by
  calc
    mixedMoment B raw282 raw282Labels = mixedMoment B raw282step0 raw282step0Labels := by
      have ha : raw282step0 = (fun i j => raw282 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw282step0 raw282; decide +kernel
      have hl : raw282step0Labels = raw282Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw282 raw282Labels permutation8 permutation5
    mixedMoment B raw282step0 raw282step0Labels = mixedMoment B raw282step1 raw282step1Labels := by
      have ha : raw282step1 = raw282step0 := by apply Matrix.ext; unfold raw282step1 raw282step0; decide +kernel
      have hl : raw282step0Labels = labelEmbedding1 ∘ raw282step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw282step0 raw282step0Labels raw282step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2784 node2784Labels := by rfl

theorem canonical283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw283 raw283Labels = mixedMoment B node416 node416Labels := by
  calc
    mixedMoment B raw283 raw283Labels = mixedMoment B raw283step0 raw283step0Labels := by
      have ha : raw283step0 = (fun i j => raw283 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw283step0 raw283; decide +kernel
      have hl : raw283step0Labels = raw283Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw283 raw283Labels permutation8 permutation5
    _ = mixedMoment B node416 node416Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5749 raw5749Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw5749 raw5749Labels = mixedMoment B raw5749step0 raw5749step0Labels := by
      have hz : ∀ j, raw5749 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5749step0 = (fun i j => raw5749 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5749step0 raw5749; decide +kernel
      have hl : raw5749step0Labels = raw5749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5749 raw5749Labels permutation265 hz
    mixedMoment B raw5749step0 raw5749step0Labels = mixedMoment B raw5749step1 raw5749step1Labels := by
      have ha : raw5749step1 = (fun i j => raw5749step0 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5749step1 raw5749step0; decide +kernel
      have hl : raw5749step1Labels = raw5749step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5749step0 raw5749step0Labels permutation48 permutation4
    mixedMoment B raw5749step1 raw5749step1Labels = mixedMoment B raw5749step2 raw5749step2Labels := by
      have ha : raw5749step2 = -raw5749step1 := by apply Matrix.ext; change ∀ i j, raw5749step2 i j = -(raw5749step1 i j); unfold raw5749step2 raw5749step1; decide +kernel
      have hl : raw5749step2Labels = raw5749step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3625 node3625Labels := by rfl

theorem canonical5754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5754 raw5754Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw5754 raw5754Labels = mixedMoment B raw5754step0 raw5754step0Labels := by
      have hz : ∀ j, raw5754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5754step0 = (fun i j => raw5754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5754step0 raw5754; decide +kernel
      have hl : raw5754step0Labels = raw5754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754 raw5754Labels permutation434 hz
    mixedMoment B raw5754step0 raw5754step0Labels = mixedMoment B raw5754step1 raw5754step1Labels := by
      have hz : ∀ j, raw5754step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5754step1 = (fun i j => raw5754step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5754step1 raw5754step0; decide +kernel
      have hl : raw5754step1Labels = raw5754step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754step0 raw5754step0Labels permutation80 hz
    mixedMoment B raw5754step1 raw5754step1Labels = mixedMoment B raw5754step2 raw5754step2Labels := by
      have hz : ∀ j, raw5754step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5754step2 = (fun i j => raw5754step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5754step2 raw5754step1; decide +kernel
      have hl : raw5754step2Labels = raw5754step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754step1 raw5754step1Labels permutation14 hz
    mixedMoment B raw5754step2 raw5754step2Labels = mixedMoment B raw5754step3 raw5754step3Labels := by
      have ha : raw5754step3 = -raw5754step2 := by apply Matrix.ext; change ∀ i j, raw5754step3 i j = -(raw5754step2 i j); unfold raw5754step3 raw5754step2; decide +kernel
      have hl : raw5754step3Labels = raw5754step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7278 raw7278Labels = mixedMoment B node3493 node3493Labels := by
  calc
    mixedMoment B raw7278 raw7278Labels = mixedMoment B raw7278step0 raw7278step0Labels := by
      have ha : raw7278step0 = (fun i j => raw7278 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7278step0 raw7278; decide +kernel
      have hl : raw7278step0Labels = raw7278Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7278 raw7278Labels permutation182 permutation2
    mixedMoment B raw7278step0 raw7278step0Labels = mixedMoment B raw7278step1 raw7278step1Labels := by
      have ha : raw7278step1 = -raw7278step0 := by apply Matrix.ext; change ∀ i j, raw7278step1 i j = -(raw7278step0 i j); unfold raw7278step1 raw7278step0; decide +kernel
      have hl : raw7278step1Labels = raw7278step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3493 node3493Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7960 raw7960Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw7960 raw7960Labels = mixedMoment B raw7960step0 raw7960step0Labels := by
      have hz : ∀ j, raw7960 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7960step0 = (fun i j => raw7960 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7960step0 raw7960; decide +kernel
      have hl : raw7960step0Labels = raw7960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7960 raw7960Labels permutation346 hz
    mixedMoment B raw7960step0 raw7960step0Labels = mixedMoment B raw7960step1 raw7960step1Labels := by
      have hz : ∀ j, raw7960step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7960step1 = (fun i j => raw7960step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7960step1 raw7960step0; decide +kernel
      have hl : raw7960step1Labels = raw7960step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7960step0 raw7960step0Labels permutation56 hz
    mixedMoment B raw7960step1 raw7960step1Labels = mixedMoment B raw7960step2 raw7960step2Labels := by
      have ha : raw7960step2 = -raw7960step1 := by apply Matrix.ext; change ∀ i j, raw7960step2 i j = -(raw7960step1 i j); unfold raw7960step2 raw7960step1; decide +kernel
      have hl : raw7960step2Labels = raw7960step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3547 node3547Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9076 raw9076Labels = mixedMoment B node3498 node3498Labels := by
  calc
    mixedMoment B raw9076 raw9076Labels = mixedMoment B raw9076step0 raw9076step0Labels := by
      have hz : ∀ j, raw9076 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9076step0 = (fun i j => raw9076 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9076step0 raw9076; decide +kernel
      have hl : raw9076step0Labels = raw9076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9076 raw9076Labels permutation265 hz
    mixedMoment B raw9076step0 raw9076step0Labels = mixedMoment B raw9076step1 raw9076step1Labels := by
      have ha : raw9076step1 = -raw9076step0 := by apply Matrix.ext; change ∀ i j, raw9076step1 i j = -(raw9076step0 i j); unfold raw9076step1 raw9076step0; decide +kernel
      have hl : raw9076step1Labels = raw9076step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3498 node3498Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9218 raw9218Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw9218 raw9218Labels = mixedMoment B raw9218step0 raw9218step0Labels := by
      have hz : ∀ j, raw9218 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9218step0 = (fun i j => raw9218 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9218step0 raw9218; decide +kernel
      have hl : raw9218step0Labels = raw9218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9218 raw9218Labels permutation265 hz
    _ = mixedMoment B node3077 node3077Labels := by rfl

theorem canonical9219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9219 raw9219Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw9219 raw9219Labels = mixedMoment B raw9219step0 raw9219step0Labels := by
      have ha : raw9219step0 = (fun i j => raw9219 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9219step0 raw9219; decide +kernel
      have hl : raw9219step0Labels = raw9219Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9219 raw9219Labels permutation682 permutation2
    mixedMoment B raw9219step0 raw9219step0Labels = mixedMoment B raw9219step1 raw9219step1Labels := by
      have ha : raw9219step1 = -raw9219step0 := by apply Matrix.ext; change ∀ i j, raw9219step1 i j = -(raw9219step0 i j); unfold raw9219step1 raw9219step0; decide +kernel
      have hl : raw9219step1Labels = raw9219step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3800 node3800Labels := by rfl

theorem canonical9220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9220 raw9220Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw9220 raw9220Labels = mixedMoment B raw9220step0 raw9220step0Labels := by
      have hz : ∀ j, raw9220 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9220step0 = (fun i j => raw9220 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9220step0 raw9220; decide +kernel
      have hl : raw9220step0Labels = raw9220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9220 raw9220Labels permutation265 hz
    mixedMoment B raw9220step0 raw9220step0Labels = mixedMoment B raw9220step1 raw9220step1Labels := by
      have ha : raw9220step1 = (fun i j => raw9220step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9220step1 raw9220step0; decide +kernel
      have hl : raw9220step1Labels = raw9220step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9220step0 raw9220step0Labels permutation151 permutation2
    mixedMoment B raw9220step1 raw9220step1Labels = mixedMoment B raw9220step2 raw9220step2Labels := by
      have ha : raw9220step2 = -raw9220step1 := by apply Matrix.ext; change ∀ i j, raw9220step2 i j = -(raw9220step1 i j); unfold raw9220step2 raw9220step1; decide +kernel
      have hl : raw9220step2Labels = raw9220step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3808 node3808Labels := by rfl

theorem canonical9221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9221 raw9221Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw9221 raw9221Labels = mixedMoment B raw9221step0 raw9221step0Labels := by
      have hz : ∀ j, raw9221 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9221step0 = (fun i j => raw9221 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9221step0 raw9221; decide +kernel
      have hl : raw9221step0Labels = raw9221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9221 raw9221Labels permutation265 hz
    mixedMoment B raw9221step0 raw9221step0Labels = mixedMoment B raw9221step1 raw9221step1Labels := by
      have ha : raw9221step1 = (fun i j => raw9221step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9221step1 raw9221step0; decide +kernel
      have hl : raw9221step1Labels = raw9221step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9221step0 raw9221step0Labels permutation149 permutation2
    mixedMoment B raw9221step1 raw9221step1Labels = mixedMoment B raw9221step2 raw9221step2Labels := by
      have ha : raw9221step2 = -raw9221step1 := by apply Matrix.ext; change ∀ i j, raw9221step2 i j = -(raw9221step1 i j); unfold raw9221step2 raw9221step1; decide +kernel
      have hl : raw9221step2Labels = raw9221step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3808 node3808Labels := by rfl

theorem canonical9222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9222 raw9222Labels = mixedMoment B node3902 node3902Labels := by
  calc
    mixedMoment B raw9222 raw9222Labels = mixedMoment B raw9222step0 raw9222step0Labels := by
      have hz : ∀ j, raw9222 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9222step0 = (fun i j => raw9222 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9222step0 raw9222; decide +kernel
      have hl : raw9222step0Labels = raw9222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9222 raw9222Labels permutation265 hz
    mixedMoment B raw9222step0 raw9222step0Labels = mixedMoment B raw9222step1 raw9222step1Labels := by
      have ha : raw9222step1 = (fun i j => raw9222step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9222step1 raw9222step0; decide +kernel
      have hl : raw9222step1Labels = raw9222step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9222step0 raw9222step0Labels permutation149 permutation2
    mixedMoment B raw9222step1 raw9222step1Labels = mixedMoment B raw9222step2 raw9222step2Labels := by
      have ha : raw9222step2 = -raw9222step1 := by apply Matrix.ext; change ∀ i j, raw9222step2 i j = -(raw9222step1 i j); unfold raw9222step2 raw9222step1; decide +kernel
      have hl : raw9222step2Labels = raw9222step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3902 node3902Labels := by rfl

theorem canonical9223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9223 raw9223Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw9223 raw9223Labels = mixedMoment B raw9223step0 raw9223step0Labels := by
      have hz : ∀ j, raw9223 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9223step0 = (fun i j => raw9223 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9223step0 raw9223; decide +kernel
      have hl : raw9223step0Labels = raw9223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9223 raw9223Labels permutation265 hz
    _ = mixedMoment B node4010 node4010Labels := by rfl

theorem canonical9224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9224 raw9224Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw9224 raw9224Labels = mixedMoment B raw9224step0 raw9224step0Labels := by
      have hz : ∀ j, raw9224 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9224step0 = (fun i j => raw9224 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9224step0 raw9224; decide +kernel
      have hl : raw9224step0Labels = raw9224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9224 raw9224Labels permutation265 hz
    mixedMoment B raw9224step0 raw9224step0Labels = mixedMoment B raw9224step1 raw9224step1Labels := by
      have ha : raw9224step1 = (fun i j => raw9224step0 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw9224step1 raw9224step0; decide +kernel
      have hl : raw9224step1Labels = raw9224step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9224step0 raw9224step0Labels permutation146 permutation0
    mixedMoment B raw9224step1 raw9224step1Labels = mixedMoment B raw9224step2 raw9224step2Labels := by
      have ha : raw9224step2 = -raw9224step1 := by apply Matrix.ext; change ∀ i j, raw9224step2 i j = -(raw9224step1 i j); unfold raw9224step2 raw9224step1; decide +kernel
      have hl : raw9224step2Labels = raw9224step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical9225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9225 raw9225Labels = mixedMoment B node1383 node1383Labels := by
  calc
    mixedMoment B raw9225 raw9225Labels = mixedMoment B raw9225step0 raw9225step0Labels := by
      have ha : raw9225step0 = (fun i j => raw9225 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9225step0 raw9225; decide +kernel
      have hl : raw9225step0Labels = raw9225Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9225 raw9225Labels permutation182 permutation2
    _ = mixedMoment B node1383 node1383Labels := by rfl

theorem canonical9226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9226 raw9226Labels = mixedMoment B node1406 node1406Labels := by
  calc
    mixedMoment B raw9226 raw9226Labels = mixedMoment B raw9226step0 raw9226step0Labels := by
      have hz : ∀ j, raw9226 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9226step0 = (fun i j => raw9226 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9226step0 raw9226; decide +kernel
      have hl : raw9226step0Labels = raw9226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9226 raw9226Labels permutation265 hz
    mixedMoment B raw9226step0 raw9226step0Labels = mixedMoment B raw9226step1 raw9226step1Labels := by
      have ha : raw9226step1 = (fun i j => raw9226step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9226step1 raw9226step0; decide +kernel
      have hl : raw9226step1Labels = raw9226step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9226step0 raw9226step0Labels permutation38 permutation2
    _ = mixedMoment B node1406 node1406Labels := by rfl

theorem canonical9227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9227 raw9227Labels = mixedMoment B node1406 node1406Labels := by
  calc
    mixedMoment B raw9227 raw9227Labels = mixedMoment B raw9227step0 raw9227step0Labels := by
      have hz : ∀ j, raw9227 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9227step0 = (fun i j => raw9227 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9227step0 raw9227; decide +kernel
      have hl : raw9227step0Labels = raw9227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9227 raw9227Labels permutation265 hz
    _ = mixedMoment B node1406 node1406Labels := by rfl

theorem canonical9228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9228 raw9228Labels = mixedMoment B node1391 node1391Labels := by
  calc
    mixedMoment B raw9228 raw9228Labels = mixedMoment B raw9228step0 raw9228step0Labels := by
      have hz : ∀ j, raw9228 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9228step0 = (fun i j => raw9228 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9228step0 raw9228; decide +kernel
      have hl : raw9228step0Labels = raw9228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9228 raw9228Labels permutation265 hz
    _ = mixedMoment B node1391 node1391Labels := by rfl

theorem canonical9229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9229 raw9229Labels = mixedMoment B node1388 node1388Labels := by
  calc
    mixedMoment B raw9229 raw9229Labels = mixedMoment B raw9229step0 raw9229step0Labels := by
      have hz : ∀ j, raw9229 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9229step0 = (fun i j => raw9229 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9229step0 raw9229; decide +kernel
      have hl : raw9229step0Labels = raw9229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9229 raw9229Labels permutation265 hz
    _ = mixedMoment B node1388 node1388Labels := by rfl

theorem canonical9230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9230 raw9230Labels = mixedMoment B node2984 node2984Labels := by
  calc
    mixedMoment B raw9230 raw9230Labels = mixedMoment B raw9230step0 raw9230step0Labels := by
      have ha : raw9230step0 = (fun i j => raw9230 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9230step0 raw9230; decide +kernel
      have hl : raw9230step0Labels = raw9230Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9230 raw9230Labels permutation158 permutation2
    _ = mixedMoment B node2984 node2984Labels := by rfl

theorem canonical9231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9231 raw9231Labels = mixedMoment B node2984 node2984Labels := by
  calc
    _ = mixedMoment B node2984 node2984Labels := by rfl

theorem canonical9232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9232 raw9232Labels = mixedMoment B node2981 node2981Labels := by
  calc
    _ = mixedMoment B node2981 node2981Labels := by rfl

theorem canonical9233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9233 raw9233Labels = mixedMoment B node2470 node2470Labels := by
  calc
    mixedMoment B raw9233 raw9233Labels = mixedMoment B raw9233step0 raw9233step0Labels := by
      have ha : raw9233step0 = (fun i j => raw9233 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9233step0 raw9233; decide +kernel
      have hl : raw9233step0Labels = raw9233Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9233 raw9233Labels permutation682 permutation2
    mixedMoment B raw9233step0 raw9233step0Labels = mixedMoment B raw9233step1 raw9233step1Labels := by
      have ha : raw9233step1 = -raw9233step0 := by apply Matrix.ext; change ∀ i j, raw9233step1 i j = -(raw9233step0 i j); unfold raw9233step1 raw9233step0; decide +kernel
      have hl : raw9233step1Labels = raw9233step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2470 node2470Labels := by rfl

theorem canonical9250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9250 raw9250Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw9250 raw9250Labels = mixedMoment B raw9250step0 raw9250step0Labels := by
      have hz : ∀ j, raw9250 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9250step0 = (fun i j => raw9250 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9250step0 raw9250; decide +kernel
      have hl : raw9250step0Labels = raw9250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9250 raw9250Labels permutation434 hz
    mixedMoment B raw9250step0 raw9250step0Labels = mixedMoment B raw9250step1 raw9250step1Labels := by
      have hz : ∀ j, raw9250step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9250step1 = (fun i j => raw9250step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9250step1 raw9250step0; decide +kernel
      have hl : raw9250step1Labels = raw9250step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9250step0 raw9250step0Labels permutation56 hz
    mixedMoment B raw9250step1 raw9250step1Labels = mixedMoment B raw9250step2 raw9250step2Labels := by
      have ha : raw9250step2 = -raw9250step1 := by apply Matrix.ext; change ∀ i j, raw9250step2 i j = -(raw9250step1 i j); unfold raw9250step2 raw9250step1; decide +kernel
      have hl : raw9250step2Labels = raw9250step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3547 node3547Labels := by rfl

theorem canonical9251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9251 raw9251Labels = mixedMoment B node2509 node2509Labels := by
  calc
    mixedMoment B raw9251 raw9251Labels = mixedMoment B raw9251step0 raw9251step0Labels := by
      have hz : ∀ j, raw9251 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9251step0 = (fun i j => raw9251 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9251step0 raw9251; decide +kernel
      have hl : raw9251step0Labels = raw9251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9251 raw9251Labels permutation265 hz
    mixedMoment B raw9251step0 raw9251step0Labels = mixedMoment B raw9251step1 raw9251step1Labels := by
      have ha : raw9251step1 = (fun i j => raw9251step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9251step1 raw9251step0; decide +kernel
      have hl : raw9251step1Labels = raw9251step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9251step0 raw9251step0Labels permutation149 permutation2
    _ = mixedMoment B node2509 node2509Labels := by rfl

theorem canonical9342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9342 raw9342Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw9342 raw9342Labels = mixedMoment B raw9342step0 raw9342step0Labels := by
      have hz : ∀ j, raw9342 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9342step0 = (fun i j => raw9342 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9342step0 raw9342; decide +kernel
      have hl : raw9342step0Labels = raw9342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9342 raw9342Labels permutation265 hz
    _ = mixedMoment B node2754 node2754Labels := by rfl

theorem canonical9343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9343 raw9343Labels = mixedMoment B node1250 node1250Labels := by
  calc
    mixedMoment B raw9343 raw9343Labels = mixedMoment B raw9343step0 raw9343step0Labels := by
      have ha : raw9343step0 = (fun i j => raw9343 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9343step0 raw9343; decide +kernel
      have hl : raw9343step0Labels = raw9343Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9343 raw9343Labels permutation182 permutation2
    _ = mixedMoment B node1250 node1250Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9344 raw9344Labels = mixedMoment B node1270 node1270Labels := by
  calc
    mixedMoment B raw9344 raw9344Labels = mixedMoment B raw9344step0 raw9344step0Labels := by
      have hz : ∀ j, raw9344 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9344step0 = (fun i j => raw9344 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9344step0 raw9344; decide +kernel
      have hl : raw9344step0Labels = raw9344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9344 raw9344Labels permutation265 hz
    mixedMoment B raw9344step0 raw9344step0Labels = mixedMoment B raw9344step1 raw9344step1Labels := by
      have ha : raw9344step1 = (fun i j => raw9344step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9344step1 raw9344step0; decide +kernel
      have hl : raw9344step1Labels = raw9344step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9344step0 raw9344step0Labels permutation38 permutation2
    _ = mixedMoment B node1270 node1270Labels := by rfl

theorem canonical9345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9345 raw9345Labels = mixedMoment B node1270 node1270Labels := by
  calc
    mixedMoment B raw9345 raw9345Labels = mixedMoment B raw9345step0 raw9345step0Labels := by
      have hz : ∀ j, raw9345 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9345step0 = (fun i j => raw9345 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9345step0 raw9345; decide +kernel
      have hl : raw9345step0Labels = raw9345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9345 raw9345Labels permutation265 hz
    _ = mixedMoment B node1270 node1270Labels := by rfl

theorem canonical9346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9346 raw9346Labels = mixedMoment B node1253 node1253Labels := by
  calc
    mixedMoment B raw9346 raw9346Labels = mixedMoment B raw9346step0 raw9346step0Labels := by
      have hz : ∀ j, raw9346 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9346step0 = (fun i j => raw9346 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9346step0 raw9346; decide +kernel
      have hl : raw9346step0Labels = raw9346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9346 raw9346Labels permutation265 hz
    mixedMoment B raw9346step0 raw9346step0Labels = mixedMoment B raw9346step1 raw9346step1Labels := by
      have ha : raw9346step1 = (fun i j => raw9346step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9346step1 raw9346step0; decide +kernel
      have hl : raw9346step1Labels = raw9346step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9346step0 raw9346step0Labels permutation33 permutation2
    _ = mixedMoment B node1253 node1253Labels := by rfl

theorem canonical9347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9347 raw9347Labels = mixedMoment B node1252 node1252Labels := by
  calc
    mixedMoment B raw9347 raw9347Labels = mixedMoment B raw9347step0 raw9347step0Labels := by
      have hz : ∀ j, raw9347 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9347step0 = (fun i j => raw9347 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9347step0 raw9347; decide +kernel
      have hl : raw9347step0Labels = raw9347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9347 raw9347Labels permutation265 hz
    _ = mixedMoment B node1252 node1252Labels := by rfl

theorem canonical9348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9348 raw9348Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw9348 raw9348Labels = mixedMoment B raw9348step0 raw9348step0Labels := by
      have hz : ∀ j, raw9348 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9348step0 = (fun i j => raw9348 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9348step0 raw9348; decide +kernel
      have hl : raw9348step0Labels = raw9348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9348 raw9348Labels permutation265 hz
    mixedMoment B raw9348step0 raw9348step0Labels = mixedMoment B raw9348step1 raw9348step1Labels := by
      have ha : raw9348step1 = (fun i j => raw9348step0 (permutation50 i) (permutation0 j)) := by apply Matrix.ext; unfold raw9348step1 raw9348step0; decide +kernel
      have hl : raw9348step1Labels = raw9348step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9348step0 raw9348step0Labels permutation50 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical9349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9349 raw9349Labels = mixedMoment B node2625 node2625Labels := by
  calc
    mixedMoment B raw9349 raw9349Labels = mixedMoment B raw9349step0 raw9349step0Labels := by
      have ha : raw9349step0 = (fun i j => raw9349 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9349step0 raw9349; decide +kernel
      have hl : raw9349step0Labels = raw9349Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9349 raw9349Labels permutation182 permutation2
    _ = mixedMoment B node2625 node2625Labels := by rfl

theorem canonical9350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9350 raw9350Labels = mixedMoment B node2625 node2625Labels := by
  calc
    mixedMoment B raw9350 raw9350Labels = mixedMoment B raw9350step0 raw9350step0Labels := by
      have ha : raw9350step0 = (fun i j => raw9350 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9350step0 raw9350; decide +kernel
      have hl : raw9350step0Labels = raw9350Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9350 raw9350Labels permutation206 permutation2
    _ = mixedMoment B node2625 node2625Labels := by rfl

theorem canonical9351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9351 raw9351Labels = mixedMoment B node2746 node2746Labels := by
  calc
    mixedMoment B raw9351 raw9351Labels = mixedMoment B raw9351step0 raw9351step0Labels := by
      have ha : raw9351step0 = (fun i j => raw9351 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9351step0 raw9351; decide +kernel
      have hl : raw9351step0Labels = raw9351Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9351 raw9351Labels permutation184 permutation2
    _ = mixedMoment B node2746 node2746Labels := by rfl

theorem canonical9352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9352 raw9352Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw9352 raw9352Labels = mixedMoment B raw9352step0 raw9352step0Labels := by
      have ha : raw9352step0 = (fun i j => raw9352 (permutation186 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9352step0 raw9352; decide +kernel
      have hl : raw9352step0Labels = raw9352Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9352 raw9352Labels permutation186 permutation2
    _ = mixedMoment B node2750 node2750Labels := by rfl

theorem canonical9353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9353 raw9353Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw9353 raw9353Labels = mixedMoment B raw9353step0 raw9353step0Labels := by
      have ha : raw9353step0 = (fun i j => raw9353 (permutation599 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9353step0 raw9353; decide +kernel
      have hl : raw9353step0Labels = raw9353Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9353 raw9353Labels permutation599 permutation4
    _ = mixedMoment B node3037 node3037Labels := by rfl

theorem canonical9354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9354 raw9354Labels = mixedMoment B node2573 node2573Labels := by
  calc
    mixedMoment B raw9354 raw9354Labels = mixedMoment B raw9354step0 raw9354step0Labels := by
      have ha : raw9354step0 = (fun i j => raw9354 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9354step0 raw9354; decide +kernel
      have hl : raw9354step0Labels = raw9354Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9354 raw9354Labels permutation158 permutation2
    _ = mixedMoment B node2573 node2573Labels := by rfl

theorem canonical9355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9355 raw9355Labels = mixedMoment B node2573 node2573Labels := by
  calc
    _ = mixedMoment B node2573 node2573Labels := by rfl

theorem canonical9356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9356 raw9356Labels = mixedMoment B node2564 node2564Labels := by
  calc
    mixedMoment B raw9356 raw9356Labels = mixedMoment B raw9356step0 raw9356step0Labels := by
      have ha : raw9356step0 = (fun i j => raw9356 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9356step0 raw9356; decide +kernel
      have hl : raw9356step0Labels = raw9356Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9356 raw9356Labels permutation153 permutation2
    _ = mixedMoment B node2564 node2564Labels := by rfl

theorem canonical9357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9357 raw9357Labels = mixedMoment B node1421 node1421Labels := by
  calc
    mixedMoment B raw9357 raw9357Labels = mixedMoment B raw9357step0 raw9357step0Labels := by
      have ha : raw9357step0 = (fun i j => raw9357 (permutation665 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9357step0 raw9357; decide +kernel
      have hl : raw9357step0Labels = raw9357Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9357 raw9357Labels permutation665 permutation4
    _ = mixedMoment B node1421 node1421Labels := by rfl

theorem canonical9358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9358 raw9358Labels = mixedMoment B node2641 node2641Labels := by
  calc
    mixedMoment B raw9358 raw9358Labels = mixedMoment B raw9358step0 raw9358step0Labels := by
      have hz : ∀ j, raw9358 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9358step0 = (fun i j => raw9358 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9358step0 raw9358; decide +kernel
      have hl : raw9358step0Labels = raw9358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9358 raw9358Labels permutation265 hz
    mixedMoment B raw9358step0 raw9358step0Labels = mixedMoment B raw9358step1 raw9358step1Labels := by
      have ha : raw9358step1 = (fun i j => raw9358step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9358step1 raw9358step0; decide +kernel
      have hl : raw9358step1Labels = raw9358step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9358step0 raw9358step0Labels permutation38 permutation2
    _ = mixedMoment B node2641 node2641Labels := by rfl

theorem canonical9359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9359 raw9359Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw9359 raw9359Labels = mixedMoment B raw9359step0 raw9359step0Labels := by
      have hz : ∀ j, raw9359 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9359step0 = (fun i j => raw9359 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9359step0 raw9359; decide +kernel
      have hl : raw9359step0Labels = raw9359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9359 raw9359Labels permutation265 hz
    mixedMoment B raw9359step0 raw9359step0Labels = mixedMoment B raw9359step1 raw9359step1Labels := by
      have ha : raw9359step1 = (fun i j => raw9359step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9359step1 raw9359step0; decide +kernel
      have hl : raw9359step1Labels = raw9359step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9359step0 raw9359step0Labels permutation40 permutation2
    _ = mixedMoment B node2754 node2754Labels := by rfl

theorem canonical9360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9360 raw9360Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw9360 raw9360Labels = mixedMoment B raw9360step0 raw9360step0Labels := by
      have hz : ∀ j, raw9360 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9360step0 = (fun i j => raw9360 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9360step0 raw9360; decide +kernel
      have hl : raw9360step0Labels = raw9360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9360 raw9360Labels permutation265 hz
    mixedMoment B raw9360step0 raw9360step0Labels = mixedMoment B raw9360step1 raw9360step1Labels := by
      have ha : raw9360step1 = (fun i j => raw9360step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9360step1 raw9360step0; decide +kernel
      have hl : raw9360step1Labels = raw9360step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9360step0 raw9360step0Labels permutation42 permutation2
    _ = mixedMoment B node2764 node2764Labels := by rfl

theorem canonical9361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9361 raw9361Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw9361 raw9361Labels = mixedMoment B raw9361step0 raw9361step0Labels := by
      have ha : raw9361step0 = (fun i j => raw9361 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9361step0 raw9361; decide +kernel
      have hl : raw9361step0Labels = raw9361Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9361 raw9361Labels permutation674 permutation7
    mixedMoment B raw9361step0 raw9361step0Labels = mixedMoment B raw9361step1 raw9361step1Labels := by
      have ha : raw9361step1 = raw9361step0 := by apply Matrix.ext; unfold raw9361step1 raw9361step0; decide +kernel
      have hl : raw9361step0Labels = labelEmbedding10 ∘ raw9361step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9361step0 raw9361step0Labels raw9361step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5256 node5256Labels := by rfl

theorem canonical9362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9362 raw9362Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw9362 raw9362Labels = mixedMoment B raw9362step0 raw9362step0Labels := by
      have hz : ∀ j, raw9362 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9362step0 = (fun i j => raw9362 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9362step0 raw9362; decide +kernel
      have hl : raw9362step0Labels = raw9362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9362 raw9362Labels permutation265 hz
    mixedMoment B raw9362step0 raw9362step0Labels = mixedMoment B raw9362step1 raw9362step1Labels := by
      have ha : raw9362step1 = (fun i j => raw9362step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9362step1 raw9362step0; decide +kernel
      have hl : raw9362step1Labels = raw9362step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9362step0 raw9362step0Labels permutation151 permutation7
    mixedMoment B raw9362step1 raw9362step1Labels = mixedMoment B raw9362step2 raw9362step2Labels := by
      have ha : raw9362step2 = raw9362step1 := by apply Matrix.ext; unfold raw9362step2 raw9362step1; decide +kernel
      have hl : raw9362step1Labels = labelEmbedding10 ∘ raw9362step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9362step1 raw9362step1Labels raw9362step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical9363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9363 raw9363Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw9363 raw9363Labels = mixedMoment B raw9363step0 raw9363step0Labels := by
      have hz : ∀ j, raw9363 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9363step0 = (fun i j => raw9363 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9363step0 raw9363; decide +kernel
      have hl : raw9363step0Labels = raw9363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9363 raw9363Labels permutation265 hz
    mixedMoment B raw9363step0 raw9363step0Labels = mixedMoment B raw9363step1 raw9363step1Labels := by
      have ha : raw9363step1 = (fun i j => raw9363step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9363step1 raw9363step0; decide +kernel
      have hl : raw9363step1Labels = raw9363step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9363step0 raw9363step0Labels permutation149 permutation7
    mixedMoment B raw9363step1 raw9363step1Labels = mixedMoment B raw9363step2 raw9363step2Labels := by
      have ha : raw9363step2 = raw9363step1 := by apply Matrix.ext; unfold raw9363step2 raw9363step1; decide +kernel
      have hl : raw9363step1Labels = labelEmbedding10 ∘ raw9363step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9363step1 raw9363step1Labels raw9363step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical9364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9364 raw9364Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw9364 raw9364Labels = mixedMoment B raw9364step0 raw9364step0Labels := by
      have hz : ∀ j, raw9364 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9364step0 = (fun i j => raw9364 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9364step0 raw9364; decide +kernel
      have hl : raw9364step0Labels = raw9364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9364 raw9364Labels permutation520 hz
    mixedMoment B raw9364step0 raw9364step0Labels = mixedMoment B raw9364step1 raw9364step1Labels := by
      have hz : ∀ j, raw9364step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9364step1 = (fun i j => raw9364step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9364step1 raw9364step0; decide +kernel
      have hl : raw9364step1Labels = raw9364step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9364step0 raw9364step0Labels permutation56 hz
    mixedMoment B raw9364step1 raw9364step1Labels = mixedMoment B raw9364step2 raw9364step2Labels := by
      have ha : raw9364step2 = (fun i j => raw9364step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9364step2 raw9364step1; decide +kernel
      have hl : raw9364step2Labels = raw9364step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9364step1 raw9364step1Labels permutation29 permutation7
    mixedMoment B raw9364step2 raw9364step2Labels = mixedMoment B raw9364step3 raw9364step3Labels := by
      have ha : raw9364step3 = raw9364step2 := by apply Matrix.ext; unfold raw9364step3 raw9364step2; decide +kernel
      have hl : raw9364step2Labels = labelEmbedding10 ∘ raw9364step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9364step2 raw9364step2Labels raw9364step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

theorem canonical9365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9365 raw9365Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw9365 raw9365Labels = mixedMoment B raw9365step0 raw9365step0Labels := by
      have hz : ∀ j, raw9365 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9365step0 = (fun i j => raw9365 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9365step0 raw9365; decide +kernel
      have hl : raw9365step0Labels = raw9365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9365 raw9365Labels permutation265 hz
    mixedMoment B raw9365step0 raw9365step0Labels = mixedMoment B raw9365step1 raw9365step1Labels := by
      have ha : raw9365step1 = (fun i j => raw9365step0 (permutation146 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9365step1 raw9365step0; decide +kernel
      have hl : raw9365step1Labels = raw9365step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9365step0 raw9365step0Labels permutation146 permutation6
    mixedMoment B raw9365step1 raw9365step1Labels = mixedMoment B raw9365step2 raw9365step2Labels := by
      have ha : raw9365step2 = raw9365step1 := by apply Matrix.ext; unfold raw9365step2 raw9365step1; decide +kernel
      have hl : raw9365step1Labels = labelEmbedding9 ∘ raw9365step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9365step1 raw9365step1Labels raw9365step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical9366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9366 raw9366Labels = mixedMoment B node4441 node4441Labels := by
  calc
    mixedMoment B raw9366 raw9366Labels = mixedMoment B raw9366step0 raw9366step0Labels := by
      have ha : raw9366step0 = (fun i j => raw9366 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9366step0 raw9366; decide +kernel
      have hl : raw9366step0Labels = raw9366Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9366 raw9366Labels permutation182 permutation3
    mixedMoment B raw9366step0 raw9366step0Labels = mixedMoment B raw9366step1 raw9366step1Labels := by
      have ha : raw9366step1 = raw9366step0 := by apply Matrix.ext; unfold raw9366step1 raw9366step0; decide +kernel
      have hl : raw9366step0Labels = labelEmbedding6 ∘ raw9366step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9366step0 raw9366step0Labels raw9366step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4441 node4441Labels := by rfl

theorem canonical9367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9367 raw9367Labels = mixedMoment B node5150 node5150Labels := by
  calc
    mixedMoment B raw9367 raw9367Labels = mixedMoment B raw9367step0 raw9367step0Labels := by
      have ha : raw9367step0 = (fun i j => raw9367 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9367step0 raw9367; decide +kernel
      have hl : raw9367step0Labels = raw9367Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9367 raw9367Labels permutation182 permutation3
    mixedMoment B raw9367step0 raw9367step0Labels = mixedMoment B raw9367step1 raw9367step1Labels := by
      have ha : raw9367step1 = raw9367step0 := by apply Matrix.ext; unfold raw9367step1 raw9367step0; decide +kernel
      have hl : raw9367step0Labels = labelEmbedding6 ∘ raw9367step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9367step0 raw9367step0Labels raw9367step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5150 node5150Labels := by rfl

theorem canonical9368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9368 raw9368Labels = mixedMoment B node5150 node5150Labels := by
  calc
    mixedMoment B raw9368 raw9368Labels = mixedMoment B raw9368step0 raw9368step0Labels := by
      have ha : raw9368step0 = (fun i j => raw9368 (permutation206 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9368step0 raw9368; decide +kernel
      have hl : raw9368step0Labels = raw9368Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9368 raw9368Labels permutation206 permutation3
    mixedMoment B raw9368step0 raw9368step0Labels = mixedMoment B raw9368step1 raw9368step1Labels := by
      have ha : raw9368step1 = raw9368step0 := by apply Matrix.ext; unfold raw9368step1 raw9368step0; decide +kernel
      have hl : raw9368step0Labels = labelEmbedding6 ∘ raw9368step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9368step0 raw9368step0Labels raw9368step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5150 node5150Labels := by rfl

theorem canonical9369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9369 raw9369Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw9369 raw9369Labels = mixedMoment B raw9369step0 raw9369step0Labels := by
      have hz : ∀ j, raw9369 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9369step0 = (fun i j => raw9369 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9369step0 raw9369; decide +kernel
      have hl : raw9369step0Labels = raw9369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9369 raw9369Labels permutation520 hz
    mixedMoment B raw9369step0 raw9369step0Labels = mixedMoment B raw9369step1 raw9369step1Labels := by
      have ha : raw9369step1 = (fun i j => raw9369step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9369step1 raw9369step0; decide +kernel
      have hl : raw9369step1Labels = raw9369step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9369step0 raw9369step0Labels permutation137 permutation7
    mixedMoment B raw9369step1 raw9369step1Labels = mixedMoment B raw9369step2 raw9369step2Labels := by
      have ha : raw9369step2 = raw9369step1 := by apply Matrix.ext; unfold raw9369step2 raw9369step1; decide +kernel
      have hl : raw9369step1Labels = labelEmbedding10 ∘ raw9369step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9369step1 raw9369step1Labels raw9369step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

theorem canonical9370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9370 raw9370Labels = mixedMoment B node5278 node5278Labels := by
  calc
    mixedMoment B raw9370 raw9370Labels = mixedMoment B raw9370step0 raw9370step0Labels := by
      have ha : raw9370step0 = (fun i j => raw9370 (permutation186 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9370step0 raw9370; decide +kernel
      have hl : raw9370step0Labels = raw9370Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9370 raw9370Labels permutation186 permutation3
    mixedMoment B raw9370step0 raw9370step0Labels = mixedMoment B raw9370step1 raw9370step1Labels := by
      have ha : raw9370step1 = raw9370step0 := by apply Matrix.ext; unfold raw9370step1 raw9370step0; decide +kernel
      have hl : raw9370step0Labels = labelEmbedding6 ∘ raw9370step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9370step0 raw9370step0Labels raw9370step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5278 node5278Labels := by rfl

theorem canonical9371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9371 raw9371Labels = mixedMoment B node4462 node4462Labels := by
  calc
    mixedMoment B raw9371 raw9371Labels = mixedMoment B raw9371step0 raw9371step0Labels := by
      have hz : ∀ j, raw9371 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9371step0 = (fun i j => raw9371 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9371step0 raw9371; decide +kernel
      have hl : raw9371step0Labels = raw9371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9371 raw9371Labels permutation265 hz
    mixedMoment B raw9371step0 raw9371step0Labels = mixedMoment B raw9371step1 raw9371step1Labels := by
      have ha : raw9371step1 = (fun i j => raw9371step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9371step1 raw9371step0; decide +kernel
      have hl : raw9371step1Labels = raw9371step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9371step0 raw9371step0Labels permutation40 permutation3
    mixedMoment B raw9371step1 raw9371step1Labels = mixedMoment B raw9371step2 raw9371step2Labels := by
      have ha : raw9371step2 = raw9371step1 := by apply Matrix.ext; unfold raw9371step2 raw9371step1; decide +kernel
      have hl : raw9371step1Labels = labelEmbedding6 ∘ raw9371step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9371step1 raw9371step1Labels raw9371step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4462 node4462Labels := by rfl

theorem canonical9372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9372 raw9372Labels = mixedMoment B node5077 node5077Labels := by
  calc
    mixedMoment B raw9372 raw9372Labels = mixedMoment B raw9372step0 raw9372step0Labels := by
      have ha : raw9372step0 = (fun i j => raw9372 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9372step0 raw9372; decide +kernel
      have hl : raw9372step0Labels = raw9372Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9372 raw9372Labels permutation160 permutation3
    mixedMoment B raw9372step0 raw9372step0Labels = mixedMoment B raw9372step1 raw9372step1Labels := by
      have ha : raw9372step1 = raw9372step0 := by apply Matrix.ext; unfold raw9372step1 raw9372step0; decide +kernel
      have hl : raw9372step0Labels = labelEmbedding6 ∘ raw9372step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9372step0 raw9372step0Labels raw9372step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5077 node5077Labels := by rfl

theorem canonical9373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9373 raw9373Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw9373 raw9373Labels = mixedMoment B raw9373step0 raw9373step0Labels := by
      have hz : ∀ j, raw9373 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9373step0 = (fun i j => raw9373 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9373step0 raw9373; decide +kernel
      have hl : raw9373step0Labels = raw9373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9373 raw9373Labels permutation265 hz
    mixedMoment B raw9373step0 raw9373step0Labels = mixedMoment B raw9373step1 raw9373step1Labels := by
      have ha : raw9373step1 = (fun i j => raw9373step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9373step1 raw9373step0; decide +kernel
      have hl : raw9373step1Labels = raw9373step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9373step0 raw9373step0Labels permutation40 permutation3
    mixedMoment B raw9373step1 raw9373step1Labels = mixedMoment B raw9373step2 raw9373step2Labels := by
      have ha : raw9373step2 = raw9373step1 := by apply Matrix.ext; unfold raw9373step2 raw9373step1; decide +kernel
      have hl : raw9373step1Labels = labelEmbedding6 ∘ raw9373step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9373step1 raw9373step1Labels raw9373step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

theorem canonical9374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9374 raw9374Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw9374 raw9374Labels = mixedMoment B raw9374step0 raw9374step0Labels := by
      have hz : ∀ j, raw9374 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9374step0 = (fun i j => raw9374 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9374step0 raw9374; decide +kernel
      have hl : raw9374step0Labels = raw9374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9374 raw9374Labels permutation520 hz
    mixedMoment B raw9374step0 raw9374step0Labels = mixedMoment B raw9374step1 raw9374step1Labels := by
      have hz : ∀ j, raw9374step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9374step1 = (fun i j => raw9374step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9374step1 raw9374step0; decide +kernel
      have hl : raw9374step1Labels = raw9374step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9374step0 raw9374step0Labels permutation56 hz
    mixedMoment B raw9374step1 raw9374step1Labels = mixedMoment B raw9374step2 raw9374step2Labels := by
      have ha : raw9374step2 = (fun i j => raw9374step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9374step2 raw9374step1; decide +kernel
      have hl : raw9374step2Labels = raw9374step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9374step1 raw9374step1Labels permutation10 permutation3
    mixedMoment B raw9374step2 raw9374step2Labels = mixedMoment B raw9374step3 raw9374step3Labels := by
      have ha : raw9374step3 = raw9374step2 := by apply Matrix.ext; unfold raw9374step3 raw9374step2; decide +kernel
      have hl : raw9374step2Labels = labelEmbedding6 ∘ raw9374step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9374step2 raw9374step2Labels raw9374step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

theorem canonical9375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9375 raw9375Labels = mixedMoment B node5288 node5288Labels := by
  calc
    mixedMoment B raw9375 raw9375Labels = mixedMoment B raw9375step0 raw9375step0Labels := by
      have hz : ∀ j, raw9375 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9375step0 = (fun i j => raw9375 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9375step0 raw9375; decide +kernel
      have hl : raw9375step0Labels = raw9375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9375 raw9375Labels permutation265 hz
    mixedMoment B raw9375step0 raw9375step0Labels = mixedMoment B raw9375step1 raw9375step1Labels := by
      have ha : raw9375step1 = (fun i j => raw9375step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9375step1 raw9375step0; decide +kernel
      have hl : raw9375step1Labels = raw9375step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9375step0 raw9375step0Labels permutation43 permutation3
    mixedMoment B raw9375step1 raw9375step1Labels = mixedMoment B raw9375step2 raw9375step2Labels := by
      have ha : raw9375step2 = raw9375step1 := by apply Matrix.ext; unfold raw9375step2 raw9375step1; decide +kernel
      have hl : raw9375step1Labels = labelEmbedding6 ∘ raw9375step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9375step1 raw9375step1Labels raw9375step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5288 node5288Labels := by rfl

theorem canonical9376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9376 raw9376Labels = mixedMoment B node4462 node4462Labels := by
  calc
    mixedMoment B raw9376 raw9376Labels = mixedMoment B raw9376step0 raw9376step0Labels := by
      have hz : ∀ j, raw9376 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9376step0 = (fun i j => raw9376 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9376step0 raw9376; decide +kernel
      have hl : raw9376step0Labels = raw9376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9376 raw9376Labels permutation265 hz
    mixedMoment B raw9376step0 raw9376step0Labels = mixedMoment B raw9376step1 raw9376step1Labels := by
      have ha : raw9376step1 = (fun i j => raw9376step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9376step1 raw9376step0; decide +kernel
      have hl : raw9376step1Labels = raw9376step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9376step0 raw9376step0Labels permutation34 permutation3
    mixedMoment B raw9376step1 raw9376step1Labels = mixedMoment B raw9376step2 raw9376step2Labels := by
      have ha : raw9376step2 = raw9376step1 := by apply Matrix.ext; unfold raw9376step2 raw9376step1; decide +kernel
      have hl : raw9376step1Labels = labelEmbedding6 ∘ raw9376step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9376step1 raw9376step1Labels raw9376step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4462 node4462Labels := by rfl

theorem canonical9377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9377 raw9377Labels = mixedMoment B node5077 node5077Labels := by
  calc
    mixedMoment B raw9377 raw9377Labels = mixedMoment B raw9377step0 raw9377step0Labels := by
      have ha : raw9377step0 = (fun i j => raw9377 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9377step0 raw9377; decide +kernel
      have hl : raw9377step0Labels = raw9377Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9377 raw9377Labels permutation154 permutation3
    mixedMoment B raw9377step0 raw9377step0Labels = mixedMoment B raw9377step1 raw9377step1Labels := by
      have ha : raw9377step1 = raw9377step0 := by apply Matrix.ext; unfold raw9377step1 raw9377step0; decide +kernel
      have hl : raw9377step0Labels = labelEmbedding6 ∘ raw9377step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9377step0 raw9377step0Labels raw9377step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5077 node5077Labels := by rfl

theorem canonical9378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9378 raw9378Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw9378 raw9378Labels = mixedMoment B raw9378step0 raw9378step0Labels := by
      have hz : ∀ j, raw9378 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9378step0 = (fun i j => raw9378 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9378step0 raw9378; decide +kernel
      have hl : raw9378step0Labels = raw9378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9378 raw9378Labels permutation265 hz
    mixedMoment B raw9378step0 raw9378step0Labels = mixedMoment B raw9378step1 raw9378step1Labels := by
      have ha : raw9378step1 = (fun i j => raw9378step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9378step1 raw9378step0; decide +kernel
      have hl : raw9378step1Labels = raw9378step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9378step0 raw9378step0Labels permutation34 permutation3
    mixedMoment B raw9378step1 raw9378step1Labels = mixedMoment B raw9378step2 raw9378step2Labels := by
      have ha : raw9378step2 = raw9378step1 := by apply Matrix.ext; unfold raw9378step2 raw9378step1; decide +kernel
      have hl : raw9378step1Labels = labelEmbedding6 ∘ raw9378step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9378step1 raw9378step1Labels raw9378step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

theorem canonical9379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9379 raw9379Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw9379 raw9379Labels = mixedMoment B raw9379step0 raw9379step0Labels := by
      have hz : ∀ j, raw9379 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9379step0 = (fun i j => raw9379 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9379step0 raw9379; decide +kernel
      have hl : raw9379step0Labels = raw9379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9379 raw9379Labels permutation520 hz
    mixedMoment B raw9379step0 raw9379step0Labels = mixedMoment B raw9379step1 raw9379step1Labels := by
      have hz : ∀ j, raw9379step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9379step1 = (fun i j => raw9379step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9379step1 raw9379step0; decide +kernel
      have hl : raw9379step1Labels = raw9379step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9379step0 raw9379step0Labels permutation56 hz
    mixedMoment B raw9379step1 raw9379step1Labels = mixedMoment B raw9379step2 raw9379step2Labels := by
      have ha : raw9379step2 = (fun i j => raw9379step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9379step2 raw9379step1; decide +kernel
      have hl : raw9379step2Labels = raw9379step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9379step1 raw9379step1Labels permutation8 permutation3
    mixedMoment B raw9379step2 raw9379step2Labels = mixedMoment B raw9379step3 raw9379step3Labels := by
      have ha : raw9379step3 = raw9379step2 := by apply Matrix.ext; unfold raw9379step3 raw9379step2; decide +kernel
      have hl : raw9379step2Labels = labelEmbedding6 ∘ raw9379step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9379step2 raw9379step2Labels raw9379step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

theorem canonical9380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9380 raw9380Labels = mixedMoment B node5288 node5288Labels := by
  calc
    mixedMoment B raw9380 raw9380Labels = mixedMoment B raw9380step0 raw9380step0Labels := by
      have hz : ∀ j, raw9380 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9380step0 = (fun i j => raw9380 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9380step0 raw9380; decide +kernel
      have hl : raw9380step0Labels = raw9380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9380 raw9380Labels permutation265 hz
    mixedMoment B raw9380step0 raw9380step0Labels = mixedMoment B raw9380step1 raw9380step1Labels := by
      have ha : raw9380step1 = (fun i j => raw9380step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9380step1 raw9380step0; decide +kernel
      have hl : raw9380step1Labels = raw9380step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9380step0 raw9380step0Labels permutation37 permutation3
    mixedMoment B raw9380step1 raw9380step1Labels = mixedMoment B raw9380step2 raw9380step2Labels := by
      have ha : raw9380step2 = raw9380step1 := by apply Matrix.ext; unfold raw9380step2 raw9380step1; decide +kernel
      have hl : raw9380step1Labels = labelEmbedding6 ∘ raw9380step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9380step1 raw9380step1Labels raw9380step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5288 node5288Labels := by rfl

theorem canonical9381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9381 raw9381Labels = mixedMoment B node4443 node4443Labels := by
  calc
    mixedMoment B raw9381 raw9381Labels = mixedMoment B raw9381step0 raw9381step0Labels := by
      have hz : ∀ j, raw9381 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9381step0 = (fun i j => raw9381 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9381step0 raw9381; decide +kernel
      have hl : raw9381step0Labels = raw9381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9381 raw9381Labels permutation265 hz
    mixedMoment B raw9381step0 raw9381step0Labels = mixedMoment B raw9381step1 raw9381step1Labels := by
      have ha : raw9381step1 = (fun i j => raw9381step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9381step1 raw9381step0; decide +kernel
      have hl : raw9381step1Labels = raw9381step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9381step0 raw9381step0Labels permutation33 permutation3
    mixedMoment B raw9381step1 raw9381step1Labels = mixedMoment B raw9381step2 raw9381step2Labels := by
      have ha : raw9381step2 = raw9381step1 := by apply Matrix.ext; unfold raw9381step2 raw9381step1; decide +kernel
      have hl : raw9381step1Labels = labelEmbedding6 ∘ raw9381step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9381step1 raw9381step1Labels raw9381step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4443 node4443Labels := by rfl

theorem canonical9382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9382 raw9382Labels = mixedMoment B node5066 node5066Labels := by
  calc
    mixedMoment B raw9382 raw9382Labels = mixedMoment B raw9382step0 raw9382step0Labels := by
      have ha : raw9382step0 = (fun i j => raw9382 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9382step0 raw9382; decide +kernel
      have hl : raw9382step0Labels = raw9382Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9382 raw9382Labels permutation153 permutation3
    mixedMoment B raw9382step0 raw9382step0Labels = mixedMoment B raw9382step1 raw9382step1Labels := by
      have ha : raw9382step1 = raw9382step0 := by apply Matrix.ext; unfold raw9382step1 raw9382step0; decide +kernel
      have hl : raw9382step0Labels = labelEmbedding6 ∘ raw9382step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9382step0 raw9382step0Labels raw9382step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5066 node5066Labels := by rfl

theorem canonical9383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9383 raw9383Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw9383 raw9383Labels = mixedMoment B raw9383step0 raw9383step0Labels := by
      have hz : ∀ j, raw9383 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9383step0 = (fun i j => raw9383 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9383step0 raw9383; decide +kernel
      have hl : raw9383step0Labels = raw9383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9383 raw9383Labels permutation265 hz
    mixedMoment B raw9383step0 raw9383step0Labels = mixedMoment B raw9383step1 raw9383step1Labels := by
      have ha : raw9383step1 = (fun i j => raw9383step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9383step1 raw9383step0; decide +kernel
      have hl : raw9383step1Labels = raw9383step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9383step0 raw9383step0Labels permutation33 permutation3
    mixedMoment B raw9383step1 raw9383step1Labels = mixedMoment B raw9383step2 raw9383step2Labels := by
      have ha : raw9383step2 = raw9383step1 := by apply Matrix.ext; unfold raw9383step2 raw9383step1; decide +kernel
      have hl : raw9383step1Labels = labelEmbedding6 ∘ raw9383step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9383step1 raw9383step1Labels raw9383step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5151 node5151Labels := by rfl

theorem canonical9384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9384 raw9384Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw9384 raw9384Labels = mixedMoment B raw9384step0 raw9384step0Labels := by
      have hz : ∀ j, raw9384 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9384step0 = (fun i j => raw9384 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9384step0 raw9384; decide +kernel
      have hl : raw9384step0Labels = raw9384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9384 raw9384Labels permutation265 hz
    mixedMoment B raw9384step0 raw9384step0Labels = mixedMoment B raw9384step1 raw9384step1Labels := by
      have ha : raw9384step1 = (fun i j => raw9384step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9384step1 raw9384step0; decide +kernel
      have hl : raw9384step1Labels = raw9384step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9384step0 raw9384step0Labels permutation39 permutation3
    mixedMoment B raw9384step1 raw9384step1Labels = mixedMoment B raw9384step2 raw9384step2Labels := by
      have ha : raw9384step2 = raw9384step1 := by apply Matrix.ext; unfold raw9384step2 raw9384step1; decide +kernel
      have hl : raw9384step1Labels = labelEmbedding6 ∘ raw9384step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9384step1 raw9384step1Labels raw9384step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5151 node5151Labels := by rfl

theorem canonical9385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9385 raw9385Labels = mixedMoment B node5279 node5279Labels := by
  calc
    mixedMoment B raw9385 raw9385Labels = mixedMoment B raw9385step0 raw9385step0Labels := by
      have hz : ∀ j, raw9385 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9385step0 = (fun i j => raw9385 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9385step0 raw9385; decide +kernel
      have hl : raw9385step0Labels = raw9385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9385 raw9385Labels permutation265 hz
    mixedMoment B raw9385step0 raw9385step0Labels = mixedMoment B raw9385step1 raw9385step1Labels := by
      have ha : raw9385step1 = (fun i j => raw9385step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9385step1 raw9385step0; decide +kernel
      have hl : raw9385step1Labels = raw9385step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9385step0 raw9385step0Labels permutation33 permutation3
    mixedMoment B raw9385step1 raw9385step1Labels = mixedMoment B raw9385step2 raw9385step2Labels := by
      have ha : raw9385step2 = raw9385step1 := by apply Matrix.ext; unfold raw9385step2 raw9385step1; decide +kernel
      have hl : raw9385step1Labels = labelEmbedding6 ∘ raw9385step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9385step1 raw9385step1Labels raw9385step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5279 node5279Labels := by rfl

theorem canonical9386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9386 raw9386Labels = mixedMoment B node4442 node4442Labels := by
  calc
    mixedMoment B raw9386 raw9386Labels = mixedMoment B raw9386step0 raw9386step0Labels := by
      have hz : ∀ j, raw9386 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9386step0 = (fun i j => raw9386 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9386step0 raw9386; decide +kernel
      have hl : raw9386step0Labels = raw9386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9386 raw9386Labels permutation265 hz
    mixedMoment B raw9386step0 raw9386step0Labels = mixedMoment B raw9386step1 raw9386step1Labels := by
      have ha : raw9386step1 = (fun i j => raw9386step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9386step1 raw9386step0; decide +kernel
      have hl : raw9386step1Labels = raw9386step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9386step0 raw9386step0Labels permutation32 permutation3
    mixedMoment B raw9386step1 raw9386step1Labels = mixedMoment B raw9386step2 raw9386step2Labels := by
      have ha : raw9386step2 = raw9386step1 := by apply Matrix.ext; unfold raw9386step2 raw9386step1; decide +kernel
      have hl : raw9386step1Labels = labelEmbedding6 ∘ raw9386step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9386step1 raw9386step1Labels raw9386step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4442 node4442Labels := by rfl

theorem canonical9387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9387 raw9387Labels = mixedMoment B node4792 node4792Labels := by
  calc
    mixedMoment B raw9387 raw9387Labels = mixedMoment B raw9387step0 raw9387step0Labels := by
      have ha : raw9387step0 = (fun i j => raw9387 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9387step0 raw9387; decide +kernel
      have hl : raw9387step0Labels = raw9387Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9387 raw9387Labels permutation682 permutation2
    mixedMoment B raw9387step0 raw9387step0Labels = mixedMoment B raw9387step1 raw9387step1Labels := by
      have ha : raw9387step1 = -raw9387step0 := by apply Matrix.ext; change ∀ i j, raw9387step1 i j = -(raw9387step0 i j); unfold raw9387step1 raw9387step0; decide +kernel
      have hl : raw9387step1Labels = raw9387step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4792 node4792Labels := by rfl

theorem canonical9388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9388 raw9388Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw9388 raw9388Labels = mixedMoment B raw9388step0 raw9388step0Labels := by
      have hz : ∀ j, raw9388 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9388step0 = (fun i j => raw9388 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9388step0 raw9388; decide +kernel
      have hl : raw9388step0Labels = raw9388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9388 raw9388Labels permutation265 hz
    mixedMoment B raw9388step0 raw9388step0Labels = mixedMoment B raw9388step1 raw9388step1Labels := by
      have ha : raw9388step1 = (fun i j => raw9388step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9388step1 raw9388step0; decide +kernel
      have hl : raw9388step1Labels = raw9388step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9388step0 raw9388step0Labels permutation151 permutation2
    mixedMoment B raw9388step1 raw9388step1Labels = mixedMoment B raw9388step2 raw9388step2Labels := by
      have ha : raw9388step2 = -raw9388step1 := by apply Matrix.ext; change ∀ i j, raw9388step2 i j = -(raw9388step1 i j); unfold raw9388step2 raw9388step1; decide +kernel
      have hl : raw9388step2Labels = raw9388step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical9389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9389 raw9389Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw9389 raw9389Labels = mixedMoment B raw9389step0 raw9389step0Labels := by
      have hz : ∀ j, raw9389 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9389step0 = (fun i j => raw9389 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9389step0 raw9389; decide +kernel
      have hl : raw9389step0Labels = raw9389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9389 raw9389Labels permutation265 hz
    mixedMoment B raw9389step0 raw9389step0Labels = mixedMoment B raw9389step1 raw9389step1Labels := by
      have ha : raw9389step1 = (fun i j => raw9389step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9389step1 raw9389step0; decide +kernel
      have hl : raw9389step1Labels = raw9389step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9389step0 raw9389step0Labels permutation149 permutation2
    mixedMoment B raw9389step1 raw9389step1Labels = mixedMoment B raw9389step2 raw9389step2Labels := by
      have ha : raw9389step2 = -raw9389step1 := by apply Matrix.ext; change ∀ i j, raw9389step2 i j = -(raw9389step1 i j); unfold raw9389step2 raw9389step1; decide +kernel
      have hl : raw9389step2Labels = raw9389step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical9390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9390 raw9390Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw9390 raw9390Labels = mixedMoment B raw9390step0 raw9390step0Labels := by
      have hz : ∀ j, raw9390 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9390step0 = (fun i j => raw9390 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9390step0 raw9390; decide +kernel
      have hl : raw9390step0Labels = raw9390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9390 raw9390Labels permutation520 hz
    mixedMoment B raw9390step0 raw9390step0Labels = mixedMoment B raw9390step1 raw9390step1Labels := by
      have hz : ∀ j, raw9390step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9390step1 = (fun i j => raw9390step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9390step1 raw9390step0; decide +kernel
      have hl : raw9390step1Labels = raw9390step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9390step0 raw9390step0Labels permutation56 hz
    mixedMoment B raw9390step1 raw9390step1Labels = mixedMoment B raw9390step2 raw9390step2Labels := by
      have ha : raw9390step2 = (fun i j => raw9390step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9390step2 raw9390step1; decide +kernel
      have hl : raw9390step2Labels = raw9390step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9390step1 raw9390step1Labels permutation29 permutation2
    mixedMoment B raw9390step2 raw9390step2Labels = mixedMoment B raw9390step3 raw9390step3Labels := by
      have ha : raw9390step3 = -raw9390step2 := by apply Matrix.ext; change ∀ i j, raw9390step3 i j = -(raw9390step2 i j); unfold raw9390step3 raw9390step2; decide +kernel
      have hl : raw9390step3Labels = raw9390step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4890 node4890Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5169 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5169 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5169 = injectiveMoment H raw5169step0 := by
      have hz : ∀ j, raw5169 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5169step0 = (fun i j => raw5169 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5169 permutation21 hz
    injectiveMoment H raw5169step0 = injectiveMoment H raw5169step1 := by
      have hz : ∀ j, raw5169step0 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5169step1 = (fun i j => raw5169step0 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5169step0 permutation5 hz
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

theorem canonical5210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5210 = injectiveMoment H node4 := by
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

theorem canonical7738 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7738 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7738 = injectiveMoment H raw7738step0 := by
      have heq : raw7738step0 = (fun i j => raw7738 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7738 permutation13 permutation1
    _ = injectiveMoment H node65 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical808 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw808 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw808 = injectiveMoment H raw808step0 := by
      have heq : raw808step0 = -raw808 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw808).symm
    injectiveMoment H raw808step0 = injectiveMoment H raw808step1 := by
      have heq : raw808step1 = (fun i j => raw808step0 (permutation9 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw808step0 permutation9 permutation8
    _ = injectiveMoment H node176 := by rfl

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

theorem canonical914 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw914 = injectiveMoment H node26 := by
  rfl

theorem canonical917 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw917 = injectiveMoment H node10 := by
  rfl

theorem canonical924 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw924 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw924 = injectiveMoment H raw924step0 := by
      have heq : raw924step0 = (fun i j => raw924 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw924 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

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

theorem sound26 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node26 = Sparse.eval value26 (momentVector H) := by
  have heq : pivotMatrix26 = (fun u v => node26 (pivotPermutation26 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node26 = injectiveMoment H pivotMatrix26 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix26 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix26 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix26 (0 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix26 (0 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix26 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix26 (1 : Fin 3) = raw924 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical924 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix26 (2 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix26 (2 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node26 + (injectiveMoment H (mergeFirst pivotMatrix26 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix26 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix26 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value26, value10, value11, Sparse.eval] at hc ⊢
  linarith

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2823 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2823 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw2823 = injectiveMoment H raw2823step0 := by
      have heq : raw2823step0 = (fun i j => raw2823 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2823 permutation4 permutation5
    _ = injectiveMoment H node57 := by rfl

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

theorem sound176 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node176 = Sparse.eval value176 (momentVector H) := by
  have heq : pivotMatrix176 = (fun u v => node176 (pivotPermutation176 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node176 = injectiveMoment H pivotMatrix176 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix176 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix176 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix176 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (0 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix176 (1 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (1 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix176 (2 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (2 : Fin 3) = raw2823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2823 hH).trans (sound57 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node176 + (injectiveMoment H (mergeFirst pivotMatrix176 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix176 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix176 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value176, value36, value57, value62, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair416 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node416 node416Labels = Sparse.eval singlePairValue416 (familyPairVector B) := by
  have hp := single_label_three B hB node416
  have hl : node416Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node416 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node416 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node416 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node416 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node416 (EqualityPatterns.family3.label 1) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node416 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node416 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node416 (EqualityPatterns.family3.label 2) = PairSemantics.raw7738 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node416 PairSemantics.raw7738; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7738 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node416 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node416 (EqualityPatterns.family3.label 3) = PairSemantics.raw914 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node416 PairSemantics.raw914; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical914 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node416 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value176 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node416 (EqualityPatterns.family3.label 4) = PairSemantics.raw808 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node416 PairSemantics.raw808; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical808 hH).trans (PairSemantics.sound176 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue416, PairSemantics.value0, PairSemantics.value4, PairSemantics.value26, PairSemantics.value65, PairSemantics.value176, Sparse.eval] at hp ⊢
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

theorem singleton2784 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2784 node2784Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node416 node416Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw282 singletonSmall2784
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2784) = raw282Labels := by decide +kernel
  rw [hl, canonical282 B hB] at h
  have hc0 : mixedMoment B raw282 (Fin.cases (0 : Fin 1) singletonSmall2784) =
      mixedMoment B node416 node416Labels := by
    have ha : raw282 = raw283 := by apply Matrix.ext; unfold raw282 raw283; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2784 = raw283Labels := by decide +kernel
    rw [ha, hj, canonical283 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
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

theorem singleton4807 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4807 node4807Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2025 node2025Labels + mixedMoment B node2224 node2224Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1743 singletonSmall4807
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4807) = raw1743Labels := by decide +kernel
  rw [hl, canonical1743 B hB] at h
  have hc0 : mixedMoment B raw1743 (Fin.cases (0 : Fin 2) singletonSmall4807) =
      mixedMoment B node2025 node2025Labels := by
    have ha : raw1743 = raw1744 := by apply Matrix.ext; unfold raw1743 raw1744; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4807 = raw1744Labels := by decide +kernel
    rw [ha, hj, canonical1744 B hB]
  have hc1 : mixedMoment B raw1743 (Fin.cases (1 : Fin 2) singletonSmall4807) =
      mixedMoment B node2224 node2224Labels := by
    have ha : raw1743 = raw1745 := by apply Matrix.ext; unfold raw1743 raw1745; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4807 = raw1745Labels := by decide +kernel
    rw [ha, hj, canonical1745 B hB]
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

theorem singleton5271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5271 node5271Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2739 node2739Labels + mixedMoment B node3534 node3534Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2280 singletonSmall5271
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5271) = raw2280Labels := by decide +kernel
  rw [hl, canonical2280 B hB] at h
  have hc0 : mixedMoment B raw2280 (Fin.cases (0 : Fin 2) singletonSmall5271) =
      mixedMoment B node2739 node2739Labels := by
    have ha : raw2280 = raw2281 := by apply Matrix.ext; unfold raw2280 raw2281; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5271 = raw2281Labels := by decide +kernel
    rw [ha, hj, canonical2281 B hB]
  have hc1 : mixedMoment B raw2280 (Fin.cases (1 : Fin 2) singletonSmall5271) =
      mixedMoment B node3534 node3534Labels := by
    have ha : raw2280 = raw2282 := by apply Matrix.ext; unfold raw2280 raw2282; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5271 = raw2282Labels := by decide +kernel
    rw [ha, hj, canonical2282 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton5306 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5306 node5306Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2784 node2784Labels + mixedMoment B node3623 node3623Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2322 singletonSmall5306
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5306) = raw2322Labels := by decide +kernel
  rw [hl, canonical2322 B hB] at h
  have hc0 : mixedMoment B raw2322 (Fin.cases (0 : Fin 2) singletonSmall5306) =
      mixedMoment B node2784 node2784Labels := by
    have ha : raw2322 = raw2323 := by apply Matrix.ext; unfold raw2322 raw2323; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5306 = raw2323Labels := by decide +kernel
    rw [ha, hj, canonical2323 B hB]
  have hc1 : mixedMoment B raw2322 (Fin.cases (1 : Fin 2) singletonSmall5306) =
      mixedMoment B node3623 node3623Labels := by
    have ha : raw2322 = raw2324 := by apply Matrix.ext; unfold raw2322 raw2324; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5306 = raw2324Labels := by decide +kernel
    rw [ha, hj, canonical2324 B hB]
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

theorem sound1250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1250 node1250Labels = Sparse.eval nodeValue1250 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1250) = mixedMoment B node1250 node1250Labels := rfl
  simpa [nodeValue1250, Sparse.eval] using hc.symm

theorem sound1252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1252 node1252Labels = Sparse.eval nodeValue1252 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1252) = mixedMoment B node1252 node1252Labels := rfl
  simpa [nodeValue1252, Sparse.eval] using hc.symm

theorem sound1253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1253 node1253Labels = Sparse.eval nodeValue1253 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1253) = mixedMoment B node1253 node1253Labels := rfl
  simpa [nodeValue1253, Sparse.eval] using hc.symm

theorem sound1270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1270 node1270Labels = Sparse.eval nodeValue1270 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1270) = mixedMoment B node1270 node1270Labels := rfl
  simpa [nodeValue1270, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1383 node1383Labels = Sparse.eval nodeValue1383 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1383) = mixedMoment B node1383 node1383Labels := rfl
  simpa [nodeValue1383, Sparse.eval] using hc.symm

theorem sound1388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1388 node1388Labels = Sparse.eval nodeValue1388 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1388) = mixedMoment B node1388 node1388Labels := rfl
  simpa [nodeValue1388, Sparse.eval] using hc.symm

theorem sound1391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1391 node1391Labels = Sparse.eval nodeValue1391 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1391) = mixedMoment B node1391 node1391Labels := rfl
  simpa [nodeValue1391, Sparse.eval] using hc.symm

theorem sound1406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1406 node1406Labels = Sparse.eval nodeValue1406 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1406) = mixedMoment B node1406 node1406Labels := rfl
  simpa [nodeValue1406, Sparse.eval] using hc.symm

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

theorem sound1421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1421 node1421Labels = Sparse.eval nodeValue1421 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1421) = mixedMoment B node1421 node1421Labels := rfl
  simpa [nodeValue1421, Sparse.eval] using hc.symm

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

theorem sound2025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2025 node2025Labels = Sparse.eval nodeValue2025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2025) = mixedMoment B node2025 node2025Labels := rfl
  simpa [nodeValue2025, Sparse.eval] using hc.symm

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

theorem sound2224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2224 node2224Labels = Sparse.eval nodeValue2224 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2224) = mixedMoment B node2224 node2224Labels := rfl
  simpa [nodeValue2224, Sparse.eval] using hc.symm

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

theorem sound2247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2247 node2247Labels = Sparse.eval nodeValue2247 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2247) = mixedMoment B node2247 node2247Labels := rfl
  simpa [nodeValue2247, Sparse.eval] using hc.symm

theorem sound2290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2290 node2290Labels = Sparse.eval nodeValue2290 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2290) = mixedMoment B node2290 node2290Labels := rfl
  simpa [nodeValue2290, Sparse.eval] using hc.symm

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

theorem sound2470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2470 node2470Labels = Sparse.eval nodeValue2470 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2470) = mixedMoment B node2470 node2470Labels := rfl
  simpa [nodeValue2470, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2509 node2509Labels = Sparse.eval nodeValue2509 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2509) = mixedMoment B node2509 node2509Labels := rfl
  simpa [nodeValue2509, Sparse.eval] using hc.symm

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

theorem sound2564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2564 node2564Labels = Sparse.eval nodeValue2564 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2564) = mixedMoment B node2564 node2564Labels := rfl
  simpa [nodeValue2564, Sparse.eval] using hc.symm

theorem sound2573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2573 node2573Labels = Sparse.eval nodeValue2573 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2573) = mixedMoment B node2573 node2573Labels := rfl
  simpa [nodeValue2573, Sparse.eval] using hc.symm

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

theorem sound2625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2625 node2625Labels = Sparse.eval nodeValue2625 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2625) = mixedMoment B node2625 node2625Labels := rfl
  simpa [nodeValue2625, Sparse.eval] using hc.symm

theorem sound2641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2641 node2641Labels = Sparse.eval nodeValue2641 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2641) = mixedMoment B node2641 node2641Labels := rfl
  simpa [nodeValue2641, Sparse.eval] using hc.symm

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

theorem sound2739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2739 node2739Labels = Sparse.eval nodeValue2739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2739) = mixedMoment B node2739 node2739Labels := rfl
  simpa [nodeValue2739, Sparse.eval] using hc.symm

theorem sound2746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2746 node2746Labels = Sparse.eval nodeValue2746 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2746) = mixedMoment B node2746 node2746Labels := rfl
  simpa [nodeValue2746, Sparse.eval] using hc.symm

theorem sound2750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2750 node2750Labels = Sparse.eval nodeValue2750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2750) = mixedMoment B node2750 node2750Labels := rfl
  simpa [nodeValue2750, Sparse.eval] using hc.symm

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

theorem sound416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node416 node416Labels = Sparse.eval nodeValue416 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue416 (familyPairVector B) := singlePair416 B _hB
    _ = _ := by
      norm_num [singlePairValue416, nodeValue416, Sparse.eval, mixedVector]
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

theorem sound2754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2754 node2754Labels = Sparse.eval nodeValue2754 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2754) = mixedMoment B node2754 node2754Labels := rfl
  simpa [nodeValue2754, Sparse.eval] using hc.symm

theorem sound2764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2764 node2764Labels = Sparse.eval nodeValue2764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2764) = mixedMoment B node2764 node2764Labels := rfl
  simpa [nodeValue2764, Sparse.eval] using hc.symm

theorem sound2784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2784 node2784Labels = Sparse.eval nodeValue2784 (mixedVector B) := by
  have h := singleton2784 B _hB
  rw [sound416 B _hB _hF] at h
  norm_num [nodeValue2784, nodeValue416, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2981 node2981Labels = Sparse.eval nodeValue2981 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2981) = mixedMoment B node2981 node2981Labels := rfl
  simpa [nodeValue2981, Sparse.eval] using hc.symm

theorem sound2984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2984 node2984Labels = Sparse.eval nodeValue2984 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2984) = mixedMoment B node2984 node2984Labels := rfl
  simpa [nodeValue2984, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3037 node3037Labels = Sparse.eval nodeValue3037 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3037) = mixedMoment B node3037 node3037Labels := rfl
  simpa [nodeValue3037, Sparse.eval] using hc.symm

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

theorem sound3493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3493 node3493Labels = Sparse.eval nodeValue3493 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3493) = mixedMoment B node3493 node3493Labels := rfl
  simpa [nodeValue3493, Sparse.eval] using hc.symm

theorem sound3498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3498 node3498Labels = Sparse.eval nodeValue3498 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3498) = mixedMoment B node3498 node3498Labels := rfl
  simpa [nodeValue3498, Sparse.eval] using hc.symm

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

theorem zero3547 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3547 node3547Labels = 0 := by
  exact mixedMoment_order_one B hB node3547 node3547Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3534 node3534Labels = Sparse.eval nodeValue3534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3534) = mixedMoment B node3534 node3534Labels := rfl
  simpa [nodeValue3534, Sparse.eval] using hc.symm

theorem sound3547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3547 node3547Labels = Sparse.eval nodeValue3547 (mixedVector B) := by
  simpa only [nodeValue3547, Sparse.eval_nil] using zero3547 B _hB _hF

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

theorem sound3623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3623 node3623Labels = Sparse.eval nodeValue3623 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3623) = mixedMoment B node3623 node3623Labels := rfl
  simpa [nodeValue3623, Sparse.eval] using hc.symm

theorem sound3625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3625 node3625Labels = Sparse.eval nodeValue3625 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3625) = mixedMoment B node3625 node3625Labels := rfl
  simpa [nodeValue3625, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3808 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3808 node3808Labels = 0 := by
  exact mixedMoment_order_one B hB node3808 node3808Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3808 node3808Labels = Sparse.eval nodeValue3808 (mixedVector B) := by
  simpa only [nodeValue3808, Sparse.eval_nil] using zero3808 B _hB _hF

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

theorem sound3902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3902 node3902Labels = Sparse.eval nodeValue3902 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3902) = mixedMoment B node3902 node3902Labels := rfl
  simpa [nodeValue3902, Sparse.eval] using hc.symm

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

theorem sound4010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4010 node4010Labels = Sparse.eval nodeValue4010 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4010) = mixedMoment B node4010 node4010Labels := rfl
  simpa [nodeValue4010, Sparse.eval] using hc.symm

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

theorem sound4091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4091 node4091Labels = Sparse.eval nodeValue4091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4091) = mixedMoment B node4091 node4091Labels := rfl
  simpa [nodeValue4091, Sparse.eval] using hc.symm

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

theorem sound4441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4441 node4441Labels = Sparse.eval nodeValue4441 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4441) = mixedMoment B node4441 node4441Labels := rfl
  simpa [nodeValue4441, Sparse.eval] using hc.symm

theorem sound4442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4442 node4442Labels = Sparse.eval nodeValue4442 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4442) = mixedMoment B node4442 node4442Labels := rfl
  simpa [nodeValue4442, Sparse.eval] using hc.symm

theorem sound4443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4443 node4443Labels = Sparse.eval nodeValue4443 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4443) = mixedMoment B node4443 node4443Labels := rfl
  simpa [nodeValue4443, Sparse.eval] using hc.symm

theorem sound4462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4462 node4462Labels = Sparse.eval nodeValue4462 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4462) = mixedMoment B node4462 node4462Labels := rfl
  simpa [nodeValue4462, Sparse.eval] using hc.symm

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

theorem sound4792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4792 node4792Labels = Sparse.eval nodeValue4792 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4792) = mixedMoment B node4792 node4792Labels := rfl
  simpa [nodeValue4792, Sparse.eval] using hc.symm

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

theorem sound4807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4807 node4807Labels = Sparse.eval nodeValue4807 (mixedVector B) := by
  have h := singleton4807 B _hB
  rw [sound2025 B _hB _hF, sound2224 B _hB _hF] at h
  norm_num [nodeValue4807, nodeValue2025, nodeValue2224, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4890 node4890Labels = Sparse.eval nodeValue4890 (mixedVector B) := by
  have h := singleton4890 B _hB
  rw [sound2247 B _hB _hF, sound2290 B _hB _hF] at h
  norm_num [nodeValue4890, nodeValue2247, nodeValue2290, Sparse.eval] at h ⊢
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

theorem sound5066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5066 node5066Labels = Sparse.eval nodeValue5066 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5066) = mixedMoment B node5066 node5066Labels := rfl
  simpa [nodeValue5066, Sparse.eval] using hc.symm

theorem sound5077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5077 node5077Labels = Sparse.eval nodeValue5077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5077) = mixedMoment B node5077 node5077Labels := rfl
  simpa [nodeValue5077, Sparse.eval] using hc.symm

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

theorem sound5173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5173 node5173Labels = Sparse.eval nodeValue5173 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5173) = mixedMoment B node5173 node5173Labels := rfl
  simpa [nodeValue5173, Sparse.eval] using hc.symm

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

theorem zero5256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5256 node5256Labels = 0 := by
  exact mixedMoment_alpha B hF node5256 node5256Labels 1 permutation203
    (by decide +kernel)

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

theorem sound5256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5256 node5256Labels = Sparse.eval nodeValue5256 (mixedVector B) := by
  simpa only [nodeValue5256, Sparse.eval_nil] using zero5256 B _hB _hF

theorem sound5270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5270 node5270Labels = Sparse.eval nodeValue5270 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5270) = mixedMoment B node5270 node5270Labels := rfl
  simpa [nodeValue5270, Sparse.eval] using hc.symm

theorem sound5271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5271 node5271Labels = Sparse.eval nodeValue5271 (mixedVector B) := by
  have h := singleton5271 B _hB
  rw [sound2739 B _hB _hF, sound3534 B _hB _hF] at h
  norm_num [nodeValue5271, nodeValue2739, nodeValue3534, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5278 node5278Labels = Sparse.eval nodeValue5278 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5278) = mixedMoment B node5278 node5278Labels := rfl
  simpa [nodeValue5278, Sparse.eval] using hc.symm

theorem sound5279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5279 node5279Labels = Sparse.eval nodeValue5279 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5279) = mixedMoment B node5279 node5279Labels := rfl
  simpa [nodeValue5279, Sparse.eval] using hc.symm

theorem sound5288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5288 node5288Labels = Sparse.eval nodeValue5288 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5288) = mixedMoment B node5288 node5288Labels := rfl
  simpa [nodeValue5288, Sparse.eval] using hc.symm

theorem sound5290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5290 node5290Labels = Sparse.eval nodeValue5290 (mixedVector B) := by
  have h := singleton5290 B _hB
  rw [sound2764 B _hB _hF, sound3581 B _hB _hF] at h
  norm_num [nodeValue5290, nodeValue2764, nodeValue3581, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5295 node5295Labels = Sparse.eval nodeValue5295 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5295) = mixedMoment B node5295 node5295Labels := rfl
  simpa [nodeValue5295, Sparse.eval] using hc.symm

theorem sound5306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5306 node5306Labels = Sparse.eval nodeValue5306 (mixedVector B) := by
  have h := singleton5306 B _hB
  rw [sound2784 B _hB _hF, sound3623 B _hB _hF] at h
  norm_num [nodeValue5306, nodeValue2784, nodeValue3623, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources16
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq535 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm535 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA535 + difference 0 0) (sourceB535 + difference 0 0) sourceC535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA535 + difference 0 0) (sourceB535 + difference 0 0) sourceC535) = raw9218 := by
      apply Matrix.ext; unfold tripleCharges sourceA535 sourceB535 sourceC535 difference raw9218; decide +kernel
    rw [ha]
    exact (canonical9218 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA535 + difference 0 1) (sourceB535 + difference 1 0) sourceC535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA535 + difference 0 1) (sourceB535 + difference 1 0) sourceC535) = raw9219 := by
      apply Matrix.ext; unfold tripleCharges sourceA535 sourceB535 sourceC535 difference raw9219; decide +kernel
    rw [ha]
    exact (canonical9219 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA535 + difference 0 2) (sourceB535 + difference 2 0) sourceC535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA535 + difference 0 2) (sourceB535 + difference 2 0) sourceC535) = raw9220 := by
      apply Matrix.ext; unfold tripleCharges sourceA535 sourceB535 sourceC535 difference raw9220; decide +kernel
    rw [ha]
    exact (canonical9220 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA535 + difference 0 3) (sourceB535 + difference 3 0) sourceC535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA535 + difference 0 3) (sourceB535 + difference 3 0) sourceC535) = raw9221 := by
      apply Matrix.ext; unfold tripleCharges sourceA535 sourceB535 sourceC535 difference raw9221; decide +kernel
    rw [ha]
    exact (canonical9221 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA535 + difference 0 4) (sourceB535 + difference 4 0) sourceC535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3902) := by
    have ha : (tripleCharges (sourceA535 + difference 0 4) (sourceB535 + difference 4 0) sourceC535) = raw9222 := by
      apply Matrix.ext; unfold tripleCharges sourceA535 sourceB535 sourceC535 difference raw9222; decide +kernel
    rw [ha]
    exact (canonical9222 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA535 + difference 0 5) (sourceB535 + difference 5 0) sourceC535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4010) := by
    have ha : (tripleCharges (sourceA535 + difference 0 5) (sourceB535 + difference 5 0) sourceC535) = raw9223 := by
      apply Matrix.ext; unfold tripleCharges sourceA535 sourceB535 sourceC535 difference raw9223; decide +kernel
    rw [ha]
    exact (canonical9223 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA535 + sourceB535) sourceC535) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA535 + sourceB535) sourceC535) = raw9224 := by
      apply Matrix.ext; unfold doubleCharges sourceA535 sourceB535 sourceC535 raw9224; decide +kernel
    rw [ha]
    exact (canonical9224 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA535 sourceB535 sourceC535
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm535, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq536 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm536 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA536 + difference 0 0) (sourceB536 + difference 0 0) sourceC536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA536 + difference 0 0) (sourceB536 + difference 0 0) sourceC536) = raw9218 := by
      apply Matrix.ext; unfold tripleCharges sourceA536 sourceB536 sourceC536 difference raw9218; decide +kernel
    rw [ha]
    exact (canonical9218 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA536 + difference 1 0) (sourceB536 + difference 0 1) sourceC536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1383) := by
    have ha : (tripleCharges (sourceA536 + difference 1 0) (sourceB536 + difference 0 1) sourceC536) = raw9225 := by
      apply Matrix.ext; unfold tripleCharges sourceA536 sourceB536 sourceC536 difference raw9225; decide +kernel
    rw [ha]
    exact (canonical9225 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA536 + difference 2 0) (sourceB536 + difference 0 2) sourceC536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1406) := by
    have ha : (tripleCharges (sourceA536 + difference 2 0) (sourceB536 + difference 0 2) sourceC536) = raw9226 := by
      apply Matrix.ext; unfold tripleCharges sourceA536 sourceB536 sourceC536 difference raw9226; decide +kernel
    rw [ha]
    exact (canonical9226 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA536 + difference 3 0) (sourceB536 + difference 0 3) sourceC536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1406) := by
    have ha : (tripleCharges (sourceA536 + difference 3 0) (sourceB536 + difference 0 3) sourceC536) = raw9227 := by
      apply Matrix.ext; unfold tripleCharges sourceA536 sourceB536 sourceC536 difference raw9227; decide +kernel
    rw [ha]
    exact (canonical9227 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA536 + difference 4 0) (sourceB536 + difference 0 4) sourceC536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1391) := by
    have ha : (tripleCharges (sourceA536 + difference 4 0) (sourceB536 + difference 0 4) sourceC536) = raw9228 := by
      apply Matrix.ext; unfold tripleCharges sourceA536 sourceB536 sourceC536 difference raw9228; decide +kernel
    rw [ha]
    exact (canonical9228 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA536 + difference 5 0) (sourceB536 + difference 0 5) sourceC536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1388) := by
    have ha : (tripleCharges (sourceA536 + difference 5 0) (sourceB536 + difference 0 5) sourceC536) = raw9229 := by
      apply Matrix.ext; unfold tripleCharges sourceA536 sourceB536 sourceC536 difference raw9229; decide +kernel
    rw [ha]
    exact (canonical9229 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA536 + sourceB536) sourceC536) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA536 + sourceB536) sourceC536) = raw9224 := by
      apply Matrix.ext; unfold doubleCharges sourceA536 sourceB536 sourceC536 raw9224; decide +kernel
    rw [ha]
    exact (canonical9224 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA536 sourceB536 sourceC536
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm536, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq537 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm537 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA537 + difference 0 1) (sourceB537 + difference 1 0) sourceC537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA537 + difference 0 1) (sourceB537 + difference 1 0) sourceC537) = raw9219 := by
      apply Matrix.ext; unfold tripleCharges sourceA537 sourceB537 sourceC537 difference raw9219; decide +kernel
    rw [ha]
    exact (canonical9219 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA537 + difference 1 1) (sourceB537 + difference 1 1) sourceC537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA537 + difference 1 1) (sourceB537 + difference 1 1) sourceC537) = raw9218 := by
      apply Matrix.ext; unfold tripleCharges sourceA537 sourceB537 sourceC537 difference raw9218; decide +kernel
    rw [ha]
    exact (canonical9218 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA537 + difference 2 1) (sourceB537 + difference 1 2) sourceC537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2984) := by
    have ha : (tripleCharges (sourceA537 + difference 2 1) (sourceB537 + difference 1 2) sourceC537) = raw9230 := by
      apply Matrix.ext; unfold tripleCharges sourceA537 sourceB537 sourceC537 difference raw9230; decide +kernel
    rw [ha]
    exact (canonical9230 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA537 + difference 3 1) (sourceB537 + difference 1 3) sourceC537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2984) := by
    have ha : (tripleCharges (sourceA537 + difference 3 1) (sourceB537 + difference 1 3) sourceC537) = raw9231 := by
      apply Matrix.ext; unfold tripleCharges sourceA537 sourceB537 sourceC537 difference raw9231; decide +kernel
    rw [ha]
    exact (canonical9231 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA537 + difference 4 1) (sourceB537 + difference 1 4) sourceC537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2981) := by
    have ha : (tripleCharges (sourceA537 + difference 4 1) (sourceB537 + difference 1 4) sourceC537) = raw9232 := by
      apply Matrix.ext; unfold tripleCharges sourceA537 sourceB537 sourceC537 difference raw9232; decide +kernel
    rw [ha]
    exact (canonical9232 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA537 + difference 5 1) (sourceB537 + difference 1 5) sourceC537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2470) := by
    have ha : (tripleCharges (sourceA537 + difference 5 1) (sourceB537 + difference 1 5) sourceC537) = raw9233 := by
      apply Matrix.ext; unfold tripleCharges sourceA537 sourceB537 sourceC537 difference raw9233; decide +kernel
    rw [ha]
    exact (canonical9233 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA537 + sourceB537) sourceC537) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA537 + sourceB537) sourceC537) = raw9224 := by
      apply Matrix.ext; unfold doubleCharges sourceA537 sourceB537 sourceC537 raw9224; decide +kernel
    rw [ha]
    exact (canonical9224 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA537 sourceB537 sourceC537
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm537, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq541 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm541 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA541 + difference 0 0) (sourceB541 + difference 0 0) sourceC541) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA541 + difference 0 0) (sourceB541 + difference 0 0) sourceC541) = raw5749 := by
      apply Matrix.ext; unfold tripleCharges sourceA541 sourceB541 sourceC541 difference raw5749; decide +kernel
    rw [ha]
    exact (canonical5749 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA541 + difference 0 1) (sourceB541 + difference 1 0) sourceC541) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3493) := by
    have ha : (tripleCharges (sourceA541 + difference 0 1) (sourceB541 + difference 1 0) sourceC541) = raw7278 := by
      apply Matrix.ext; unfold tripleCharges sourceA541 sourceB541 sourceC541 difference raw7278; decide +kernel
    rw [ha]
    exact (canonical7278 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA541 + difference 0 2) (sourceB541 + difference 2 0) sourceC541) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA541 + difference 0 2) (sourceB541 + difference 2 0) sourceC541) = raw7960 := by
      apply Matrix.ext; unfold tripleCharges sourceA541 sourceB541 sourceC541 difference raw7960; decide +kernel
    rw [ha]
    exact (canonical7960 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA541 + difference 0 3) (sourceB541 + difference 3 0) sourceC541) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA541 + difference 0 3) (sourceB541 + difference 3 0) sourceC541) = raw9250 := by
      apply Matrix.ext; unfold tripleCharges sourceA541 sourceB541 sourceC541 difference raw9250; decide +kernel
    rw [ha]
    exact (canonical9250 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA541 + difference 0 4) (sourceB541 + difference 4 0) sourceC541) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3498) := by
    have ha : (tripleCharges (sourceA541 + difference 0 4) (sourceB541 + difference 4 0) sourceC541) = raw9076 := by
      apply Matrix.ext; unfold tripleCharges sourceA541 sourceB541 sourceC541 difference raw9076; decide +kernel
    rw [ha]
    exact (canonical9076 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA541 + difference 0 5) (sourceB541 + difference 5 0) sourceC541) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2509) := by
    have ha : (tripleCharges (sourceA541 + difference 0 5) (sourceB541 + difference 5 0) sourceC541) = raw9251 := by
      apply Matrix.ext; unfold tripleCharges sourceA541 sourceB541 sourceC541 difference raw9251; decide +kernel
    rw [ha]
    exact (canonical9251 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA541 + sourceB541) sourceC541) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA541 + sourceB541) sourceC541) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA541 sourceB541 sourceC541 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA541 sourceB541 sourceC541
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm541, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources17
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq545 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm545 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA545 + difference 0 0) (sourceB545 + difference 0 0) sourceC545) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA545 + difference 0 0) (sourceB545 + difference 0 0) sourceC545) = raw9342 := by
      apply Matrix.ext; unfold tripleCharges sourceA545 sourceB545 sourceC545 difference raw9342; decide +kernel
    rw [ha]
    exact (canonical9342 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA545 + difference 1 0) (sourceB545 + difference 0 1) sourceC545) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1250) := by
    have ha : (tripleCharges (sourceA545 + difference 1 0) (sourceB545 + difference 0 1) sourceC545) = raw9343 := by
      apply Matrix.ext; unfold tripleCharges sourceA545 sourceB545 sourceC545 difference raw9343; decide +kernel
    rw [ha]
    exact (canonical9343 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA545 + difference 2 0) (sourceB545 + difference 0 2) sourceC545) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA545 + difference 2 0) (sourceB545 + difference 0 2) sourceC545) = raw9344 := by
      apply Matrix.ext; unfold tripleCharges sourceA545 sourceB545 sourceC545 difference raw9344; decide +kernel
    rw [ha]
    exact (canonical9344 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA545 + difference 3 0) (sourceB545 + difference 0 3) sourceC545) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA545 + difference 3 0) (sourceB545 + difference 0 3) sourceC545) = raw9345 := by
      apply Matrix.ext; unfold tripleCharges sourceA545 sourceB545 sourceC545 difference raw9345; decide +kernel
    rw [ha]
    exact (canonical9345 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA545 + difference 4 0) (sourceB545 + difference 0 4) sourceC545) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1253) := by
    have ha : (tripleCharges (sourceA545 + difference 4 0) (sourceB545 + difference 0 4) sourceC545) = raw9346 := by
      apply Matrix.ext; unfold tripleCharges sourceA545 sourceB545 sourceC545 difference raw9346; decide +kernel
    rw [ha]
    exact (canonical9346 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA545 + difference 5 0) (sourceB545 + difference 0 5) sourceC545) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1252) := by
    have ha : (tripleCharges (sourceA545 + difference 5 0) (sourceB545 + difference 0 5) sourceC545) = raw9347 := by
      apply Matrix.ext; unfold tripleCharges sourceA545 sourceB545 sourceC545 difference raw9347; decide +kernel
    rw [ha]
    exact (canonical9347 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA545 + sourceB545) sourceC545) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA545 + sourceB545) sourceC545) = raw9348 := by
      apply Matrix.ext; unfold doubleCharges sourceA545 sourceB545 sourceC545 raw9348; decide +kernel
    rw [ha]
    exact (canonical9348 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA545 sourceB545 sourceC545
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm545, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq546 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm546 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA546 + difference 1 0) (sourceB546 + difference 0 1) sourceC546) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1250) := by
    have ha : (tripleCharges (sourceA546 + difference 1 0) (sourceB546 + difference 0 1) sourceC546) = raw9343 := by
      apply Matrix.ext; unfold tripleCharges sourceA546 sourceB546 sourceC546 difference raw9343; decide +kernel
    rw [ha]
    exact (canonical9343 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA546 + difference 1 1) (sourceB546 + difference 1 1) sourceC546) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA546 + difference 1 1) (sourceB546 + difference 1 1) sourceC546) = raw9342 := by
      apply Matrix.ext; unfold tripleCharges sourceA546 sourceB546 sourceC546 difference raw9342; decide +kernel
    rw [ha]
    exact (canonical9342 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA546 + difference 1 2) (sourceB546 + difference 2 1) sourceC546) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2625) := by
    have ha : (tripleCharges (sourceA546 + difference 1 2) (sourceB546 + difference 2 1) sourceC546) = raw9349 := by
      apply Matrix.ext; unfold tripleCharges sourceA546 sourceB546 sourceC546 difference raw9349; decide +kernel
    rw [ha]
    exact (canonical9349 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA546 + difference 1 3) (sourceB546 + difference 3 1) sourceC546) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2625) := by
    have ha : (tripleCharges (sourceA546 + difference 1 3) (sourceB546 + difference 3 1) sourceC546) = raw9350 := by
      apply Matrix.ext; unfold tripleCharges sourceA546 sourceB546 sourceC546 difference raw9350; decide +kernel
    rw [ha]
    exact (canonical9350 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA546 + difference 1 4) (sourceB546 + difference 4 1) sourceC546) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2746) := by
    have ha : (tripleCharges (sourceA546 + difference 1 4) (sourceB546 + difference 4 1) sourceC546) = raw9351 := by
      apply Matrix.ext; unfold tripleCharges sourceA546 sourceB546 sourceC546 difference raw9351; decide +kernel
    rw [ha]
    exact (canonical9351 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA546 + difference 1 5) (sourceB546 + difference 5 1) sourceC546) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA546 + difference 1 5) (sourceB546 + difference 5 1) sourceC546) = raw9352 := by
      apply Matrix.ext; unfold tripleCharges sourceA546 sourceB546 sourceC546 difference raw9352; decide +kernel
    rw [ha]
    exact (canonical9352 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA546 + sourceB546) sourceC546) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA546 + sourceB546) sourceC546) = raw9348 := by
      apply Matrix.ext; unfold doubleCharges sourceA546 sourceB546 sourceC546 raw9348; decide +kernel
    rw [ha]
    exact (canonical9348 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA546 sourceB546 sourceC546
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm546, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq547 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm547 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA547 + difference 0 1) (sourceB547 + difference 1 0) sourceC547) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA547 + difference 0 1) (sourceB547 + difference 1 0) sourceC547) = raw9353 := by
      apply Matrix.ext; unfold tripleCharges sourceA547 sourceB547 sourceC547 difference raw9353; decide +kernel
    rw [ha]
    exact (canonical9353 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA547 + difference 1 1) (sourceB547 + difference 1 1) sourceC547) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA547 + difference 1 1) (sourceB547 + difference 1 1) sourceC547) = raw9342 := by
      apply Matrix.ext; unfold tripleCharges sourceA547 sourceB547 sourceC547 difference raw9342; decide +kernel
    rw [ha]
    exact (canonical9342 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA547 + difference 2 1) (sourceB547 + difference 1 2) sourceC547) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2573) := by
    have ha : (tripleCharges (sourceA547 + difference 2 1) (sourceB547 + difference 1 2) sourceC547) = raw9354 := by
      apply Matrix.ext; unfold tripleCharges sourceA547 sourceB547 sourceC547 difference raw9354; decide +kernel
    rw [ha]
    exact (canonical9354 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA547 + difference 3 1) (sourceB547 + difference 1 3) sourceC547) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2573) := by
    have ha : (tripleCharges (sourceA547 + difference 3 1) (sourceB547 + difference 1 3) sourceC547) = raw9355 := by
      apply Matrix.ext; unfold tripleCharges sourceA547 sourceB547 sourceC547 difference raw9355; decide +kernel
    rw [ha]
    exact (canonical9355 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA547 + difference 4 1) (sourceB547 + difference 1 4) sourceC547) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2564) := by
    have ha : (tripleCharges (sourceA547 + difference 4 1) (sourceB547 + difference 1 4) sourceC547) = raw9356 := by
      apply Matrix.ext; unfold tripleCharges sourceA547 sourceB547 sourceC547 difference raw9356; decide +kernel
    rw [ha]
    exact (canonical9356 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA547 + difference 5 1) (sourceB547 + difference 1 5) sourceC547) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1421) := by
    have ha : (tripleCharges (sourceA547 + difference 5 1) (sourceB547 + difference 1 5) sourceC547) = raw9357 := by
      apply Matrix.ext; unfold tripleCharges sourceA547 sourceB547 sourceC547 difference raw9357; decide +kernel
    rw [ha]
    exact (canonical9357 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA547 + sourceB547) sourceC547) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA547 + sourceB547) sourceC547) = raw9348 := by
      apply Matrix.ext; unfold doubleCharges sourceA547 sourceB547 sourceC547 raw9348; decide +kernel
    rw [ha]
    exact (canonical9348 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA547 sourceB547 sourceC547
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm547, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq548 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm548 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA548 + difference 2 0) (sourceB548 + difference 0 2) sourceC548) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA548 + difference 2 0) (sourceB548 + difference 0 2) sourceC548) = raw9344 := by
      apply Matrix.ext; unfold tripleCharges sourceA548 sourceB548 sourceC548 difference raw9344; decide +kernel
    rw [ha]
    exact (canonical9344 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA548 + difference 2 1) (sourceB548 + difference 1 2) sourceC548) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2573) := by
    have ha : (tripleCharges (sourceA548 + difference 2 1) (sourceB548 + difference 1 2) sourceC548) = raw9354 := by
      apply Matrix.ext; unfold tripleCharges sourceA548 sourceB548 sourceC548 difference raw9354; decide +kernel
    rw [ha]
    exact (canonical9354 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA548 + difference 2 2) (sourceB548 + difference 2 2) sourceC548) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA548 + difference 2 2) (sourceB548 + difference 2 2) sourceC548) = raw9342 := by
      apply Matrix.ext; unfold tripleCharges sourceA548 sourceB548 sourceC548 difference raw9342; decide +kernel
    rw [ha]
    exact (canonical9342 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA548 + difference 2 3) (sourceB548 + difference 3 2) sourceC548) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2641) := by
    have ha : (tripleCharges (sourceA548 + difference 2 3) (sourceB548 + difference 3 2) sourceC548) = raw9358 := by
      apply Matrix.ext; unfold tripleCharges sourceA548 sourceB548 sourceC548 difference raw9358; decide +kernel
    rw [ha]
    exact (canonical9358 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA548 + difference 2 4) (sourceB548 + difference 4 2) sourceC548) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA548 + difference 2 4) (sourceB548 + difference 4 2) sourceC548) = raw9359 := by
      apply Matrix.ext; unfold tripleCharges sourceA548 sourceB548 sourceC548 difference raw9359; decide +kernel
    rw [ha]
    exact (canonical9359 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA548 + difference 2 5) (sourceB548 + difference 5 2) sourceC548) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA548 + difference 2 5) (sourceB548 + difference 5 2) sourceC548) = raw9360 := by
      apply Matrix.ext; unfold tripleCharges sourceA548 sourceB548 sourceC548 difference raw9360; decide +kernel
    rw [ha]
    exact (canonical9360 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA548 + sourceB548) sourceC548) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA548 + sourceB548) sourceC548) = raw9348 := by
      apply Matrix.ext; unfold doubleCharges sourceA548 sourceB548 sourceC548 raw9348; decide +kernel
    rw [ha]
    exact (canonical9348 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA548 sourceB548 sourceC548
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm548, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq549 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm549 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA549 + difference 0 1) (sourceB549 + difference 1 0) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA549 + difference 0 1) (sourceB549 + difference 1 0) sourceC549) = raw9361 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9361; decide +kernel
    rw [ha]
    exact (canonical9361 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA549 + difference 0 2) (sourceB549 + difference 2 0) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA549 + difference 0 2) (sourceB549 + difference 2 0) sourceC549) = raw9362 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9362; decide +kernel
    rw [ha]
    exact (canonical9362 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA549 + difference 0 3) (sourceB549 + difference 3 0) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA549 + difference 0 3) (sourceB549 + difference 3 0) sourceC549) = raw9363 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9363; decide +kernel
    rw [ha]
    exact (canonical9363 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA549 + difference 0 4) (sourceB549 + difference 4 0) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA549 + difference 0 4) (sourceB549 + difference 4 0) sourceC549) = raw9364 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9364; decide +kernel
    rw [ha]
    exact (canonical9364 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA549 + difference 0 5) (sourceB549 + difference 5 0) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA549 + difference 0 5) (sourceB549 + difference 5 0) sourceC549) = raw9365 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9365; decide +kernel
    rw [ha]
    exact (canonical9365 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA549 + difference 1 0) (sourceB549 + difference 0 1) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4441) := by
    have ha : (tripleCharges (sourceA549 + difference 1 0) (sourceB549 + difference 0 1) sourceC549) = raw9366 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9366; decide +kernel
    rw [ha]
    exact (canonical9366 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA549 + difference 1 2) (sourceB549 + difference 2 1) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5150) := by
    have ha : (tripleCharges (sourceA549 + difference 1 2) (sourceB549 + difference 2 1) sourceC549) = raw9367 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9367; decide +kernel
    rw [ha]
    exact (canonical9367 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA549 + difference 1 3) (sourceB549 + difference 3 1) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5150) := by
    have ha : (tripleCharges (sourceA549 + difference 1 3) (sourceB549 + difference 3 1) sourceC549) = raw9368 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9368; decide +kernel
    rw [ha]
    exact (canonical9368 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA549 + difference 1 4) (sourceB549 + difference 4 1) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA549 + difference 1 4) (sourceB549 + difference 4 1) sourceC549) = raw9369 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9369; decide +kernel
    rw [ha]
    exact (canonical9369 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA549 + difference 1 5) (sourceB549 + difference 5 1) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5278) := by
    have ha : (tripleCharges (sourceA549 + difference 1 5) (sourceB549 + difference 5 1) sourceC549) = raw9370 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9370; decide +kernel
    rw [ha]
    exact (canonical9370 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA549 + difference 2 0) (sourceB549 + difference 0 2) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4462) := by
    have ha : (tripleCharges (sourceA549 + difference 2 0) (sourceB549 + difference 0 2) sourceC549) = raw9371 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9371; decide +kernel
    rw [ha]
    exact (canonical9371 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA549 + difference 2 1) (sourceB549 + difference 1 2) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5077) := by
    have ha : (tripleCharges (sourceA549 + difference 2 1) (sourceB549 + difference 1 2) sourceC549) = raw9372 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9372; decide +kernel
    rw [ha]
    exact (canonical9372 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA549 + difference 2 3) (sourceB549 + difference 3 2) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA549 + difference 2 3) (sourceB549 + difference 3 2) sourceC549) = raw9373 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9373; decide +kernel
    rw [ha]
    exact (canonical9373 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA549 + difference 2 4) (sourceB549 + difference 4 2) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA549 + difference 2 4) (sourceB549 + difference 4 2) sourceC549) = raw9374 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9374; decide +kernel
    rw [ha]
    exact (canonical9374 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA549 + difference 2 5) (sourceB549 + difference 5 2) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5288) := by
    have ha : (tripleCharges (sourceA549 + difference 2 5) (sourceB549 + difference 5 2) sourceC549) = raw9375 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9375; decide +kernel
    rw [ha]
    exact (canonical9375 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA549 + difference 3 0) (sourceB549 + difference 0 3) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4462) := by
    have ha : (tripleCharges (sourceA549 + difference 3 0) (sourceB549 + difference 0 3) sourceC549) = raw9376 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9376; decide +kernel
    rw [ha]
    exact (canonical9376 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA549 + difference 3 1) (sourceB549 + difference 1 3) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5077) := by
    have ha : (tripleCharges (sourceA549 + difference 3 1) (sourceB549 + difference 1 3) sourceC549) = raw9377 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9377; decide +kernel
    rw [ha]
    exact (canonical9377 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA549 + difference 3 2) (sourceB549 + difference 2 3) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA549 + difference 3 2) (sourceB549 + difference 2 3) sourceC549) = raw9378 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9378; decide +kernel
    rw [ha]
    exact (canonical9378 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA549 + difference 3 4) (sourceB549 + difference 4 3) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA549 + difference 3 4) (sourceB549 + difference 4 3) sourceC549) = raw9379 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9379; decide +kernel
    rw [ha]
    exact (canonical9379 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA549 + difference 3 5) (sourceB549 + difference 5 3) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5288) := by
    have ha : (tripleCharges (sourceA549 + difference 3 5) (sourceB549 + difference 5 3) sourceC549) = raw9380 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9380; decide +kernel
    rw [ha]
    exact (canonical9380 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA549 + difference 4 0) (sourceB549 + difference 0 4) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4443) := by
    have ha : (tripleCharges (sourceA549 + difference 4 0) (sourceB549 + difference 0 4) sourceC549) = raw9381 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9381; decide +kernel
    rw [ha]
    exact (canonical9381 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA549 + difference 4 1) (sourceB549 + difference 1 4) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5066) := by
    have ha : (tripleCharges (sourceA549 + difference 4 1) (sourceB549 + difference 1 4) sourceC549) = raw9382 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9382; decide +kernel
    rw [ha]
    exact (canonical9382 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA549 + difference 4 2) (sourceB549 + difference 2 4) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5151) := by
    have ha : (tripleCharges (sourceA549 + difference 4 2) (sourceB549 + difference 2 4) sourceC549) = raw9383 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9383; decide +kernel
    rw [ha]
    exact (canonical9383 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA549 + difference 4 3) (sourceB549 + difference 3 4) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5151) := by
    have ha : (tripleCharges (sourceA549 + difference 4 3) (sourceB549 + difference 3 4) sourceC549) = raw9384 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9384; decide +kernel
    rw [ha]
    exact (canonical9384 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA549 + difference 4 5) (sourceB549 + difference 5 4) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5279) := by
    have ha : (tripleCharges (sourceA549 + difference 4 5) (sourceB549 + difference 5 4) sourceC549) = raw9385 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9385; decide +kernel
    rw [ha]
    exact (canonical9385 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA549 + difference 5 0) (sourceB549 + difference 0 5) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4442) := by
    have ha : (tripleCharges (sourceA549 + difference 5 0) (sourceB549 + difference 0 5) sourceC549) = raw9386 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9386; decide +kernel
    rw [ha]
    exact (canonical9386 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA549 + difference 5 1) (sourceB549 + difference 1 5) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4792) := by
    have ha : (tripleCharges (sourceA549 + difference 5 1) (sourceB549 + difference 1 5) sourceC549) = raw9387 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9387; decide +kernel
    rw [ha]
    exact (canonical9387 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA549 + difference 5 2) (sourceB549 + difference 2 5) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA549 + difference 5 2) (sourceB549 + difference 2 5) sourceC549) = raw9388 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9388; decide +kernel
    rw [ha]
    exact (canonical9388 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA549 + difference 5 3) (sourceB549 + difference 3 5) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA549 + difference 5 3) (sourceB549 + difference 3 5) sourceC549) = raw9389 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9389; decide +kernel
    rw [ha]
    exact (canonical9389 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA549 + difference 5 4) (sourceB549 + difference 4 5) sourceC549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA549 + difference 5 4) (sourceB549 + difference 4 5) sourceC549) = raw9390 := by
      apply Matrix.ext; unfold tripleCharges sourceA549 sourceB549 sourceC549 difference raw9390; decide +kernel
    rw [ha]
    exact (canonical9390 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA549 sourceB549 sourceC549
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm549, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck449 : Integer.Sparse.reindex keyMap MixedData.row449 = numericRow449 := by decide +kernel

theorem numericCheck449 (x : Master → ℝ) : Integer.Sparse.eval numericRow449 x =
    (1 : ℝ) * reducedSource449 x := by
  norm_num [numericRow449, reducedSource449, Integer.Sparse.eval, Sparse.eval, nodeValue3077, nodeValue3800, nodeValue3808, nodeValue3902, nodeValue4010, nodeValue4091]

theorem reindexCheck450 : Integer.Sparse.reindex keyMap MixedData.row450 = numericRow450 := by decide +kernel

theorem numericCheck450 (x : Master → ℝ) : Integer.Sparse.eval numericRow450 x =
    (1 : ℝ) * reducedSource450 x := by
  norm_num [numericRow450, reducedSource450, Integer.Sparse.eval, Sparse.eval, nodeValue1383, nodeValue1388, nodeValue1391, nodeValue1406, nodeValue3077, nodeValue4091]

theorem reindexCheck451 : Integer.Sparse.reindex keyMap MixedData.row451 = numericRow451 := by decide +kernel

theorem numericCheck451 (x : Master → ℝ) : Integer.Sparse.eval numericRow451 x =
    (1 : ℝ) * reducedSource451 x := by
  norm_num [numericRow451, reducedSource451, Integer.Sparse.eval, Sparse.eval, nodeValue2470, nodeValue2981, nodeValue2984, nodeValue3077, nodeValue3800, nodeValue4091]

theorem reindexCheck455 : Integer.Sparse.reindex keyMap MixedData.row455 = numericRow455 := by decide +kernel

theorem numericCheck455 (x : Master → ℝ) : Integer.Sparse.eval numericRow455 x =
    (1 : ℝ) * reducedSource455 x := by
  norm_num [numericRow455, reducedSource455, Integer.Sparse.eval, Sparse.eval, nodeValue2509, nodeValue3493, nodeValue3498, nodeValue3547, nodeValue3625, nodeValue4084]

theorem reindexCheck457 : Integer.Sparse.reindex keyMap MixedData.row457 = numericRow457 := by decide +kernel

theorem numericCheck457 (x : Master → ℝ) : Integer.Sparse.eval numericRow457 x =
    (1 : ℝ) * reducedSource457 x := by
  norm_num [numericRow457, reducedSource457, Integer.Sparse.eval, Sparse.eval, nodeValue1250, nodeValue1252, nodeValue1253, nodeValue1270, nodeValue2754, nodeValue4091]

theorem reindexCheck458 : Integer.Sparse.reindex keyMap MixedData.row458 = numericRow458 := by decide +kernel

theorem numericCheck458 (x : Master → ℝ) : Integer.Sparse.eval numericRow458 x =
    (1 : ℝ) * reducedSource458 x := by
  norm_num [numericRow458, reducedSource458, Integer.Sparse.eval, Sparse.eval, nodeValue1250, nodeValue2625, nodeValue2746, nodeValue2750, nodeValue2754, nodeValue4091]

theorem reindexCheck459 : Integer.Sparse.reindex keyMap MixedData.row459 = numericRow459 := by decide +kernel

theorem numericCheck459 (x : Master → ℝ) : Integer.Sparse.eval numericRow459 x =
    (1 : ℝ) * reducedSource459 x := by
  norm_num [numericRow459, reducedSource459, Integer.Sparse.eval, Sparse.eval, nodeValue1421, nodeValue2564, nodeValue2573, nodeValue2754, nodeValue3037, nodeValue4091]

theorem reindexCheck460 : Integer.Sparse.reindex keyMap MixedData.row460 = numericRow460 := by decide +kernel

theorem numericCheck460 (x : Master → ℝ) : Integer.Sparse.eval numericRow460 x =
    (1 : ℝ) * reducedSource460 x := by
  norm_num [numericRow460, reducedSource460, Integer.Sparse.eval, Sparse.eval, nodeValue1270, nodeValue2573, nodeValue2641, nodeValue2754, nodeValue2764, nodeValue4091]

theorem reindexCheck461 : Integer.Sparse.reindex keyMap MixedData.row461 = numericRow461 := by decide +kernel

theorem numericCheck461 (x : Master → ℝ) : Integer.Sparse.eval numericRow461 x =
    (8640 : ℝ) * reducedSource461 x := by
  norm_num [numericRow461, reducedSource461, Integer.Sparse.eval, Sparse.eval, nodeValue4441, nodeValue4442, nodeValue4443, nodeValue4462, nodeValue4792, nodeValue4807, nodeValue4890, nodeValue5066, nodeValue5077, nodeValue5150, nodeValue5151, nodeValue5173, nodeValue5256, nodeValue5270, nodeValue5271, nodeValue5278, nodeValue5279, nodeValue5288, nodeValue5290, nodeValue5295, nodeValue5306]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero449 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource449 (mixedVector B) = 0 := by
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h3800 : mixedVector B (Sum.inr 3800) = Sparse.eval nodeValue3800 (mixedVector B) := by
    change mixedMoment B node3800 node3800Labels = _
    exact sound3800 B hB hF
  have h3808 : mixedVector B (Sum.inr 3808) = Sparse.eval nodeValue3808 (mixedVector B) := by
    change mixedMoment B node3808 node3808Labels = _
    exact sound3808 B hB hF
  have h3902 : mixedVector B (Sum.inr 3902) = Sparse.eval nodeValue3902 (mixedVector B) := by
    change mixedMoment B node3902 node3902Labels = _
    exact sound3902 B hB hF
  have h4010 : mixedVector B (Sum.inr 4010) = Sparse.eval nodeValue4010 (mixedVector B) := by
    change mixedMoment B node4010 node4010Labels = _
    exact sound4010 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm535, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3077, h3800, h3808, h3902, h4010, h4091, reducedSource449] using sourceEq535 B hB

theorem rowSound449 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row449 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck449, numericCheck449, reducedZero449 B hB hF, mul_zero]

theorem reducedZero450 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource450 (mixedVector B) = 0 := by
  have h1383 : mixedVector B (Sum.inr 1383) = Sparse.eval nodeValue1383 (mixedVector B) := by
    change mixedMoment B node1383 node1383Labels = _
    exact sound1383 B hB hF
  have h1388 : mixedVector B (Sum.inr 1388) = Sparse.eval nodeValue1388 (mixedVector B) := by
    change mixedMoment B node1388 node1388Labels = _
    exact sound1388 B hB hF
  have h1391 : mixedVector B (Sum.inr 1391) = Sparse.eval nodeValue1391 (mixedVector B) := by
    change mixedMoment B node1391 node1391Labels = _
    exact sound1391 B hB hF
  have h1406 : mixedVector B (Sum.inr 1406) = Sparse.eval nodeValue1406 (mixedVector B) := by
    change mixedMoment B node1406 node1406Labels = _
    exact sound1406 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm536, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1383, h1388, h1391, h1406, h3077, h4091, reducedSource450] using sourceEq536 B hB

theorem rowSound450 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row450 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck450, numericCheck450, reducedZero450 B hB hF, mul_zero]

theorem reducedZero451 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource451 (mixedVector B) = 0 := by
  have h2470 : mixedVector B (Sum.inr 2470) = Sparse.eval nodeValue2470 (mixedVector B) := by
    change mixedMoment B node2470 node2470Labels = _
    exact sound2470 B hB hF
  have h2981 : mixedVector B (Sum.inr 2981) = Sparse.eval nodeValue2981 (mixedVector B) := by
    change mixedMoment B node2981 node2981Labels = _
    exact sound2981 B hB hF
  have h2984 : mixedVector B (Sum.inr 2984) = Sparse.eval nodeValue2984 (mixedVector B) := by
    change mixedMoment B node2984 node2984Labels = _
    exact sound2984 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h3800 : mixedVector B (Sum.inr 3800) = Sparse.eval nodeValue3800 (mixedVector B) := by
    change mixedMoment B node3800 node3800Labels = _
    exact sound3800 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm537, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2470, h2981, h2984, h3077, h3800, h4091, reducedSource451] using sourceEq537 B hB

theorem rowSound451 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row451 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck451, numericCheck451, reducedZero451 B hB hF, mul_zero]

theorem reducedZero455 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource455 (mixedVector B) = 0 := by
  have h2509 : mixedVector B (Sum.inr 2509) = Sparse.eval nodeValue2509 (mixedVector B) := by
    change mixedMoment B node2509 node2509Labels = _
    exact sound2509 B hB hF
  have h3493 : mixedVector B (Sum.inr 3493) = Sparse.eval nodeValue3493 (mixedVector B) := by
    change mixedMoment B node3493 node3493Labels = _
    exact sound3493 B hB hF
  have h3498 : mixedVector B (Sum.inr 3498) = Sparse.eval nodeValue3498 (mixedVector B) := by
    change mixedMoment B node3498 node3498Labels = _
    exact sound3498 B hB hF
  have h3547 : mixedVector B (Sum.inr 3547) = Sparse.eval nodeValue3547 (mixedVector B) := by
    change mixedMoment B node3547 node3547Labels = _
    exact sound3547 B hB hF
  have h3625 : mixedVector B (Sum.inr 3625) = Sparse.eval nodeValue3625 (mixedVector B) := by
    change mixedMoment B node3625 node3625Labels = _
    exact sound3625 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm541, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2509, h3493, h3498, h3547, h3625, h4084, reducedSource455] using sourceEq541 B hB

theorem rowSound455 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row455 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck455, numericCheck455, reducedZero455 B hB hF, mul_zero]

theorem reducedZero457 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource457 (mixedVector B) = 0 := by
  have h1250 : mixedVector B (Sum.inr 1250) = Sparse.eval nodeValue1250 (mixedVector B) := by
    change mixedMoment B node1250 node1250Labels = _
    exact sound1250 B hB hF
  have h1252 : mixedVector B (Sum.inr 1252) = Sparse.eval nodeValue1252 (mixedVector B) := by
    change mixedMoment B node1252 node1252Labels = _
    exact sound1252 B hB hF
  have h1253 : mixedVector B (Sum.inr 1253) = Sparse.eval nodeValue1253 (mixedVector B) := by
    change mixedMoment B node1253 node1253Labels = _
    exact sound1253 B hB hF
  have h1270 : mixedVector B (Sum.inr 1270) = Sparse.eval nodeValue1270 (mixedVector B) := by
    change mixedMoment B node1270 node1270Labels = _
    exact sound1270 B hB hF
  have h2754 : mixedVector B (Sum.inr 2754) = Sparse.eval nodeValue2754 (mixedVector B) := by
    change mixedMoment B node2754 node2754Labels = _
    exact sound2754 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm545, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1250, h1252, h1253, h1270, h2754, h4091, reducedSource457] using sourceEq545 B hB

theorem rowSound457 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row457 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck457, numericCheck457, reducedZero457 B hB hF, mul_zero]

theorem reducedZero458 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource458 (mixedVector B) = 0 := by
  have h1250 : mixedVector B (Sum.inr 1250) = Sparse.eval nodeValue1250 (mixedVector B) := by
    change mixedMoment B node1250 node1250Labels = _
    exact sound1250 B hB hF
  have h2625 : mixedVector B (Sum.inr 2625) = Sparse.eval nodeValue2625 (mixedVector B) := by
    change mixedMoment B node2625 node2625Labels = _
    exact sound2625 B hB hF
  have h2746 : mixedVector B (Sum.inr 2746) = Sparse.eval nodeValue2746 (mixedVector B) := by
    change mixedMoment B node2746 node2746Labels = _
    exact sound2746 B hB hF
  have h2750 : mixedVector B (Sum.inr 2750) = Sparse.eval nodeValue2750 (mixedVector B) := by
    change mixedMoment B node2750 node2750Labels = _
    exact sound2750 B hB hF
  have h2754 : mixedVector B (Sum.inr 2754) = Sparse.eval nodeValue2754 (mixedVector B) := by
    change mixedMoment B node2754 node2754Labels = _
    exact sound2754 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm546, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1250, h2625, h2746, h2750, h2754, h4091, reducedSource458] using sourceEq546 B hB

theorem rowSound458 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row458 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck458, numericCheck458, reducedZero458 B hB hF, mul_zero]

theorem reducedZero459 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource459 (mixedVector B) = 0 := by
  have h1421 : mixedVector B (Sum.inr 1421) = Sparse.eval nodeValue1421 (mixedVector B) := by
    change mixedMoment B node1421 node1421Labels = _
    exact sound1421 B hB hF
  have h2564 : mixedVector B (Sum.inr 2564) = Sparse.eval nodeValue2564 (mixedVector B) := by
    change mixedMoment B node2564 node2564Labels = _
    exact sound2564 B hB hF
  have h2573 : mixedVector B (Sum.inr 2573) = Sparse.eval nodeValue2573 (mixedVector B) := by
    change mixedMoment B node2573 node2573Labels = _
    exact sound2573 B hB hF
  have h2754 : mixedVector B (Sum.inr 2754) = Sparse.eval nodeValue2754 (mixedVector B) := by
    change mixedMoment B node2754 node2754Labels = _
    exact sound2754 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm547, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1421, h2564, h2573, h2754, h3037, h4091, reducedSource459] using sourceEq547 B hB

theorem rowSound459 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row459 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck459, numericCheck459, reducedZero459 B hB hF, mul_zero]

theorem reducedZero460 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource460 (mixedVector B) = 0 := by
  have h1270 : mixedVector B (Sum.inr 1270) = Sparse.eval nodeValue1270 (mixedVector B) := by
    change mixedMoment B node1270 node1270Labels = _
    exact sound1270 B hB hF
  have h2573 : mixedVector B (Sum.inr 2573) = Sparse.eval nodeValue2573 (mixedVector B) := by
    change mixedMoment B node2573 node2573Labels = _
    exact sound2573 B hB hF
  have h2641 : mixedVector B (Sum.inr 2641) = Sparse.eval nodeValue2641 (mixedVector B) := by
    change mixedMoment B node2641 node2641Labels = _
    exact sound2641 B hB hF
  have h2754 : mixedVector B (Sum.inr 2754) = Sparse.eval nodeValue2754 (mixedVector B) := by
    change mixedMoment B node2754 node2754Labels = _
    exact sound2754 B hB hF
  have h2764 : mixedVector B (Sum.inr 2764) = Sparse.eval nodeValue2764 (mixedVector B) := by
    change mixedMoment B node2764 node2764Labels = _
    exact sound2764 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm548, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1270, h2573, h2641, h2754, h2764, h4091, reducedSource460] using sourceEq548 B hB

theorem rowSound460 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row460 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck460, numericCheck460, reducedZero460 B hB hF, mul_zero]

theorem reducedZero461 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource461 (mixedVector B) = 0 := by
  have h4441 : mixedVector B (Sum.inr 4441) = Sparse.eval nodeValue4441 (mixedVector B) := by
    change mixedMoment B node4441 node4441Labels = _
    exact sound4441 B hB hF
  have h4442 : mixedVector B (Sum.inr 4442) = Sparse.eval nodeValue4442 (mixedVector B) := by
    change mixedMoment B node4442 node4442Labels = _
    exact sound4442 B hB hF
  have h4443 : mixedVector B (Sum.inr 4443) = Sparse.eval nodeValue4443 (mixedVector B) := by
    change mixedMoment B node4443 node4443Labels = _
    exact sound4443 B hB hF
  have h4462 : mixedVector B (Sum.inr 4462) = Sparse.eval nodeValue4462 (mixedVector B) := by
    change mixedMoment B node4462 node4462Labels = _
    exact sound4462 B hB hF
  have h4792 : mixedVector B (Sum.inr 4792) = Sparse.eval nodeValue4792 (mixedVector B) := by
    change mixedMoment B node4792 node4792Labels = _
    exact sound4792 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4890 : mixedVector B (Sum.inr 4890) = Sparse.eval nodeValue4890 (mixedVector B) := by
    change mixedMoment B node4890 node4890Labels = _
    exact sound4890 B hB hF
  have h5066 : mixedVector B (Sum.inr 5066) = Sparse.eval nodeValue5066 (mixedVector B) := by
    change mixedMoment B node5066 node5066Labels = _
    exact sound5066 B hB hF
  have h5077 : mixedVector B (Sum.inr 5077) = Sparse.eval nodeValue5077 (mixedVector B) := by
    change mixedMoment B node5077 node5077Labels = _
    exact sound5077 B hB hF
  have h5150 : mixedVector B (Sum.inr 5150) = Sparse.eval nodeValue5150 (mixedVector B) := by
    change mixedMoment B node5150 node5150Labels = _
    exact sound5150 B hB hF
  have h5151 : mixedVector B (Sum.inr 5151) = Sparse.eval nodeValue5151 (mixedVector B) := by
    change mixedMoment B node5151 node5151Labels = _
    exact sound5151 B hB hF
  have h5173 : mixedVector B (Sum.inr 5173) = Sparse.eval nodeValue5173 (mixedVector B) := by
    change mixedMoment B node5173 node5173Labels = _
    exact sound5173 B hB hF
  have h5256 : mixedVector B (Sum.inr 5256) = Sparse.eval nodeValue5256 (mixedVector B) := by
    change mixedMoment B node5256 node5256Labels = _
    exact sound5256 B hB hF
  have h5270 : mixedVector B (Sum.inr 5270) = Sparse.eval nodeValue5270 (mixedVector B) := by
    change mixedMoment B node5270 node5270Labels = _
    exact sound5270 B hB hF
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  have h5278 : mixedVector B (Sum.inr 5278) = Sparse.eval nodeValue5278 (mixedVector B) := by
    change mixedMoment B node5278 node5278Labels = _
    exact sound5278 B hB hF
  have h5279 : mixedVector B (Sum.inr 5279) = Sparse.eval nodeValue5279 (mixedVector B) := by
    change mixedMoment B node5279 node5279Labels = _
    exact sound5279 B hB hF
  have h5288 : mixedVector B (Sum.inr 5288) = Sparse.eval nodeValue5288 (mixedVector B) := by
    change mixedMoment B node5288 node5288Labels = _
    exact sound5288 B hB hF
  have h5290 : mixedVector B (Sum.inr 5290) = Sparse.eval nodeValue5290 (mixedVector B) := by
    change mixedMoment B node5290 node5290Labels = _
    exact sound5290 B hB hF
  have h5295 : mixedVector B (Sum.inr 5295) = Sparse.eval nodeValue5295 (mixedVector B) := by
    change mixedMoment B node5295 node5295Labels = _
    exact sound5295 B hB hF
  have h5306 : mixedVector B (Sum.inr 5306) = Sparse.eval nodeValue5306 (mixedVector B) := by
    change mixedMoment B node5306 node5306Labels = _
    exact sound5306 B hB hF
  simpa only [sourceForm549, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4441, h4442, h4443, h4462, h4792, h4807, h4890, h5066, h5077, h5150, h5151, h5173, h5256, h5270, h5271, h5278, h5279, h5288, h5290, h5295, h5306, reducedSource461] using sourceEq549 B hB

theorem rowSound461 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row461 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck461, numericCheck461, reducedZero461 B hB hF, mul_zero]

theorem sourceRowsAt448 : MixedData.sourceRows (448 : Fin 2425) =
    MixedData.row448 := by decide +kernel

theorem sourceRowsAt449 : MixedData.sourceRows (449 : Fin 2425) =
    MixedData.row449 := by decide +kernel

theorem sourceRowsAt450 : MixedData.sourceRows (450 : Fin 2425) =
    MixedData.row450 := by decide +kernel

theorem sourceRowsAt451 : MixedData.sourceRows (451 : Fin 2425) =
    MixedData.row451 := by decide +kernel

theorem sourceRowsAt452 : MixedData.sourceRows (452 : Fin 2425) =
    MixedData.row452 := by decide +kernel

theorem sourceRowsAt453 : MixedData.sourceRows (453 : Fin 2425) =
    MixedData.row453 := by decide +kernel

theorem sourceRowsAt454 : MixedData.sourceRows (454 : Fin 2425) =
    MixedData.row454 := by decide +kernel

theorem sourceRowsAt455 : MixedData.sourceRows (455 : Fin 2425) =
    MixedData.row455 := by decide +kernel

theorem sourceRowsAt456 : MixedData.sourceRows (456 : Fin 2425) =
    MixedData.row456 := by decide +kernel

theorem sourceRowsAt457 : MixedData.sourceRows (457 : Fin 2425) =
    MixedData.row457 := by decide +kernel

theorem sourceRowsAt458 : MixedData.sourceRows (458 : Fin 2425) =
    MixedData.row458 := by decide +kernel

theorem sourceRowsAt459 : MixedData.sourceRows (459 : Fin 2425) =
    MixedData.row459 := by decide +kernel

theorem sourceRowsAt460 : MixedData.sourceRows (460 : Fin 2425) =
    MixedData.row460 := by decide +kernel

theorem sourceRowsAt461 : MixedData.sourceRows (461 : Fin 2425) =
    MixedData.row461 := by decide +kernel

theorem sourceRowsAt462 : MixedData.sourceRows (462 : Fin 2425) =
    MixedData.row462 := by decide +kernel

theorem sourceRowsAt463 : MixedData.sourceRows (463 : Fin 2425) =
    MixedData.row463 := by decide +kernel

theorem chunkSound28_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 28) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 448 ∨ k.val = 449 ∨ k.val = 450 ∨ k.val = 451 ∨ k.val = 452 ∨ k.val = 453 ∨ k.val = 454 ∨ k.val = 455 ∨ k.val = 456 ∨ k.val = 457 ∨ k.val = 458 ∨ k.val = 459 ∨ k.val = 460 ∨ k.val = 461 ∨ k.val = 462 ∨ k.val = 463 := by omega
  rcases heq with h448 | h449 | h450 | h451 | h452 | h453 | h454 | h455 | h456 | h457 | h458 | h459 | h460 | h461 | h462 | h463
  · have he : k = (448 : Fin 2425) := Fin.ext h448
    subst k
    rw [sourceRowsAt448]
    exact rowSound448_e B hB hF
  · have he : k = (449 : Fin 2425) := Fin.ext h449
    subst k
    rw [sourceRowsAt449]
    exact rowSound449 B hB hF
  · have he : k = (450 : Fin 2425) := Fin.ext h450
    subst k
    rw [sourceRowsAt450]
    exact rowSound450 B hB hF
  · have he : k = (451 : Fin 2425) := Fin.ext h451
    subst k
    rw [sourceRowsAt451]
    exact rowSound451 B hB hF
  · have he : k = (452 : Fin 2425) := Fin.ext h452
    subst k
    rw [sourceRowsAt452]
    exact rowSound452_e B hB hF
  · have he : k = (453 : Fin 2425) := Fin.ext h453
    subst k
    rw [sourceRowsAt453]
    exact rowSound453_e B hB hF
  · have he : k = (454 : Fin 2425) := Fin.ext h454
    subst k
    rw [sourceRowsAt454]
    exact rowSound454_e B hB hF
  · have he : k = (455 : Fin 2425) := Fin.ext h455
    subst k
    rw [sourceRowsAt455]
    exact rowSound455 B hB hF
  · have he : k = (456 : Fin 2425) := Fin.ext h456
    subst k
    rw [sourceRowsAt456]
    exact rowSound456_e B hB hF
  · have he : k = (457 : Fin 2425) := Fin.ext h457
    subst k
    rw [sourceRowsAt457]
    exact rowSound457 B hB hF
  · have he : k = (458 : Fin 2425) := Fin.ext h458
    subst k
    rw [sourceRowsAt458]
    exact rowSound458 B hB hF
  · have he : k = (459 : Fin 2425) := Fin.ext h459
    subst k
    rw [sourceRowsAt459]
    exact rowSound459 B hB hF
  · have he : k = (460 : Fin 2425) := Fin.ext h460
    subst k
    rw [sourceRowsAt460]
    exact rowSound460 B hB hF
  · have he : k = (461 : Fin 2425) := Fin.ext h461
    subst k
    rw [sourceRowsAt461]
    exact rowSound461 B hB hF
  · have he : k = (462 : Fin 2425) := Fin.ext h462
    subst k
    rw [sourceRowsAt462]
    exact rowSound462_e B hB hF
  · have he : k = (463 : Fin 2425) := Fin.ext h463
    subst k
    rw [sourceRowsAt463]
    exact rowSound463_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28_e_oai
