-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound21_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:04:09.063948+00:00
-- url     : https://prove2.me/submissions/7b4c33c0-272f-45d8-b34d-979d134cb985

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E111
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E142
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E171
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound339_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound340_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound341_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound342_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound343_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound344_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound345_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw280 raw280Labels = mixedMoment B node2778 node2778Labels := by
  calc
    mixedMoment B raw280 raw280Labels = mixedMoment B raw280step0 raw280step0Labels := by
      have ha : raw280step0 = (fun i j => raw280 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw280step0 raw280; decide +kernel
      have hl : raw280step0Labels = raw280Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw280 raw280Labels permutation2 permutation5
    mixedMoment B raw280step0 raw280step0Labels = mixedMoment B raw280step1 raw280step1Labels := by
      have ha : raw280step1 = raw280step0 := by apply Matrix.ext; unfold raw280step1 raw280step0; decide +kernel
      have hl : raw280step0Labels = labelEmbedding1 ∘ raw280step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw280step0 raw280step0Labels raw280step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2778 node2778Labels := by rfl

theorem canonical281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw281 raw281Labels = mixedMoment B node270 node270Labels := by
  calc
    mixedMoment B raw281 raw281Labels = mixedMoment B raw281step0 raw281step0Labels := by
      have ha : raw281step0 = (fun i j => raw281 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw281step0 raw281; decide +kernel
      have hl : raw281step0Labels = raw281Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw281 raw281Labels permutation7 permutation4
    mixedMoment B raw281step0 raw281step0Labels = mixedMoment B raw281step1 raw281step1Labels := by
      have ha : raw281step1 = -raw281step0 := by apply Matrix.ext; change ∀ i j, raw281step1 i j = -(raw281step0 i j); unfold raw281step1 raw281step0; decide +kernel
      have hl : raw281step1Labels = raw281step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node270 node270Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw404 raw404Labels = mixedMoment B node3121 node3121Labels := by
  calc
    mixedMoment B raw404 raw404Labels = mixedMoment B raw404step0 raw404step0Labels := by
      have ha : raw404step0 = (fun i j => raw404 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw404step0 raw404; decide +kernel
      have hl : raw404step0Labels = raw404Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw404 raw404Labels permutation2 permutation5
    mixedMoment B raw404step0 raw404step0Labels = mixedMoment B raw404step1 raw404step1Labels := by
      have ha : raw404step1 = raw404step0 := by apply Matrix.ext; unfold raw404step1 raw404step0; decide +kernel
      have hl : raw404step0Labels = labelEmbedding1 ∘ raw404step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw404step0 raw404step0Labels raw404step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3121 node3121Labels := by rfl

theorem canonical405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw405 raw405Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw405 raw405Labels = mixedMoment B raw405step0 raw405step0Labels := by
      have ha : raw405step0 = (fun i j => raw405 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw405step0 raw405; decide +kernel
      have hl : raw405step0Labels = raw405Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw405 raw405Labels permutation2 permutation4
    _ = mixedMoment B node420 node420Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5760 raw5760Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw5760 raw5760Labels = mixedMoment B raw5760step0 raw5760step0Labels := by
      have hz : ∀ j, raw5760 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5760step0 = (fun i j => raw5760 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5760step0 raw5760; decide +kernel
      have hl : raw5760step0Labels = raw5760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5760 raw5760Labels permutation265 hz
    mixedMoment B raw5760step0 raw5760step0Labels = mixedMoment B raw5760step1 raw5760step1Labels := by
      have ha : raw5760step1 = (fun i j => raw5760step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5760step1 raw5760step0; decide +kernel
      have hl : raw5760step1Labels = raw5760step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5760step0 raw5760step0Labels permutation50 permutation4
    mixedMoment B raw5760step1 raw5760step1Labels = mixedMoment B raw5760step2 raw5760step2Labels := by
      have ha : raw5760step2 = -raw5760step1 := by apply Matrix.ext; change ∀ i j, raw5760step2 i j = -(raw5760step1 i j); unfold raw5760step2 raw5760step1; decide +kernel
      have hl : raw5760step2Labels = raw5760step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2277 node2277Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6104 raw6104Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw6104 raw6104Labels = mixedMoment B raw6104step0 raw6104step0Labels := by
      have hz : ∀ j, raw6104 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6104step0 = (fun i j => raw6104 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6104step0 raw6104; decide +kernel
      have hl : raw6104step0Labels = raw6104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6104 raw6104Labels permutation434 hz
    mixedMoment B raw6104step0 raw6104step0Labels = mixedMoment B raw6104step1 raw6104step1Labels := by
      have hz : ∀ j, raw6104step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6104step1 = (fun i j => raw6104step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6104step1 raw6104step0; decide +kernel
      have hl : raw6104step1Labels = raw6104step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6104step0 raw6104step0Labels permutation80 hz
    mixedMoment B raw6104step1 raw6104step1Labels = mixedMoment B raw6104step2 raw6104step2Labels := by
      have ha : raw6104step2 = (fun i j => raw6104step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6104step2 raw6104step1; decide +kernel
      have hl : raw6104step2Labels = raw6104step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6104step1 raw6104step1Labels permutation10 permutation2
    mixedMoment B raw6104step2 raw6104step2Labels = mixedMoment B raw6104step3 raw6104step3Labels := by
      have ha : raw6104step3 = -raw6104step2 := by apply Matrix.ext; change ∀ i j, raw6104step3 i j = -(raw6104step2 i j); unfold raw6104step3 raw6104step2; decide +kernel
      have hl : raw6104step3Labels = raw6104step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3582 node3582Labels := by rfl

theorem canonical6121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6121 raw6121Labels = mixedMoment B node3633 node3633Labels := by
  calc
    mixedMoment B raw6121 raw6121Labels = mixedMoment B raw6121step0 raw6121step0Labels := by
      have hz : ∀ j, raw6121 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6121step0 = (fun i j => raw6121 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6121step0 raw6121; decide +kernel
      have hl : raw6121step0Labels = raw6121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6121 raw6121Labels permutation434 hz
    mixedMoment B raw6121step0 raw6121step0Labels = mixedMoment B raw6121step1 raw6121step1Labels := by
      have hz : ∀ j, raw6121step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6121step1 = (fun i j => raw6121step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6121step1 raw6121step0; decide +kernel
      have hl : raw6121step1Labels = raw6121step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6121step0 raw6121step0Labels permutation80 hz
    mixedMoment B raw6121step1 raw6121step1Labels = mixedMoment B raw6121step2 raw6121step2Labels := by
      have hz : ∀ j, raw6121step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw6121step2 = (fun i j => raw6121step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw6121step2 raw6121step1; decide +kernel
      have hl : raw6121step2Labels = raw6121step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6121step1 raw6121step1Labels permutation14 hz
    mixedMoment B raw6121step2 raw6121step2Labels = mixedMoment B raw6121step3 raw6121step3Labels := by
      have ha : raw6121step3 = (fun i j => raw6121step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6121step3 raw6121step2; decide +kernel
      have hl : raw6121step3Labels = raw6121step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6121step2 raw6121step2Labels permutation3 permutation4
    mixedMoment B raw6121step3 raw6121step3Labels = mixedMoment B raw6121step4 raw6121step4Labels := by
      have ha : raw6121step4 = -raw6121step3 := by apply Matrix.ext; change ∀ i j, raw6121step4 i j = -(raw6121step3 i j); unfold raw6121step4 raw6121step3; decide +kernel
      have hl : raw6121step4Labels = raw6121step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3633 node3633Labels := by rfl

theorem canonical6123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6123 raw6123Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw6123 raw6123Labels = mixedMoment B raw6123step0 raw6123step0Labels := by
      have hz : ∀ j, raw6123 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6123step0 = (fun i j => raw6123 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6123step0 raw6123; decide +kernel
      have hl : raw6123step0Labels = raw6123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6123 raw6123Labels permutation434 hz
    mixedMoment B raw6123step0 raw6123step0Labels = mixedMoment B raw6123step1 raw6123step1Labels := by
      have hz : ∀ j, raw6123step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6123step1 = (fun i j => raw6123step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6123step1 raw6123step0; decide +kernel
      have hl : raw6123step1Labels = raw6123step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6123step0 raw6123step0Labels permutation80 hz
    mixedMoment B raw6123step1 raw6123step1Labels = mixedMoment B raw6123step2 raw6123step2Labels := by
      have ha : raw6123step2 = (fun i j => raw6123step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6123step2 raw6123step1; decide +kernel
      have hl : raw6123step2Labels = raw6123step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6123step1 raw6123step1Labels permutation9 permutation4
    mixedMoment B raw6123step2 raw6123step2Labels = mixedMoment B raw6123step3 raw6123step3Labels := by
      have ha : raw6123step3 = -raw6123step2 := by apply Matrix.ext; change ∀ i j, raw6123step3 i j = -(raw6123step2 i j); unfold raw6123step3 raw6123step2; decide +kernel
      have hl : raw6123step3Labels = raw6123step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3548 node3548Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6437 raw6437Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw6437 raw6437Labels = mixedMoment B raw6437step0 raw6437step0Labels := by
      have hz : ∀ j, raw6437 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6437step0 = (fun i j => raw6437 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6437step0 raw6437; decide +kernel
      have hl : raw6437step0Labels = raw6437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6437 raw6437Labels permutation346 hz
    mixedMoment B raw6437step0 raw6437step0Labels = mixedMoment B raw6437step1 raw6437step1Labels := by
      have ha : raw6437step1 = (fun i j => raw6437step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6437step1 raw6437step0; decide +kernel
      have hl : raw6437step1Labels = raw6437step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6437step0 raw6437step0Labels permutation40 permutation2
    mixedMoment B raw6437step1 raw6437step1Labels = mixedMoment B raw6437step2 raw6437step2Labels := by
      have ha : raw6437step2 = -raw6437step1 := by apply Matrix.ext; change ∀ i j, raw6437step2 i j = -(raw6437step1 i j); unfold raw6437step2 raw6437step1; decide +kernel
      have hl : raw6437step2Labels = raw6437step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical6440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6440 raw6440Labels = mixedMoment B node2033 node2033Labels := by
  calc
    mixedMoment B raw6440 raw6440Labels = mixedMoment B raw6440step0 raw6440step0Labels := by
      have ha : raw6440step0 = (fun i j => raw6440 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6440step0 raw6440; decide +kernel
      have hl : raw6440step0Labels = raw6440Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6440 raw6440Labels permutation170 permutation4
    mixedMoment B raw6440step0 raw6440step0Labels = mixedMoment B raw6440step1 raw6440step1Labels := by
      have ha : raw6440step1 = -raw6440step0 := by apply Matrix.ext; change ∀ i j, raw6440step1 i j = -(raw6440step0 i j); unfold raw6440step1 raw6440step0; decide +kernel
      have hl : raw6440step1Labels = raw6440step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2033 node2033Labels := by rfl

theorem canonical6445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6445 raw6445Labels = mixedMoment B node3632 node3632Labels := by
  calc
    mixedMoment B raw6445 raw6445Labels = mixedMoment B raw6445step0 raw6445step0Labels := by
      have hz : ∀ j, raw6445 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6445step0 = (fun i j => raw6445 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6445step0 raw6445; decide +kernel
      have hl : raw6445step0Labels = raw6445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6445 raw6445Labels permutation346 hz
    mixedMoment B raw6445step0 raw6445step0Labels = mixedMoment B raw6445step1 raw6445step1Labels := by
      have hz : ∀ j, raw6445step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6445step1 = (fun i j => raw6445step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6445step1 raw6445step0; decide +kernel
      have hl : raw6445step1Labels = raw6445step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6445step0 raw6445step0Labels permutation56 hz
    mixedMoment B raw6445step1 raw6445step1Labels = mixedMoment B raw6445step2 raw6445step2Labels := by
      have ha : raw6445step2 = (fun i j => raw6445step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6445step2 raw6445step1; decide +kernel
      have hl : raw6445step2Labels = raw6445step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6445step1 raw6445step1Labels permutation12 permutation4
    mixedMoment B raw6445step2 raw6445step2Labels = mixedMoment B raw6445step3 raw6445step3Labels := by
      have ha : raw6445step3 = -raw6445step2 := by apply Matrix.ext; change ∀ i j, raw6445step3 i j = -(raw6445step2 i j); unfold raw6445step3 raw6445step2; decide +kernel
      have hl : raw6445step3Labels = raw6445step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3632 node3632Labels := by rfl

theorem canonical6450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6450 raw6450Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw6450 raw6450Labels = mixedMoment B raw6450step0 raw6450step0Labels := by
      have ha : raw6450step0 = (fun i j => raw6450 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6450step0 raw6450; decide +kernel
      have hl : raw6450step0Labels = raw6450Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6450 raw6450Labels permutation170 permutation4
    mixedMoment B raw6450step0 raw6450step0Labels = mixedMoment B raw6450step1 raw6450step1Labels := by
      have ha : raw6450step1 = -raw6450step0 := by apply Matrix.ext; change ∀ i j, raw6450step1 i j = -(raw6450step0 i j); unfold raw6450step1 raw6450step0; decide +kernel
      have hl : raw6450step1Labels = raw6450step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3539 node3539Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7096 raw7096Labels = mixedMoment B node2034 node2034Labels := by
  calc
    mixedMoment B raw7096 raw7096Labels = mixedMoment B raw7096step0 raw7096step0Labels := by
      have ha : raw7096step0 = (fun i j => raw7096 (permutation171 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7096step0 raw7096; decide +kernel
      have hl : raw7096step0Labels = raw7096Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7096 raw7096Labels permutation171 permutation4
    mixedMoment B raw7096step0 raw7096step0Labels = mixedMoment B raw7096step1 raw7096step1Labels := by
      have ha : raw7096step1 = -raw7096step0 := by apply Matrix.ext; change ∀ i j, raw7096step1 i j = -(raw7096step0 i j); unfold raw7096step1 raw7096step0; decide +kernel
      have hl : raw7096step1Labels = raw7096step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2034 node2034Labels := by rfl

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

theorem canonical7280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7280 raw7280Labels = mixedMoment B node2051 node2051Labels := by
  calc
    mixedMoment B raw7280 raw7280Labels = mixedMoment B raw7280step0 raw7280step0Labels := by
      have ha : raw7280step0 = (fun i j => raw7280 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7280step0 raw7280; decide +kernel
      have hl : raw7280step0Labels = raw7280Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7280 raw7280Labels permutation152 permutation4
    mixedMoment B raw7280step0 raw7280step0Labels = mixedMoment B raw7280step1 raw7280step1Labels := by
      have ha : raw7280step1 = -raw7280step0 := by apply Matrix.ext; change ∀ i j, raw7280step1 i j = -(raw7280step0 i j); unfold raw7280step1 raw7280step0; decide +kernel
      have hl : raw7280step1Labels = raw7280step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2051 node2051Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7551 raw7551Labels = mixedMoment B node3488 node3488Labels := by
  calc
    mixedMoment B raw7551 raw7551Labels = mixedMoment B raw7551step0 raw7551step0Labels := by
      have ha : raw7551step0 = (fun i j => raw7551 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7551step0 raw7551; decide +kernel
      have hl : raw7551step0Labels = raw7551Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7551 raw7551Labels permutation184 permutation2
    mixedMoment B raw7551step0 raw7551step0Labels = mixedMoment B raw7551step1 raw7551step1Labels := by
      have ha : raw7551step1 = -raw7551step0 := by apply Matrix.ext; change ∀ i j, raw7551step1 i j = -(raw7551step0 i j); unfold raw7551step1 raw7551step0; decide +kernel
      have hl : raw7551step1Labels = raw7551step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3488 node3488Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7552 raw7552Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw7552 raw7552Labels = mixedMoment B raw7552step0 raw7552step0Labels := by
      have hz : ∀ j, raw7552 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7552step0 = (fun i j => raw7552 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7552step0 raw7552; decide +kernel
      have hl : raw7552step0Labels = raw7552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7552 raw7552Labels permutation434 hz
    mixedMoment B raw7552step0 raw7552step0Labels = mixedMoment B raw7552step1 raw7552step1Labels := by
      have ha : raw7552step1 = (fun i j => raw7552step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7552step1 raw7552step0; decide +kernel
      have hl : raw7552step1Labels = raw7552step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7552step0 raw7552step0Labels permutation40 permutation2
    mixedMoment B raw7552step1 raw7552step1Labels = mixedMoment B raw7552step2 raw7552step2Labels := by
      have ha : raw7552step2 = -raw7552step1 := by apply Matrix.ext; change ∀ i j, raw7552step2 i j = -(raw7552step1 i j); unfold raw7552step2 raw7552step1; decide +kernel
      have hl : raw7552step2Labels = raw7552step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical7553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7553 raw7553Labels = mixedMoment B node2552 node2552Labels := by
  calc
    mixedMoment B raw7553 raw7553Labels = mixedMoment B raw7553step0 raw7553step0Labels := by
      have ha : raw7553step0 = (fun i j => raw7553 (permutation620 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7553step0 raw7553; decide +kernel
      have hl : raw7553step0Labels = raw7553Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7553 raw7553Labels permutation620 permutation2
    _ = mixedMoment B node2552 node2552Labels := by rfl

theorem canonical7554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7554 raw7554Labels = mixedMoment B node2034 node2034Labels := by
  calc
    mixedMoment B raw7554 raw7554Labels = mixedMoment B raw7554step0 raw7554step0Labels := by
      have ha : raw7554step0 = (fun i j => raw7554 (permutation173 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7554step0 raw7554; decide +kernel
      have hl : raw7554step0Labels = raw7554Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7554 raw7554Labels permutation173 permutation4
    mixedMoment B raw7554step0 raw7554step0Labels = mixedMoment B raw7554step1 raw7554step1Labels := by
      have ha : raw7554step1 = -raw7554step0 := by apply Matrix.ext; change ∀ i j, raw7554step1 i j = -(raw7554step0 i j); unfold raw7554step1 raw7554step0; decide +kernel
      have hl : raw7554step1Labels = raw7554step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2034 node2034Labels := by rfl

theorem canonical7555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7555 raw7555Labels = mixedMoment B node3632 node3632Labels := by
  calc
    mixedMoment B raw7555 raw7555Labels = mixedMoment B raw7555step0 raw7555step0Labels := by
      have hz : ∀ j, raw7555 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7555step0 = (fun i j => raw7555 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7555step0 raw7555; decide +kernel
      have hl : raw7555step0Labels = raw7555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7555 raw7555Labels permutation434 hz
    mixedMoment B raw7555step0 raw7555step0Labels = mixedMoment B raw7555step1 raw7555step1Labels := by
      have hz : ∀ j, raw7555step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7555step1 = (fun i j => raw7555step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7555step1 raw7555step0; decide +kernel
      have hl : raw7555step1Labels = raw7555step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7555step0 raw7555step0Labels permutation56 hz
    mixedMoment B raw7555step1 raw7555step1Labels = mixedMoment B raw7555step2 raw7555step2Labels := by
      have ha : raw7555step2 = (fun i j => raw7555step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7555step2 raw7555step1; decide +kernel
      have hl : raw7555step2Labels = raw7555step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7555step1 raw7555step1Labels permutation12 permutation4
    mixedMoment B raw7555step2 raw7555step2Labels = mixedMoment B raw7555step3 raw7555step3Labels := by
      have ha : raw7555step3 = -raw7555step2 := by apply Matrix.ext; change ∀ i j, raw7555step3 i j = -(raw7555step2 i j); unfold raw7555step3 raw7555step2; decide +kernel
      have hl : raw7555step3Labels = raw7555step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3632 node3632Labels := by rfl

theorem canonical7556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7556 raw7556Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw7556 raw7556Labels = mixedMoment B raw7556step0 raw7556step0Labels := by
      have hz : ∀ j, raw7556 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7556step0 = (fun i j => raw7556 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7556step0 raw7556; decide +kernel
      have hl : raw7556step0Labels = raw7556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7556 raw7556Labels permutation265 hz
    mixedMoment B raw7556step0 raw7556step0Labels = mixedMoment B raw7556step1 raw7556step1Labels := by
      have ha : raw7556step1 = (fun i j => raw7556step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7556step1 raw7556step0; decide +kernel
      have hl : raw7556step1Labels = raw7556step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7556step0 raw7556step0Labels permutation149 permutation2
    _ = mixedMoment B node2738 node2738Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7692 raw7692Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw7692 raw7692Labels = mixedMoment B raw7692step0 raw7692step0Labels := by
      have hz : ∀ j, raw7692 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7692step0 = (fun i j => raw7692 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7692step0 raw7692; decide +kernel
      have hl : raw7692step0Labels = raw7692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7692 raw7692Labels permutation434 hz
    mixedMoment B raw7692step0 raw7692step0Labels = mixedMoment B raw7692step1 raw7692step1Labels := by
      have hz : ∀ j, raw7692step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7692step1 = (fun i j => raw7692step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7692step1 raw7692step0; decide +kernel
      have hl : raw7692step1Labels = raw7692step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7692step0 raw7692step0Labels permutation56 hz
    mixedMoment B raw7692step1 raw7692step1Labels = mixedMoment B raw7692step2 raw7692step2Labels := by
      have ha : raw7692step2 = (fun i j => raw7692step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7692step2 raw7692step1; decide +kernel
      have hl : raw7692step2Labels = raw7692step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7692step1 raw7692step1Labels permutation10 permutation2
    mixedMoment B raw7692step2 raw7692step2Labels = mixedMoment B raw7692step3 raw7692step3Labels := by
      have ha : raw7692step3 = -raw7692step2 := by apply Matrix.ext; change ∀ i j, raw7692step3 i j = -(raw7692step2 i j); unfold raw7692step3 raw7692step2; decide +kernel
      have hl : raw7692step3Labels = raw7692step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3582 node3582Labels := by rfl

theorem canonical7693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7693 raw7693Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw7693 raw7693Labels = mixedMoment B raw7693step0 raw7693step0Labels := by
      have hz : ∀ j, raw7693 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7693step0 = (fun i j => raw7693 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7693step0 raw7693; decide +kernel
      have hl : raw7693step0Labels = raw7693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7693 raw7693Labels permutation346 hz
    mixedMoment B raw7693step0 raw7693step0Labels = mixedMoment B raw7693step1 raw7693step1Labels := by
      have hz : ∀ j, raw7693step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7693step1 = (fun i j => raw7693step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7693step1 raw7693step0; decide +kernel
      have hl : raw7693step1Labels = raw7693step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7693step0 raw7693step0Labels permutation56 hz
    mixedMoment B raw7693step1 raw7693step1Labels = mixedMoment B raw7693step2 raw7693step2Labels := by
      have ha : raw7693step2 = (fun i j => raw7693step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7693step2 raw7693step1; decide +kernel
      have hl : raw7693step2Labels = raw7693step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7693step1 raw7693step1Labels permutation10 permutation2
    mixedMoment B raw7693step2 raw7693step2Labels = mixedMoment B raw7693step3 raw7693step3Labels := by
      have ha : raw7693step3 = -raw7693step2 := by apply Matrix.ext; change ∀ i j, raw7693step3 i j = -(raw7693step2 i j); unfold raw7693step3 raw7693step2; decide +kernel
      have hl : raw7693step3Labels = raw7693step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3582 node3582Labels := by rfl

theorem canonical7694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7694 raw7694Labels = mixedMoment B node3629 node3629Labels := by
  calc
    mixedMoment B raw7694 raw7694Labels = mixedMoment B raw7694step0 raw7694step0Labels := by
      have hz : ∀ j, raw7694 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7694step0 = (fun i j => raw7694 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7694step0 raw7694; decide +kernel
      have hl : raw7694step0Labels = raw7694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7694 raw7694Labels permutation434 hz
    mixedMoment B raw7694step0 raw7694step0Labels = mixedMoment B raw7694step1 raw7694step1Labels := by
      have hz : ∀ j, raw7694step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7694step1 = (fun i j => raw7694step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7694step1 raw7694step0; decide +kernel
      have hl : raw7694step1Labels = raw7694step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7694step0 raw7694step0Labels permutation80 hz
    mixedMoment B raw7694step1 raw7694step1Labels = mixedMoment B raw7694step2 raw7694step2Labels := by
      have hz : ∀ j, raw7694step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7694step2 = (fun i j => raw7694step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7694step2 raw7694step1; decide +kernel
      have hl : raw7694step2Labels = raw7694step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7694step1 raw7694step1Labels permutation14 hz
    mixedMoment B raw7694step2 raw7694step2Labels = mixedMoment B raw7694step3 raw7694step3Labels := by
      have ha : raw7694step3 = -raw7694step2 := by apply Matrix.ext; change ∀ i j, raw7694step3 i j = -(raw7694step2 i j); unfold raw7694step3 raw7694step2; decide +kernel
      have hl : raw7694step3Labels = raw7694step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3629 node3629Labels := by rfl

theorem canonical7695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7695 raw7695Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw7695 raw7695Labels = mixedMoment B raw7695step0 raw7695step0Labels := by
      have hz : ∀ j, raw7695 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7695step0 = (fun i j => raw7695 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7695step0 raw7695; decide +kernel
      have hl : raw7695step0Labels = raw7695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7695 raw7695Labels permutation434 hz
    mixedMoment B raw7695step0 raw7695step0Labels = mixedMoment B raw7695step1 raw7695step1Labels := by
      have hz : ∀ j, raw7695step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7695step1 = (fun i j => raw7695step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7695step1 raw7695step0; decide +kernel
      have hl : raw7695step1Labels = raw7695step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7695step0 raw7695step0Labels permutation80 hz
    mixedMoment B raw7695step1 raw7695step1Labels = mixedMoment B raw7695step2 raw7695step2Labels := by
      have hz : ∀ j, raw7695step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7695step2 = (fun i j => raw7695step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7695step2 raw7695step1; decide +kernel
      have hl : raw7695step2Labels = raw7695step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7695step1 raw7695step1Labels permutation14 hz
    mixedMoment B raw7695step2 raw7695step2Labels = mixedMoment B raw7695step3 raw7695step3Labels := by
      have ha : raw7695step3 = (fun i j => raw7695step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7695step3 raw7695step2; decide +kernel
      have hl : raw7695step3Labels = raw7695step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7695step2 raw7695step2Labels permutation7 permutation2
    _ = mixedMoment B node2783 node2783Labels := by rfl

theorem canonical7696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7696 raw7696Labels = mixedMoment B node3632 node3632Labels := by
  calc
    mixedMoment B raw7696 raw7696Labels = mixedMoment B raw7696step0 raw7696step0Labels := by
      have hz : ∀ j, raw7696 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7696step0 = (fun i j => raw7696 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7696step0 raw7696; decide +kernel
      have hl : raw7696step0Labels = raw7696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7696 raw7696Labels permutation434 hz
    mixedMoment B raw7696step0 raw7696step0Labels = mixedMoment B raw7696step1 raw7696step1Labels := by
      have hz : ∀ j, raw7696step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7696step1 = (fun i j => raw7696step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7696step1 raw7696step0; decide +kernel
      have hl : raw7696step1Labels = raw7696step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7696step0 raw7696step0Labels permutation80 hz
    mixedMoment B raw7696step1 raw7696step1Labels = mixedMoment B raw7696step2 raw7696step2Labels := by
      have ha : raw7696step2 = (fun i j => raw7696step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7696step2 raw7696step1; decide +kernel
      have hl : raw7696step2Labels = raw7696step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7696step1 raw7696step1Labels permutation12 permutation4
    mixedMoment B raw7696step2 raw7696step2Labels = mixedMoment B raw7696step3 raw7696step3Labels := by
      have ha : raw7696step3 = -raw7696step2 := by apply Matrix.ext; change ∀ i j, raw7696step3 i j = -(raw7696step2 i j); unfold raw7696step3 raw7696step2; decide +kernel
      have hl : raw7696step3Labels = raw7696step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3632 node3632Labels := by rfl

theorem canonical7697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7697 raw7697Labels = mixedMoment B node3635 node3635Labels := by
  calc
    mixedMoment B raw7697 raw7697Labels = mixedMoment B raw7697step0 raw7697step0Labels := by
      have hz : ∀ j, raw7697 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7697step0 = (fun i j => raw7697 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7697step0 raw7697; decide +kernel
      have hl : raw7697step0Labels = raw7697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7697 raw7697Labels permutation434 hz
    mixedMoment B raw7697step0 raw7697step0Labels = mixedMoment B raw7697step1 raw7697step1Labels := by
      have hz : ∀ j, raw7697step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7697step1 = (fun i j => raw7697step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7697step1 raw7697step0; decide +kernel
      have hl : raw7697step1Labels = raw7697step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7697step0 raw7697step0Labels permutation80 hz
    mixedMoment B raw7697step1 raw7697step1Labels = mixedMoment B raw7697step2 raw7697step2Labels := by
      have hz : ∀ j, raw7697step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7697step2 = (fun i j => raw7697step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7697step2 raw7697step1; decide +kernel
      have hl : raw7697step2Labels = raw7697step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7697step1 raw7697step1Labels permutation14 hz
    mixedMoment B raw7697step2 raw7697step2Labels = mixedMoment B raw7697step3 raw7697step3Labels := by
      have ha : raw7697step3 = (fun i j => raw7697step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7697step3 raw7697step2; decide +kernel
      have hl : raw7697step3Labels = raw7697step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7697step2 raw7697step2Labels permutation2 permutation4
    mixedMoment B raw7697step3 raw7697step3Labels = mixedMoment B raw7697step4 raw7697step4Labels := by
      have ha : raw7697step4 = -raw7697step3 := by apply Matrix.ext; change ∀ i j, raw7697step4 i j = -(raw7697step3 i j); unfold raw7697step4 raw7697step3; decide +kernel
      have hl : raw7697step4Labels = raw7697step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3635 node3635Labels := by rfl

theorem canonical7698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7698 raw7698Labels = mixedMoment B node2293 node2293Labels := by
  calc
    mixedMoment B raw7698 raw7698Labels = mixedMoment B raw7698step0 raw7698step0Labels := by
      have hz : ∀ j, raw7698 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7698step0 = (fun i j => raw7698 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7698step0 raw7698; decide +kernel
      have hl : raw7698step0Labels = raw7698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7698 raw7698Labels permutation434 hz
    mixedMoment B raw7698step0 raw7698step0Labels = mixedMoment B raw7698step1 raw7698step1Labels := by
      have hz : ∀ j, raw7698step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7698step1 = (fun i j => raw7698step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7698step1 raw7698step0; decide +kernel
      have hl : raw7698step1Labels = raw7698step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7698step0 raw7698step0Labels permutation80 hz
    mixedMoment B raw7698step1 raw7698step1Labels = mixedMoment B raw7698step2 raw7698step2Labels := by
      have hz : ∀ j, raw7698step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7698step2 = (fun i j => raw7698step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7698step2 raw7698step1; decide +kernel
      have hl : raw7698step2Labels = raw7698step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7698step1 raw7698step1Labels permutation14 hz
    mixedMoment B raw7698step2 raw7698step2Labels = mixedMoment B raw7698step3 raw7698step3Labels := by
      have ha : raw7698step3 = (fun i j => raw7698step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7698step3 raw7698step2; decide +kernel
      have hl : raw7698step3Labels = raw7698step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7698step2 raw7698step2Labels permutation3 permutation4
    mixedMoment B raw7698step3 raw7698step3Labels = mixedMoment B raw7698step4 raw7698step4Labels := by
      have ha : raw7698step4 = -raw7698step3 := by apply Matrix.ext; change ∀ i j, raw7698step4 i j = -(raw7698step3 i j); unfold raw7698step4 raw7698step3; decide +kernel
      have hl : raw7698step4Labels = raw7698step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2293 node2293Labels := by rfl

theorem canonical7699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7699 raw7699Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw7699 raw7699Labels = mixedMoment B raw7699step0 raw7699step0Labels := by
      have hz : ∀ j, raw7699 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7699step0 = (fun i j => raw7699 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7699step0 raw7699; decide +kernel
      have hl : raw7699step0Labels = raw7699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7699 raw7699Labels permutation434 hz
    mixedMoment B raw7699step0 raw7699step0Labels = mixedMoment B raw7699step1 raw7699step1Labels := by
      have hz : ∀ j, raw7699step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7699step1 = (fun i j => raw7699step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7699step1 raw7699step0; decide +kernel
      have hl : raw7699step1Labels = raw7699step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7699step0 raw7699step0Labels permutation56 hz
    mixedMoment B raw7699step1 raw7699step1Labels = mixedMoment B raw7699step2 raw7699step2Labels := by
      have ha : raw7699step2 = (fun i j => raw7699step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7699step2 raw7699step1; decide +kernel
      have hl : raw7699step2Labels = raw7699step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7699step1 raw7699step1Labels permutation9 permutation4
    mixedMoment B raw7699step2 raw7699step2Labels = mixedMoment B raw7699step3 raw7699step3Labels := by
      have ha : raw7699step3 = -raw7699step2 := by apply Matrix.ext; change ∀ i j, raw7699step3 i j = -(raw7699step2 i j); unfold raw7699step3 raw7699step2; decide +kernel
      have hl : raw7699step3Labels = raw7699step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3548 node3548Labels := by rfl

theorem canonical7700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7700 raw7700Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw7700 raw7700Labels = mixedMoment B raw7700step0 raw7700step0Labels := by
      have hz : ∀ j, raw7700 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7700step0 = (fun i j => raw7700 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7700step0 raw7700; decide +kernel
      have hl : raw7700step0Labels = raw7700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7700 raw7700Labels permutation346 hz
    mixedMoment B raw7700step0 raw7700step0Labels = mixedMoment B raw7700step1 raw7700step1Labels := by
      have hz : ∀ j, raw7700step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7700step1 = (fun i j => raw7700step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7700step1 raw7700step0; decide +kernel
      have hl : raw7700step1Labels = raw7700step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7700step0 raw7700step0Labels permutation56 hz
    mixedMoment B raw7700step1 raw7700step1Labels = mixedMoment B raw7700step2 raw7700step2Labels := by
      have ha : raw7700step2 = (fun i j => raw7700step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7700step2 raw7700step1; decide +kernel
      have hl : raw7700step2Labels = raw7700step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7700step1 raw7700step1Labels permutation9 permutation4
    mixedMoment B raw7700step2 raw7700step2Labels = mixedMoment B raw7700step3 raw7700step3Labels := by
      have ha : raw7700step3 = -raw7700step2 := by apply Matrix.ext; change ∀ i j, raw7700step3 i j = -(raw7700step2 i j); unfold raw7700step3 raw7700step2; decide +kernel
      have hl : raw7700step3Labels = raw7700step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3548 node3548Labels := by rfl

theorem canonical7761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7761 raw7761Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw7761 raw7761Labels = mixedMoment B raw7761step0 raw7761step0Labels := by
      have hz : ∀ j, raw7761 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7761step0 = (fun i j => raw7761 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7761step0 raw7761; decide +kernel
      have hl : raw7761step0Labels = raw7761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7761 raw7761Labels permutation434 hz
    mixedMoment B raw7761step0 raw7761step0Labels = mixedMoment B raw7761step1 raw7761step1Labels := by
      have hz : ∀ j, raw7761step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7761step1 = (fun i j => raw7761step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7761step1 raw7761step0; decide +kernel
      have hl : raw7761step1Labels = raw7761step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7761step0 raw7761step0Labels permutation80 hz
    mixedMoment B raw7761step1 raw7761step1Labels = mixedMoment B raw7761step2 raw7761step2Labels := by
      have ha : raw7761step2 = (fun i j => raw7761step1 (permutation26 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7761step2 raw7761step1; decide +kernel
      have hl : raw7761step2Labels = raw7761step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7761step1 raw7761step1Labels permutation26 permutation5
    mixedMoment B raw7761step2 raw7761step2Labels = mixedMoment B raw7761step3 raw7761step3Labels := by
      have ha : raw7761step3 = raw7761step2 := by apply Matrix.ext; unfold raw7761step3 raw7761step2; decide +kernel
      have hl : raw7761step2Labels = labelEmbedding1 ∘ raw7761step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7761step2 raw7761step2Labels raw7761step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2777 node2777Labels := by rfl

theorem canonical7762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7762 raw7762Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw7762 raw7762Labels = mixedMoment B raw7762step0 raw7762step0Labels := by
      have hz : ∀ j, raw7762 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7762step0 = (fun i j => raw7762 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7762step0 raw7762; decide +kernel
      have hl : raw7762step0Labels = raw7762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7762 raw7762Labels permutation434 hz
    mixedMoment B raw7762step0 raw7762step0Labels = mixedMoment B raw7762step1 raw7762step1Labels := by
      have hz : ∀ j, raw7762step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7762step1 = (fun i j => raw7762step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7762step1 raw7762step0; decide +kernel
      have hl : raw7762step1Labels = raw7762step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7762step0 raw7762step0Labels permutation56 hz
    mixedMoment B raw7762step1 raw7762step1Labels = mixedMoment B raw7762step2 raw7762step2Labels := by
      have ha : raw7762step2 = (fun i j => raw7762step1 (permutation26 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7762step2 raw7762step1; decide +kernel
      have hl : raw7762step2Labels = raw7762step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7762step1 raw7762step1Labels permutation26 permutation5
    mixedMoment B raw7762step2 raw7762step2Labels = mixedMoment B raw7762step3 raw7762step3Labels := by
      have ha : raw7762step3 = raw7762step2 := by apply Matrix.ext; unfold raw7762step3 raw7762step2; decide +kernel
      have hl : raw7762step2Labels = labelEmbedding1 ∘ raw7762step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7762step2 raw7762step2Labels raw7762step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2777 node2777Labels := by rfl

theorem canonical7763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7763 raw7763Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw7763 raw7763Labels = mixedMoment B raw7763step0 raw7763step0Labels := by
      have hz : ∀ j, raw7763 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7763step0 = (fun i j => raw7763 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7763step0 raw7763; decide +kernel
      have hl : raw7763step0Labels = raw7763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7763 raw7763Labels permutation346 hz
    mixedMoment B raw7763step0 raw7763step0Labels = mixedMoment B raw7763step1 raw7763step1Labels := by
      have hz : ∀ j, raw7763step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7763step1 = (fun i j => raw7763step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7763step1 raw7763step0; decide +kernel
      have hl : raw7763step1Labels = raw7763step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7763step0 raw7763step0Labels permutation56 hz
    mixedMoment B raw7763step1 raw7763step1Labels = mixedMoment B raw7763step2 raw7763step2Labels := by
      have ha : raw7763step2 = (fun i j => raw7763step1 (permutation26 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7763step2 raw7763step1; decide +kernel
      have hl : raw7763step2Labels = raw7763step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7763step1 raw7763step1Labels permutation26 permutation5
    mixedMoment B raw7763step2 raw7763step2Labels = mixedMoment B raw7763step3 raw7763step3Labels := by
      have ha : raw7763step3 = raw7763step2 := by apply Matrix.ext; unfold raw7763step3 raw7763step2; decide +kernel
      have hl : raw7763step2Labels = labelEmbedding1 ∘ raw7763step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7763step2 raw7763step2Labels raw7763step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2777 node2777Labels := by rfl

theorem canonical7764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7764 raw7764Labels = mixedMoment B node2778 node2778Labels := by
  calc
    mixedMoment B raw7764 raw7764Labels = mixedMoment B raw7764step0 raw7764step0Labels := by
      have hz : ∀ j, raw7764 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7764step0 = (fun i j => raw7764 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7764step0 raw7764; decide +kernel
      have hl : raw7764step0Labels = raw7764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7764 raw7764Labels permutation434 hz
    mixedMoment B raw7764step0 raw7764step0Labels = mixedMoment B raw7764step1 raw7764step1Labels := by
      have hz : ∀ j, raw7764step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7764step1 = (fun i j => raw7764step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7764step1 raw7764step0; decide +kernel
      have hl : raw7764step1Labels = raw7764step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7764step0 raw7764step0Labels permutation80 hz
    mixedMoment B raw7764step1 raw7764step1Labels = mixedMoment B raw7764step2 raw7764step2Labels := by
      have hz : ∀ j, raw7764step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7764step2 = (fun i j => raw7764step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7764step2 raw7764step1; decide +kernel
      have hl : raw7764step2Labels = raw7764step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7764step1 raw7764step1Labels permutation14 hz
    mixedMoment B raw7764step2 raw7764step2Labels = mixedMoment B raw7764step3 raw7764step3Labels := by
      have ha : raw7764step3 = (fun i j => raw7764step2 (permutation6 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7764step3 raw7764step2; decide +kernel
      have hl : raw7764step3Labels = raw7764step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7764step2 raw7764step2Labels permutation6 permutation5
    mixedMoment B raw7764step3 raw7764step3Labels = mixedMoment B raw7764step4 raw7764step4Labels := by
      have ha : raw7764step4 = raw7764step3 := by apply Matrix.ext; unfold raw7764step4 raw7764step3; decide +kernel
      have hl : raw7764step3Labels = labelEmbedding1 ∘ raw7764step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7764step3 raw7764step3Labels raw7764step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2778 node2778Labels := by rfl

theorem canonical7765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7765 raw7765Labels = mixedMoment B node3121 node3121Labels := by
  calc
    mixedMoment B raw7765 raw7765Labels = mixedMoment B raw7765step0 raw7765step0Labels := by
      have hz : ∀ j, raw7765 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7765step0 = (fun i j => raw7765 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7765step0 raw7765; decide +kernel
      have hl : raw7765step0Labels = raw7765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7765 raw7765Labels permutation434 hz
    mixedMoment B raw7765step0 raw7765step0Labels = mixedMoment B raw7765step1 raw7765step1Labels := by
      have hz : ∀ j, raw7765step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7765step1 = (fun i j => raw7765step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7765step1 raw7765step0; decide +kernel
      have hl : raw7765step1Labels = raw7765step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7765step0 raw7765step0Labels permutation80 hz
    mixedMoment B raw7765step1 raw7765step1Labels = mixedMoment B raw7765step2 raw7765step2Labels := by
      have hz : ∀ j, raw7765step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7765step2 = (fun i j => raw7765step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7765step2 raw7765step1; decide +kernel
      have hl : raw7765step2Labels = raw7765step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7765step1 raw7765step1Labels permutation14 hz
    mixedMoment B raw7765step2 raw7765step2Labels = mixedMoment B raw7765step3 raw7765step3Labels := by
      have ha : raw7765step3 = (fun i j => raw7765step2 (permutation5 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7765step3 raw7765step2; decide +kernel
      have hl : raw7765step3Labels = raw7765step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7765step2 raw7765step2Labels permutation5 permutation7
    mixedMoment B raw7765step3 raw7765step3Labels = mixedMoment B raw7765step4 raw7765step4Labels := by
      have ha : raw7765step4 = raw7765step3 := by apply Matrix.ext; unfold raw7765step4 raw7765step3; decide +kernel
      have hl : raw7765step3Labels = labelEmbedding1 ∘ raw7765step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7765step3 raw7765step3Labels raw7765step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3121 node3121Labels := by rfl

theorem canonical7766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7766 raw7766Labels = mixedMoment B node2521 node2521Labels := by
  calc
    mixedMoment B raw7766 raw7766Labels = mixedMoment B raw7766step0 raw7766step0Labels := by
      have hz : ∀ j, raw7766 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7766step0 = (fun i j => raw7766 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7766step0 raw7766; decide +kernel
      have hl : raw7766step0Labels = raw7766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7766 raw7766Labels permutation434 hz
    mixedMoment B raw7766step0 raw7766step0Labels = mixedMoment B raw7766step1 raw7766step1Labels := by
      have hz : ∀ j, raw7766step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7766step1 = (fun i j => raw7766step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7766step1 raw7766step0; decide +kernel
      have hl : raw7766step1Labels = raw7766step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7766step0 raw7766step0Labels permutation80 hz
    mixedMoment B raw7766step1 raw7766step1Labels = mixedMoment B raw7766step2 raw7766step2Labels := by
      have ha : raw7766step2 = (fun i j => raw7766step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7766step2 raw7766step1; decide +kernel
      have hl : raw7766step2Labels = raw7766step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7766step1 raw7766step1Labels permutation29 permutation5
    mixedMoment B raw7766step2 raw7766step2Labels = mixedMoment B raw7766step3 raw7766step3Labels := by
      have ha : raw7766step3 = raw7766step2 := by apply Matrix.ext; unfold raw7766step3 raw7766step2; decide +kernel
      have hl : raw7766step2Labels = labelEmbedding1 ∘ raw7766step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7766step2 raw7766step2Labels raw7766step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2521 node2521Labels := by rfl

theorem canonical7767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7767 raw7767Labels = mixedMoment B node2516 node2516Labels := by
  calc
    mixedMoment B raw7767 raw7767Labels = mixedMoment B raw7767step0 raw7767step0Labels := by
      have hz : ∀ j, raw7767 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7767step0 = (fun i j => raw7767 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7767step0 raw7767; decide +kernel
      have hl : raw7767step0Labels = raw7767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7767 raw7767Labels permutation434 hz
    mixedMoment B raw7767step0 raw7767step0Labels = mixedMoment B raw7767step1 raw7767step1Labels := by
      have ha : raw7767step1 = (fun i j => raw7767step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7767step1 raw7767step0; decide +kernel
      have hl : raw7767step1Labels = raw7767step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7767step0 raw7767step0Labels permutation136 permutation5
    mixedMoment B raw7767step1 raw7767step1Labels = mixedMoment B raw7767step2 raw7767step2Labels := by
      have ha : raw7767step2 = raw7767step1 := by apply Matrix.ext; unfold raw7767step2 raw7767step1; decide +kernel
      have hl : raw7767step1Labels = labelEmbedding1 ∘ raw7767step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7767step1 raw7767step1Labels raw7767step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2516 node2516Labels := by rfl

theorem canonical7768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7768 raw7768Labels = mixedMoment B node2516 node2516Labels := by
  calc
    mixedMoment B raw7768 raw7768Labels = mixedMoment B raw7768step0 raw7768step0Labels := by
      have hz : ∀ j, raw7768 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7768step0 = (fun i j => raw7768 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7768step0 raw7768; decide +kernel
      have hl : raw7768step0Labels = raw7768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7768 raw7768Labels permutation346 hz
    mixedMoment B raw7768step0 raw7768step0Labels = mixedMoment B raw7768step1 raw7768step1Labels := by
      have ha : raw7768step1 = (fun i j => raw7768step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7768step1 raw7768step0; decide +kernel
      have hl : raw7768step1Labels = raw7768step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7768step0 raw7768step0Labels permutation136 permutation5
    mixedMoment B raw7768step1 raw7768step1Labels = mixedMoment B raw7768step2 raw7768step2Labels := by
      have ha : raw7768step2 = raw7768step1 := by apply Matrix.ext; unfold raw7768step2 raw7768step1; decide +kernel
      have hl : raw7768step1Labels = labelEmbedding1 ∘ raw7768step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7768step1 raw7768step1Labels raw7768step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2516 node2516Labels := by rfl

theorem canonical7769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7769 raw7769Labels = mixedMoment B node2520 node2520Labels := by
  calc
    mixedMoment B raw7769 raw7769Labels = mixedMoment B raw7769step0 raw7769step0Labels := by
      have hz : ∀ j, raw7769 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7769step0 = (fun i j => raw7769 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7769step0 raw7769; decide +kernel
      have hl : raw7769step0Labels = raw7769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7769 raw7769Labels permutation434 hz
    mixedMoment B raw7769step0 raw7769step0Labels = mixedMoment B raw7769step1 raw7769step1Labels := by
      have hz : ∀ j, raw7769step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7769step1 = (fun i j => raw7769step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7769step1 raw7769step0; decide +kernel
      have hl : raw7769step1Labels = raw7769step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7769step0 raw7769step0Labels permutation80 hz
    mixedMoment B raw7769step1 raw7769step1Labels = mixedMoment B raw7769step2 raw7769step2Labels := by
      have ha : raw7769step2 = (fun i j => raw7769step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7769step2 raw7769step1; decide +kernel
      have hl : raw7769step2Labels = raw7769step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7769step1 raw7769step1Labels permutation28 permutation5
    mixedMoment B raw7769step2 raw7769step2Labels = mixedMoment B raw7769step3 raw7769step3Labels := by
      have ha : raw7769step3 = raw7769step2 := by apply Matrix.ext; unfold raw7769step3 raw7769step2; decide +kernel
      have hl : raw7769step2Labels = labelEmbedding1 ∘ raw7769step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7769step2 raw7769step2Labels raw7769step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2520 node2520Labels := by rfl

theorem canonical7770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7770 raw7770Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw7770 raw7770Labels = mixedMoment B raw7770step0 raw7770step0Labels := by
      have hz : ∀ j, raw7770 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7770step0 = (fun i j => raw7770 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7770step0 raw7770; decide +kernel
      have hl : raw7770step0Labels = raw7770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7770 raw7770Labels permutation434 hz
    mixedMoment B raw7770step0 raw7770step0Labels = mixedMoment B raw7770step1 raw7770step1Labels := by
      have hz : ∀ j, raw7770step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7770step1 = (fun i j => raw7770step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7770step1 raw7770step0; decide +kernel
      have hl : raw7770step1Labels = raw7770step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7770step0 raw7770step0Labels permutation80 hz
    mixedMoment B raw7770step1 raw7770step1Labels = mixedMoment B raw7770step2 raw7770step2Labels := by
      have ha : raw7770step2 = (fun i j => raw7770step1 (permutation23 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7770step2 raw7770step1; decide +kernel
      have hl : raw7770step2Labels = raw7770step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7770step1 raw7770step1Labels permutation23 permutation7
    mixedMoment B raw7770step2 raw7770step2Labels = mixedMoment B raw7770step3 raw7770step3Labels := by
      have ha : raw7770step3 = raw7770step2 := by apply Matrix.ext; unfold raw7770step3 raw7770step2; decide +kernel
      have hl : raw7770step2Labels = labelEmbedding1 ∘ raw7770step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7770step2 raw7770step2Labels raw7770step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

theorem canonical7771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7771 raw7771Labels = mixedMoment B node2521 node2521Labels := by
  calc
    mixedMoment B raw7771 raw7771Labels = mixedMoment B raw7771step0 raw7771step0Labels := by
      have hz : ∀ j, raw7771 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7771step0 = (fun i j => raw7771 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7771step0 raw7771; decide +kernel
      have hl : raw7771step0Labels = raw7771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7771 raw7771Labels permutation434 hz
    mixedMoment B raw7771step0 raw7771step0Labels = mixedMoment B raw7771step1 raw7771step1Labels := by
      have hz : ∀ j, raw7771step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7771step1 = (fun i j => raw7771step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7771step1 raw7771step0; decide +kernel
      have hl : raw7771step1Labels = raw7771step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7771step0 raw7771step0Labels permutation56 hz
    mixedMoment B raw7771step1 raw7771step1Labels = mixedMoment B raw7771step2 raw7771step2Labels := by
      have ha : raw7771step2 = (fun i j => raw7771step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7771step2 raw7771step1; decide +kernel
      have hl : raw7771step2Labels = raw7771step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7771step1 raw7771step1Labels permutation29 permutation5
    mixedMoment B raw7771step2 raw7771step2Labels = mixedMoment B raw7771step3 raw7771step3Labels := by
      have ha : raw7771step3 = raw7771step2 := by apply Matrix.ext; unfold raw7771step3 raw7771step2; decide +kernel
      have hl : raw7771step2Labels = labelEmbedding1 ∘ raw7771step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7771step2 raw7771step2Labels raw7771step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2521 node2521Labels := by rfl

theorem canonical7772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7772 raw7772Labels = mixedMoment B node2516 node2516Labels := by
  calc
    mixedMoment B raw7772 raw7772Labels = mixedMoment B raw7772step0 raw7772step0Labels := by
      have hz : ∀ j, raw7772 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7772step0 = (fun i j => raw7772 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7772step0 raw7772; decide +kernel
      have hl : raw7772step0Labels = raw7772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7772 raw7772Labels permutation434 hz
    mixedMoment B raw7772step0 raw7772step0Labels = mixedMoment B raw7772step1 raw7772step1Labels := by
      have ha : raw7772step1 = (fun i j => raw7772step0 (permutation142 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7772step1 raw7772step0; decide +kernel
      have hl : raw7772step1Labels = raw7772step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7772step0 raw7772step0Labels permutation142 permutation5
    mixedMoment B raw7772step1 raw7772step1Labels = mixedMoment B raw7772step2 raw7772step2Labels := by
      have ha : raw7772step2 = raw7772step1 := by apply Matrix.ext; unfold raw7772step2 raw7772step1; decide +kernel
      have hl : raw7772step1Labels = labelEmbedding1 ∘ raw7772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7772step1 raw7772step1Labels raw7772step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2516 node2516Labels := by rfl

theorem canonical7773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7773 raw7773Labels = mixedMoment B node2516 node2516Labels := by
  calc
    mixedMoment B raw7773 raw7773Labels = mixedMoment B raw7773step0 raw7773step0Labels := by
      have hz : ∀ j, raw7773 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7773step0 = (fun i j => raw7773 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7773step0 raw7773; decide +kernel
      have hl : raw7773step0Labels = raw7773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7773 raw7773Labels permutation265 hz
    mixedMoment B raw7773step0 raw7773step0Labels = mixedMoment B raw7773step1 raw7773step1Labels := by
      have ha : raw7773step1 = (fun i j => raw7773step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7773step1 raw7773step0; decide +kernel
      have hl : raw7773step1Labels = raw7773step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7773step0 raw7773step0Labels permutation136 permutation5
    mixedMoment B raw7773step1 raw7773step1Labels = mixedMoment B raw7773step2 raw7773step2Labels := by
      have ha : raw7773step2 = raw7773step1 := by apply Matrix.ext; unfold raw7773step2 raw7773step1; decide +kernel
      have hl : raw7773step1Labels = labelEmbedding1 ∘ raw7773step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7773step1 raw7773step1Labels raw7773step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2516 node2516Labels := by rfl

theorem canonical7774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7774 raw7774Labels = mixedMoment B node2520 node2520Labels := by
  calc
    mixedMoment B raw7774 raw7774Labels = mixedMoment B raw7774step0 raw7774step0Labels := by
      have hz : ∀ j, raw7774 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7774step0 = (fun i j => raw7774 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7774step0 raw7774; decide +kernel
      have hl : raw7774step0Labels = raw7774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7774 raw7774Labels permutation434 hz
    mixedMoment B raw7774step0 raw7774step0Labels = mixedMoment B raw7774step1 raw7774step1Labels := by
      have hz : ∀ j, raw7774step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7774step1 = (fun i j => raw7774step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7774step1 raw7774step0; decide +kernel
      have hl : raw7774step1Labels = raw7774step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7774step0 raw7774step0Labels permutation56 hz
    mixedMoment B raw7774step1 raw7774step1Labels = mixedMoment B raw7774step2 raw7774step2Labels := by
      have ha : raw7774step2 = (fun i j => raw7774step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7774step2 raw7774step1; decide +kernel
      have hl : raw7774step2Labels = raw7774step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7774step1 raw7774step1Labels permutation28 permutation5
    mixedMoment B raw7774step2 raw7774step2Labels = mixedMoment B raw7774step3 raw7774step3Labels := by
      have ha : raw7774step3 = raw7774step2 := by apply Matrix.ext; unfold raw7774step3 raw7774step2; decide +kernel
      have hl : raw7774step2Labels = labelEmbedding1 ∘ raw7774step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7774step2 raw7774step2Labels raw7774step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2520 node2520Labels := by rfl

theorem canonical7775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7775 raw7775Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw7775 raw7775Labels = mixedMoment B raw7775step0 raw7775step0Labels := by
      have hz : ∀ j, raw7775 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7775step0 = (fun i j => raw7775 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7775step0 raw7775; decide +kernel
      have hl : raw7775step0Labels = raw7775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7775 raw7775Labels permutation434 hz
    mixedMoment B raw7775step0 raw7775step0Labels = mixedMoment B raw7775step1 raw7775step1Labels := by
      have hz : ∀ j, raw7775step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7775step1 = (fun i j => raw7775step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7775step1 raw7775step0; decide +kernel
      have hl : raw7775step1Labels = raw7775step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7775step0 raw7775step0Labels permutation56 hz
    mixedMoment B raw7775step1 raw7775step1Labels = mixedMoment B raw7775step2 raw7775step2Labels := by
      have ha : raw7775step2 = (fun i j => raw7775step1 (permutation23 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7775step2 raw7775step1; decide +kernel
      have hl : raw7775step2Labels = raw7775step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7775step1 raw7775step1Labels permutation23 permutation7
    mixedMoment B raw7775step2 raw7775step2Labels = mixedMoment B raw7775step3 raw7775step3Labels := by
      have ha : raw7775step3 = raw7775step2 := by apply Matrix.ext; unfold raw7775step3 raw7775step2; decide +kernel
      have hl : raw7775step2Labels = labelEmbedding1 ∘ raw7775step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7775step2 raw7775step2Labels raw7775step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

theorem canonical7776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7776 raw7776Labels = mixedMoment B node2521 node2521Labels := by
  calc
    mixedMoment B raw7776 raw7776Labels = mixedMoment B raw7776step0 raw7776step0Labels := by
      have hz : ∀ j, raw7776 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7776step0 = (fun i j => raw7776 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7776step0 raw7776; decide +kernel
      have hl : raw7776step0Labels = raw7776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7776 raw7776Labels permutation346 hz
    mixedMoment B raw7776step0 raw7776step0Labels = mixedMoment B raw7776step1 raw7776step1Labels := by
      have hz : ∀ j, raw7776step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7776step1 = (fun i j => raw7776step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7776step1 raw7776step0; decide +kernel
      have hl : raw7776step1Labels = raw7776step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7776step0 raw7776step0Labels permutation56 hz
    mixedMoment B raw7776step1 raw7776step1Labels = mixedMoment B raw7776step2 raw7776step2Labels := by
      have ha : raw7776step2 = (fun i j => raw7776step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7776step2 raw7776step1; decide +kernel
      have hl : raw7776step2Labels = raw7776step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7776step1 raw7776step1Labels permutation29 permutation5
    mixedMoment B raw7776step2 raw7776step2Labels = mixedMoment B raw7776step3 raw7776step3Labels := by
      have ha : raw7776step3 = raw7776step2 := by apply Matrix.ext; unfold raw7776step3 raw7776step2; decide +kernel
      have hl : raw7776step2Labels = labelEmbedding1 ∘ raw7776step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7776step2 raw7776step2Labels raw7776step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2521 node2521Labels := by rfl

theorem canonical7777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7777 raw7777Labels = mixedMoment B node2516 node2516Labels := by
  calc
    mixedMoment B raw7777 raw7777Labels = mixedMoment B raw7777step0 raw7777step0Labels := by
      have hz : ∀ j, raw7777 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7777step0 = (fun i j => raw7777 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7777step0 raw7777; decide +kernel
      have hl : raw7777step0Labels = raw7777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7777 raw7777Labels permutation346 hz
    mixedMoment B raw7777step0 raw7777step0Labels = mixedMoment B raw7777step1 raw7777step1Labels := by
      have ha : raw7777step1 = (fun i j => raw7777step0 (permutation142 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7777step1 raw7777step0; decide +kernel
      have hl : raw7777step1Labels = raw7777step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7777step0 raw7777step0Labels permutation142 permutation5
    mixedMoment B raw7777step1 raw7777step1Labels = mixedMoment B raw7777step2 raw7777step2Labels := by
      have ha : raw7777step2 = raw7777step1 := by apply Matrix.ext; unfold raw7777step2 raw7777step1; decide +kernel
      have hl : raw7777step1Labels = labelEmbedding1 ∘ raw7777step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7777step1 raw7777step1Labels raw7777step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2516 node2516Labels := by rfl

theorem canonical7778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7778 raw7778Labels = mixedMoment B node2516 node2516Labels := by
  calc
    mixedMoment B raw7778 raw7778Labels = mixedMoment B raw7778step0 raw7778step0Labels := by
      have hz : ∀ j, raw7778 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7778step0 = (fun i j => raw7778 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7778step0 raw7778; decide +kernel
      have hl : raw7778step0Labels = raw7778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7778 raw7778Labels permutation265 hz
    mixedMoment B raw7778step0 raw7778step0Labels = mixedMoment B raw7778step1 raw7778step1Labels := by
      have ha : raw7778step1 = (fun i j => raw7778step0 (permutation142 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7778step1 raw7778step0; decide +kernel
      have hl : raw7778step1Labels = raw7778step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7778step0 raw7778step0Labels permutation142 permutation5
    mixedMoment B raw7778step1 raw7778step1Labels = mixedMoment B raw7778step2 raw7778step2Labels := by
      have ha : raw7778step2 = raw7778step1 := by apply Matrix.ext; unfold raw7778step2 raw7778step1; decide +kernel
      have hl : raw7778step1Labels = labelEmbedding1 ∘ raw7778step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7778step1 raw7778step1Labels raw7778step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2516 node2516Labels := by rfl

theorem canonical7779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7779 raw7779Labels = mixedMoment B node2520 node2520Labels := by
  calc
    mixedMoment B raw7779 raw7779Labels = mixedMoment B raw7779step0 raw7779step0Labels := by
      have hz : ∀ j, raw7779 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7779step0 = (fun i j => raw7779 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7779step0 raw7779; decide +kernel
      have hl : raw7779step0Labels = raw7779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7779 raw7779Labels permutation346 hz
    mixedMoment B raw7779step0 raw7779step0Labels = mixedMoment B raw7779step1 raw7779step1Labels := by
      have hz : ∀ j, raw7779step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7779step1 = (fun i j => raw7779step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7779step1 raw7779step0; decide +kernel
      have hl : raw7779step1Labels = raw7779step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7779step0 raw7779step0Labels permutation56 hz
    mixedMoment B raw7779step1 raw7779step1Labels = mixedMoment B raw7779step2 raw7779step2Labels := by
      have ha : raw7779step2 = (fun i j => raw7779step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7779step2 raw7779step1; decide +kernel
      have hl : raw7779step2Labels = raw7779step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7779step1 raw7779step1Labels permutation28 permutation5
    mixedMoment B raw7779step2 raw7779step2Labels = mixedMoment B raw7779step3 raw7779step3Labels := by
      have ha : raw7779step3 = raw7779step2 := by apply Matrix.ext; unfold raw7779step3 raw7779step2; decide +kernel
      have hl : raw7779step2Labels = labelEmbedding1 ∘ raw7779step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7779step2 raw7779step2Labels raw7779step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2520 node2520Labels := by rfl

theorem canonical7780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7780 raw7780Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw7780 raw7780Labels = mixedMoment B raw7780step0 raw7780step0Labels := by
      have hz : ∀ j, raw7780 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7780step0 = (fun i j => raw7780 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7780step0 raw7780; decide +kernel
      have hl : raw7780step0Labels = raw7780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7780 raw7780Labels permutation346 hz
    mixedMoment B raw7780step0 raw7780step0Labels = mixedMoment B raw7780step1 raw7780step1Labels := by
      have hz : ∀ j, raw7780step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7780step1 = (fun i j => raw7780step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7780step1 raw7780step0; decide +kernel
      have hl : raw7780step1Labels = raw7780step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7780step0 raw7780step0Labels permutation56 hz
    mixedMoment B raw7780step1 raw7780step1Labels = mixedMoment B raw7780step2 raw7780step2Labels := by
      have ha : raw7780step2 = (fun i j => raw7780step1 (permutation23 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7780step2 raw7780step1; decide +kernel
      have hl : raw7780step2Labels = raw7780step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7780step1 raw7780step1Labels permutation23 permutation7
    mixedMoment B raw7780step2 raw7780step2Labels = mixedMoment B raw7780step3 raw7780step3Labels := by
      have ha : raw7780step3 = raw7780step2 := by apply Matrix.ext; unfold raw7780step3 raw7780step2; decide +kernel
      have hl : raw7780step2Labels = labelEmbedding1 ∘ raw7780step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7780step2 raw7780step2Labels raw7780step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

theorem canonical7781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7781 raw7781Labels = mixedMoment B node2780 node2780Labels := by
  calc
    mixedMoment B raw7781 raw7781Labels = mixedMoment B raw7781step0 raw7781step0Labels := by
      have hz : ∀ j, raw7781 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7781step0 = (fun i j => raw7781 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7781step0 raw7781; decide +kernel
      have hl : raw7781step0Labels = raw7781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7781 raw7781Labels permutation434 hz
    mixedMoment B raw7781step0 raw7781step0Labels = mixedMoment B raw7781step1 raw7781step1Labels := by
      have hz : ∀ j, raw7781step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7781step1 = (fun i j => raw7781step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7781step1 raw7781step0; decide +kernel
      have hl : raw7781step1Labels = raw7781step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7781step0 raw7781step0Labels permutation80 hz
    mixedMoment B raw7781step1 raw7781step1Labels = mixedMoment B raw7781step2 raw7781step2Labels := by
      have hz : ∀ j, raw7781step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7781step2 = (fun i j => raw7781step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7781step2 raw7781step1; decide +kernel
      have hl : raw7781step2Labels = raw7781step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7781step1 raw7781step1Labels permutation14 hz
    mixedMoment B raw7781step2 raw7781step2Labels = mixedMoment B raw7781step3 raw7781step3Labels := by
      have ha : raw7781step3 = (fun i j => raw7781step2 (permutation7 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7781step3 raw7781step2; decide +kernel
      have hl : raw7781step3Labels = raw7781step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7781step2 raw7781step2Labels permutation7 permutation5
    mixedMoment B raw7781step3 raw7781step3Labels = mixedMoment B raw7781step4 raw7781step4Labels := by
      have ha : raw7781step4 = raw7781step3 := by apply Matrix.ext; unfold raw7781step4 raw7781step3; decide +kernel
      have hl : raw7781step3Labels = labelEmbedding1 ∘ raw7781step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7781step3 raw7781step3Labels raw7781step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2780 node2780Labels := by rfl

theorem canonical7782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7782 raw7782Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw7782 raw7782Labels = mixedMoment B raw7782step0 raw7782step0Labels := by
      have hz : ∀ j, raw7782 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7782step0 = (fun i j => raw7782 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7782step0 raw7782; decide +kernel
      have hl : raw7782step0Labels = raw7782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7782 raw7782Labels permutation434 hz
    mixedMoment B raw7782step0 raw7782step0Labels = mixedMoment B raw7782step1 raw7782step1Labels := by
      have hz : ∀ j, raw7782step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7782step1 = (fun i j => raw7782step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7782step1 raw7782step0; decide +kernel
      have hl : raw7782step1Labels = raw7782step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7782step0 raw7782step0Labels permutation80 hz
    mixedMoment B raw7782step1 raw7782step1Labels = mixedMoment B raw7782step2 raw7782step2Labels := by
      have ha : raw7782step2 = (fun i j => raw7782step1 (permutation23 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7782step2 raw7782step1; decide +kernel
      have hl : raw7782step2Labels = raw7782step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7782step1 raw7782step1Labels permutation23 permutation7
    mixedMoment B raw7782step2 raw7782step2Labels = mixedMoment B raw7782step3 raw7782step3Labels := by
      have ha : raw7782step3 = raw7782step2 := by apply Matrix.ext; unfold raw7782step3 raw7782step2; decide +kernel
      have hl : raw7782step2Labels = labelEmbedding1 ∘ raw7782step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7782step2 raw7782step2Labels raw7782step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2761 node2761Labels := by rfl

theorem canonical7783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7783 raw7783Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw7783 raw7783Labels = mixedMoment B raw7783step0 raw7783step0Labels := by
      have hz : ∀ j, raw7783 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7783step0 = (fun i j => raw7783 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7783step0 raw7783; decide +kernel
      have hl : raw7783step0Labels = raw7783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7783 raw7783Labels permutation434 hz
    mixedMoment B raw7783step0 raw7783step0Labels = mixedMoment B raw7783step1 raw7783step1Labels := by
      have hz : ∀ j, raw7783step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7783step1 = (fun i j => raw7783step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7783step1 raw7783step0; decide +kernel
      have hl : raw7783step1Labels = raw7783step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7783step0 raw7783step0Labels permutation56 hz
    mixedMoment B raw7783step1 raw7783step1Labels = mixedMoment B raw7783step2 raw7783step2Labels := by
      have ha : raw7783step2 = (fun i j => raw7783step1 (permutation23 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7783step2 raw7783step1; decide +kernel
      have hl : raw7783step2Labels = raw7783step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7783step1 raw7783step1Labels permutation23 permutation7
    mixedMoment B raw7783step2 raw7783step2Labels = mixedMoment B raw7783step3 raw7783step3Labels := by
      have ha : raw7783step3 = raw7783step2 := by apply Matrix.ext; unfold raw7783step3 raw7783step2; decide +kernel
      have hl : raw7783step2Labels = labelEmbedding1 ∘ raw7783step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7783step2 raw7783step2Labels raw7783step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2761 node2761Labels := by rfl

theorem canonical7784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7784 raw7784Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw7784 raw7784Labels = mixedMoment B raw7784step0 raw7784step0Labels := by
      have hz : ∀ j, raw7784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7784step0 = (fun i j => raw7784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7784step0 raw7784; decide +kernel
      have hl : raw7784step0Labels = raw7784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7784 raw7784Labels permutation346 hz
    mixedMoment B raw7784step0 raw7784step0Labels = mixedMoment B raw7784step1 raw7784step1Labels := by
      have hz : ∀ j, raw7784step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7784step1 = (fun i j => raw7784step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7784step1 raw7784step0; decide +kernel
      have hl : raw7784step1Labels = raw7784step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7784step0 raw7784step0Labels permutation56 hz
    mixedMoment B raw7784step1 raw7784step1Labels = mixedMoment B raw7784step2 raw7784step2Labels := by
      have ha : raw7784step2 = (fun i j => raw7784step1 (permutation23 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7784step2 raw7784step1; decide +kernel
      have hl : raw7784step2Labels = raw7784step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7784step1 raw7784step1Labels permutation23 permutation7
    mixedMoment B raw7784step2 raw7784step2Labels = mixedMoment B raw7784step3 raw7784step3Labels := by
      have ha : raw7784step3 = raw7784step2 := by apply Matrix.ext; unfold raw7784step3 raw7784step2; decide +kernel
      have hl : raw7784step2Labels = labelEmbedding1 ∘ raw7784step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7784step2 raw7784step2Labels raw7784step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2761 node2761Labels := by rfl

theorem canonical7785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7785 raw7785Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw7785 raw7785Labels = mixedMoment B raw7785step0 raw7785step0Labels := by
      have hz : ∀ j, raw7785 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7785step0 = (fun i j => raw7785 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7785step0 raw7785; decide +kernel
      have hl : raw7785step0Labels = raw7785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7785 raw7785Labels permutation434 hz
    mixedMoment B raw7785step0 raw7785step0Labels = mixedMoment B raw7785step1 raw7785step1Labels := by
      have hz : ∀ j, raw7785step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7785step1 = (fun i j => raw7785step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7785step1 raw7785step0; decide +kernel
      have hl : raw7785step1Labels = raw7785step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7785step0 raw7785step0Labels permutation80 hz
    mixedMoment B raw7785step1 raw7785step1Labels = mixedMoment B raw7785step2 raw7785step2Labels := by
      have hz : ∀ j, raw7785step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7785step2 = (fun i j => raw7785step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7785step2 raw7785step1; decide +kernel
      have hl : raw7785step2Labels = raw7785step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7785step1 raw7785step1Labels permutation14 hz
    mixedMoment B raw7785step2 raw7785step2Labels = mixedMoment B raw7785step3 raw7785step3Labels := by
      have ha : raw7785step3 = (fun i j => raw7785step2 (permutation5 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7785step3 raw7785step2; decide +kernel
      have hl : raw7785step3Labels = raw7785step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7785step2 raw7785step2Labels permutation5 permutation7
    mixedMoment B raw7785step3 raw7785step3Labels = mixedMoment B raw7785step4 raw7785step4Labels := by
      have ha : raw7785step4 = raw7785step3 := by apply Matrix.ext; unfold raw7785step4 raw7785step3; decide +kernel
      have hl : raw7785step3Labels = labelEmbedding1 ∘ raw7785step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7785step3 raw7785step3Labels raw7785step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2783 node2783Labels := by rfl

theorem canonical7786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7786 raw7786Labels = mixedMoment B node1093 node1093Labels := by
  calc
    mixedMoment B raw7786 raw7786Labels = mixedMoment B raw7786step0 raw7786step0Labels := by
      have hz : ∀ j, raw7786 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7786step0 = (fun i j => raw7786 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7786step0 raw7786; decide +kernel
      have hl : raw7786step0Labels = raw7786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7786 raw7786Labels permutation434 hz
    mixedMoment B raw7786step0 raw7786step0Labels = mixedMoment B raw7786step1 raw7786step1Labels := by
      have hz : ∀ j, raw7786step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7786step1 = (fun i j => raw7786step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7786step1 raw7786step0; decide +kernel
      have hl : raw7786step1Labels = raw7786step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7786step0 raw7786step0Labels permutation80 hz
    mixedMoment B raw7786step1 raw7786step1Labels = mixedMoment B raw7786step2 raw7786step2Labels := by
      have hz : ∀ j, raw7786step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7786step2 = (fun i j => raw7786step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7786step2 raw7786step1; decide +kernel
      have hl : raw7786step2Labels = raw7786step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7786step1 raw7786step1Labels permutation14 hz
    mixedMoment B raw7786step2 raw7786step2Labels = mixedMoment B raw7786step3 raw7786step3Labels := by
      have ha : raw7786step3 = (fun i j => raw7786step2 (permutation7 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7786step3 raw7786step2; decide +kernel
      have hl : raw7786step3Labels = raw7786step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7786step2 raw7786step2Labels permutation7 permutation5
    mixedMoment B raw7786step3 raw7786step3Labels = mixedMoment B raw7786step4 raw7786step4Labels := by
      have ha : raw7786step4 = raw7786step3 := by apply Matrix.ext; unfold raw7786step4 raw7786step3; decide +kernel
      have hl : raw7786step3Labels = labelEmbedding1 ∘ raw7786step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7786step3 raw7786step3Labels raw7786step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1093 node1093Labels := by rfl

theorem canonical7787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7787 raw7787Labels = mixedMoment B node1088 node1088Labels := by
  calc
    mixedMoment B raw7787 raw7787Labels = mixedMoment B raw7787step0 raw7787step0Labels := by
      have hz : ∀ j, raw7787 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7787step0 = (fun i j => raw7787 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7787step0 raw7787; decide +kernel
      have hl : raw7787step0Labels = raw7787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7787 raw7787Labels permutation434 hz
    mixedMoment B raw7787step0 raw7787step0Labels = mixedMoment B raw7787step1 raw7787step1Labels := by
      have hz : ∀ j, raw7787step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7787step1 = (fun i j => raw7787step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7787step1 raw7787step0; decide +kernel
      have hl : raw7787step1Labels = raw7787step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7787step0 raw7787step0Labels permutation80 hz
    mixedMoment B raw7787step1 raw7787step1Labels = mixedMoment B raw7787step2 raw7787step2Labels := by
      have ha : raw7787step2 = (fun i j => raw7787step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7787step2 raw7787step1; decide +kernel
      have hl : raw7787step2Labels = raw7787step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7787step1 raw7787step1Labels permutation28 permutation5
    mixedMoment B raw7787step2 raw7787step2Labels = mixedMoment B raw7787step3 raw7787step3Labels := by
      have ha : raw7787step3 = raw7787step2 := by apply Matrix.ext; unfold raw7787step3 raw7787step2; decide +kernel
      have hl : raw7787step2Labels = labelEmbedding1 ∘ raw7787step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7787step2 raw7787step2Labels raw7787step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1088 node1088Labels := by rfl

theorem canonical7788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7788 raw7788Labels = mixedMoment B node1088 node1088Labels := by
  calc
    mixedMoment B raw7788 raw7788Labels = mixedMoment B raw7788step0 raw7788step0Labels := by
      have hz : ∀ j, raw7788 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7788step0 = (fun i j => raw7788 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7788step0 raw7788; decide +kernel
      have hl : raw7788step0Labels = raw7788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7788 raw7788Labels permutation434 hz
    mixedMoment B raw7788step0 raw7788step0Labels = mixedMoment B raw7788step1 raw7788step1Labels := by
      have hz : ∀ j, raw7788step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7788step1 = (fun i j => raw7788step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7788step1 raw7788step0; decide +kernel
      have hl : raw7788step1Labels = raw7788step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7788step0 raw7788step0Labels permutation56 hz
    mixedMoment B raw7788step1 raw7788step1Labels = mixedMoment B raw7788step2 raw7788step2Labels := by
      have ha : raw7788step2 = (fun i j => raw7788step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7788step2 raw7788step1; decide +kernel
      have hl : raw7788step2Labels = raw7788step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7788step1 raw7788step1Labels permutation28 permutation5
    mixedMoment B raw7788step2 raw7788step2Labels = mixedMoment B raw7788step3 raw7788step3Labels := by
      have ha : raw7788step3 = raw7788step2 := by apply Matrix.ext; unfold raw7788step3 raw7788step2; decide +kernel
      have hl : raw7788step2Labels = labelEmbedding1 ∘ raw7788step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7788step2 raw7788step2Labels raw7788step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1088 node1088Labels := by rfl

theorem canonical7789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7789 raw7789Labels = mixedMoment B node1088 node1088Labels := by
  calc
    mixedMoment B raw7789 raw7789Labels = mixedMoment B raw7789step0 raw7789step0Labels := by
      have hz : ∀ j, raw7789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7789step0 = (fun i j => raw7789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7789step0 raw7789; decide +kernel
      have hl : raw7789step0Labels = raw7789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7789 raw7789Labels permutation346 hz
    mixedMoment B raw7789step0 raw7789step0Labels = mixedMoment B raw7789step1 raw7789step1Labels := by
      have hz : ∀ j, raw7789step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7789step1 = (fun i j => raw7789step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7789step1 raw7789step0; decide +kernel
      have hl : raw7789step1Labels = raw7789step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7789step0 raw7789step0Labels permutation56 hz
    mixedMoment B raw7789step1 raw7789step1Labels = mixedMoment B raw7789step2 raw7789step2Labels := by
      have ha : raw7789step2 = (fun i j => raw7789step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7789step2 raw7789step1; decide +kernel
      have hl : raw7789step2Labels = raw7789step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7789step1 raw7789step1Labels permutation28 permutation5
    mixedMoment B raw7789step2 raw7789step2Labels = mixedMoment B raw7789step3 raw7789step3Labels := by
      have ha : raw7789step3 = raw7789step2 := by apply Matrix.ext; unfold raw7789step3 raw7789step2; decide +kernel
      have hl : raw7789step2Labels = labelEmbedding1 ∘ raw7789step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7789step2 raw7789step2Labels raw7789step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1088 node1088Labels := by rfl

theorem canonical7790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7790 raw7790Labels = mixedMoment B node1092 node1092Labels := by
  calc
    mixedMoment B raw7790 raw7790Labels = mixedMoment B raw7790step0 raw7790step0Labels := by
      have hz : ∀ j, raw7790 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7790step0 = (fun i j => raw7790 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7790step0 raw7790; decide +kernel
      have hl : raw7790step0Labels = raw7790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7790 raw7790Labels permutation434 hz
    mixedMoment B raw7790step0 raw7790step0Labels = mixedMoment B raw7790step1 raw7790step1Labels := by
      have hz : ∀ j, raw7790step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7790step1 = (fun i j => raw7790step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7790step1 raw7790step0; decide +kernel
      have hl : raw7790step1Labels = raw7790step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7790step0 raw7790step0Labels permutation80 hz
    mixedMoment B raw7790step1 raw7790step1Labels = mixedMoment B raw7790step2 raw7790step2Labels := by
      have hz : ∀ j, raw7790step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7790step2 = (fun i j => raw7790step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7790step2 raw7790step1; decide +kernel
      have hl : raw7790step2Labels = raw7790step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7790step1 raw7790step1Labels permutation14 hz
    mixedMoment B raw7790step2 raw7790step2Labels = mixedMoment B raw7790step3 raw7790step3Labels := by
      have ha : raw7790step3 = (fun i j => raw7790step2 (permutation6 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7790step3 raw7790step2; decide +kernel
      have hl : raw7790step3Labels = raw7790step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7790step2 raw7790step2Labels permutation6 permutation5
    mixedMoment B raw7790step3 raw7790step3Labels = mixedMoment B raw7790step4 raw7790step4Labels := by
      have ha : raw7790step4 = raw7790step3 := by apply Matrix.ext; unfold raw7790step4 raw7790step3; decide +kernel
      have hl : raw7790step3Labels = labelEmbedding1 ∘ raw7790step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7790step3 raw7790step3Labels raw7790step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1092 node1092Labels := by rfl

theorem canonical7791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7791 raw7791Labels = mixedMoment B node2789 node2789Labels := by
  calc
    mixedMoment B raw7791 raw7791Labels = mixedMoment B raw7791step0 raw7791step0Labels := by
      have hz : ∀ j, raw7791 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7791step0 = (fun i j => raw7791 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7791step0 raw7791; decide +kernel
      have hl : raw7791step0Labels = raw7791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7791 raw7791Labels permutation434 hz
    mixedMoment B raw7791step0 raw7791step0Labels = mixedMoment B raw7791step1 raw7791step1Labels := by
      have hz : ∀ j, raw7791step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7791step1 = (fun i j => raw7791step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7791step1 raw7791step0; decide +kernel
      have hl : raw7791step1Labels = raw7791step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7791step0 raw7791step0Labels permutation80 hz
    mixedMoment B raw7791step1 raw7791step1Labels = mixedMoment B raw7791step2 raw7791step2Labels := by
      have hz : ∀ j, raw7791step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7791step2 = (fun i j => raw7791step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7791step2 raw7791step1; decide +kernel
      have hl : raw7791step2Labels = raw7791step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7791step1 raw7791step1Labels permutation14 hz
    _ = mixedMoment B node2789 node2789Labels := by rfl

theorem canonical7792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7792 raw7792Labels = mixedMoment B node1303 node1303Labels := by
  calc
    mixedMoment B raw7792 raw7792Labels = mixedMoment B raw7792step0 raw7792step0Labels := by
      have hz : ∀ j, raw7792 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7792step0 = (fun i j => raw7792 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7792step0 raw7792; decide +kernel
      have hl : raw7792step0Labels = raw7792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7792 raw7792Labels permutation434 hz
    mixedMoment B raw7792step0 raw7792step0Labels = mixedMoment B raw7792step1 raw7792step1Labels := by
      have hz : ∀ j, raw7792step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7792step1 = (fun i j => raw7792step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7792step1 raw7792step0; decide +kernel
      have hl : raw7792step1Labels = raw7792step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7792step0 raw7792step0Labels permutation80 hz
    _ = mixedMoment B node1303 node1303Labels := by rfl

theorem canonical7793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7793 raw7793Labels = mixedMoment B node1303 node1303Labels := by
  calc
    mixedMoment B raw7793 raw7793Labels = mixedMoment B raw7793step0 raw7793step0Labels := by
      have hz : ∀ j, raw7793 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7793step0 = (fun i j => raw7793 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7793step0 raw7793; decide +kernel
      have hl : raw7793step0Labels = raw7793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7793 raw7793Labels permutation434 hz
    mixedMoment B raw7793step0 raw7793step0Labels = mixedMoment B raw7793step1 raw7793step1Labels := by
      have hz : ∀ j, raw7793step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7793step1 = (fun i j => raw7793step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7793step1 raw7793step0; decide +kernel
      have hl : raw7793step1Labels = raw7793step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7793step0 raw7793step0Labels permutation56 hz
    _ = mixedMoment B node1303 node1303Labels := by rfl

theorem canonical7794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7794 raw7794Labels = mixedMoment B node1303 node1303Labels := by
  calc
    mixedMoment B raw7794 raw7794Labels = mixedMoment B raw7794step0 raw7794step0Labels := by
      have hz : ∀ j, raw7794 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7794step0 = (fun i j => raw7794 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7794step0 raw7794; decide +kernel
      have hl : raw7794step0Labels = raw7794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7794 raw7794Labels permutation346 hz
    mixedMoment B raw7794step0 raw7794step0Labels = mixedMoment B raw7794step1 raw7794step1Labels := by
      have hz : ∀ j, raw7794step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7794step1 = (fun i j => raw7794step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7794step1 raw7794step0; decide +kernel
      have hl : raw7794step1Labels = raw7794step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7794step0 raw7794step0Labels permutation56 hz
    _ = mixedMoment B node1303 node1303Labels := by rfl

theorem canonical7795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7795 raw7795Labels = mixedMoment B node1310 node1310Labels := by
  calc
    mixedMoment B raw7795 raw7795Labels = mixedMoment B raw7795step0 raw7795step0Labels := by
      have hz : ∀ j, raw7795 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7795step0 = (fun i j => raw7795 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7795step0 raw7795; decide +kernel
      have hl : raw7795step0Labels = raw7795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7795 raw7795Labels permutation434 hz
    mixedMoment B raw7795step0 raw7795step0Labels = mixedMoment B raw7795step1 raw7795step1Labels := by
      have hz : ∀ j, raw7795step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7795step1 = (fun i j => raw7795step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7795step1 raw7795step0; decide +kernel
      have hl : raw7795step1Labels = raw7795step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7795step0 raw7795step0Labels permutation80 hz
    mixedMoment B raw7795step1 raw7795step1Labels = mixedMoment B raw7795step2 raw7795step2Labels := by
      have hz : ∀ j, raw7795step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7795step2 = (fun i j => raw7795step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7795step2 raw7795step1; decide +kernel
      have hl : raw7795step2Labels = raw7795step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7795step1 raw7795step1Labels permutation14 hz
    mixedMoment B raw7795step2 raw7795step2Labels = mixedMoment B raw7795step3 raw7795step3Labels := by
      have ha : raw7795step3 = (fun i j => raw7795step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7795step3 raw7795step2; decide +kernel
      have hl : raw7795step3Labels = raw7795step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7795step2 raw7795step2Labels permutation3 permutation2
    _ = mixedMoment B node1310 node1310Labels := by rfl

theorem canonical7796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7796 raw7796Labels = mixedMoment B node1309 node1309Labels := by
  calc
    mixedMoment B raw7796 raw7796Labels = mixedMoment B raw7796step0 raw7796step0Labels := by
      have hz : ∀ j, raw7796 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7796step0 = (fun i j => raw7796 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7796step0 raw7796; decide +kernel
      have hl : raw7796step0Labels = raw7796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7796 raw7796Labels permutation434 hz
    mixedMoment B raw7796step0 raw7796step0Labels = mixedMoment B raw7796step1 raw7796step1Labels := by
      have hz : ∀ j, raw7796step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7796step1 = (fun i j => raw7796step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7796step1 raw7796step0; decide +kernel
      have hl : raw7796step1Labels = raw7796step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7796step0 raw7796step0Labels permutation80 hz
    mixedMoment B raw7796step1 raw7796step1Labels = mixedMoment B raw7796step2 raw7796step2Labels := by
      have hz : ∀ j, raw7796step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7796step2 = (fun i j => raw7796step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7796step2 raw7796step1; decide +kernel
      have hl : raw7796step2Labels = raw7796step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7796step1 raw7796step1Labels permutation14 hz
    _ = mixedMoment B node1309 node1309Labels := by rfl

theorem canonical7797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7797 raw7797Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw7797 raw7797Labels = mixedMoment B raw7797step0 raw7797step0Labels := by
      have hz : ∀ j, raw7797 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7797step0 = (fun i j => raw7797 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7797step0 raw7797; decide +kernel
      have hl : raw7797step0Labels = raw7797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7797 raw7797Labels permutation434 hz
    mixedMoment B raw7797step0 raw7797step0Labels = mixedMoment B raw7797step1 raw7797step1Labels := by
      have hz : ∀ j, raw7797step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7797step1 = (fun i j => raw7797step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7797step1 raw7797step0; decide +kernel
      have hl : raw7797step1Labels = raw7797step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7797step0 raw7797step0Labels permutation80 hz
    mixedMoment B raw7797step1 raw7797step1Labels = mixedMoment B raw7797step2 raw7797step2Labels := by
      have hz : ∀ j, raw7797step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7797step2 = (fun i j => raw7797step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7797step2 raw7797step1; decide +kernel
      have hl : raw7797step2Labels = raw7797step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7797step1 raw7797step1Labels permutation14 hz
    mixedMoment B raw7797step2 raw7797step2Labels = mixedMoment B raw7797step3 raw7797step3Labels := by
      have ha : raw7797step3 = (fun i j => raw7797step2 (permutation5 i) (permutation0 j)) := by apply Matrix.ext; unfold raw7797step3 raw7797step2; decide +kernel
      have hl : raw7797step3Labels = raw7797step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7797step2 raw7797step2Labels permutation5 permutation0
    mixedMoment B raw7797step3 raw7797step3Labels = mixedMoment B raw7797step4 raw7797step4Labels := by
      have ha : raw7797step4 = -raw7797step3 := by apply Matrix.ext; change ∀ i j, raw7797step4 i j = -(raw7797step3 i j); unfold raw7797step4 raw7797step3; decide +kernel
      have hl : raw7797step4Labels = raw7797step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical7798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7798 raw7798Labels = mixedMoment B node2597 node2597Labels := by
  calc
    mixedMoment B raw7798 raw7798Labels = mixedMoment B raw7798step0 raw7798step0Labels := by
      have hz : ∀ j, raw7798 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7798step0 = (fun i j => raw7798 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7798step0 raw7798; decide +kernel
      have hl : raw7798step0Labels = raw7798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7798 raw7798Labels permutation434 hz
    mixedMoment B raw7798step0 raw7798step0Labels = mixedMoment B raw7798step1 raw7798step1Labels := by
      have ha : raw7798step1 = (fun i j => raw7798step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7798step1 raw7798step0; decide +kernel
      have hl : raw7798step1Labels = raw7798step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7798step0 raw7798step0Labels permutation38 permutation2
    _ = mixedMoment B node2597 node2597Labels := by rfl

theorem canonical7799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7799 raw7799Labels = mixedMoment B node2597 node2597Labels := by
  calc
    mixedMoment B raw7799 raw7799Labels = mixedMoment B raw7799step0 raw7799step0Labels := by
      have hz : ∀ j, raw7799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7799step0 = (fun i j => raw7799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7799step0 raw7799; decide +kernel
      have hl : raw7799step0Labels = raw7799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7799 raw7799Labels permutation346 hz
    mixedMoment B raw7799step0 raw7799step0Labels = mixedMoment B raw7799step1 raw7799step1Labels := by
      have ha : raw7799step1 = (fun i j => raw7799step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7799step1 raw7799step0; decide +kernel
      have hl : raw7799step1Labels = raw7799step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7799step0 raw7799step0Labels permutation38 permutation2
    _ = mixedMoment B node2597 node2597Labels := by rfl

theorem canonical7800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7800 raw7800Labels = mixedMoment B node2134 node2134Labels := by
  calc
    mixedMoment B raw7800 raw7800Labels = mixedMoment B raw7800step0 raw7800step0Labels := by
      have hz : ∀ j, raw7800 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7800step0 = (fun i j => raw7800 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7800step0 raw7800; decide +kernel
      have hl : raw7800step0Labels = raw7800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7800 raw7800Labels permutation434 hz
    mixedMoment B raw7800step0 raw7800step0Labels = mixedMoment B raw7800step1 raw7800step1Labels := by
      have hz : ∀ j, raw7800step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7800step1 = (fun i j => raw7800step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7800step1 raw7800step0; decide +kernel
      have hl : raw7800step1Labels = raw7800step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7800step0 raw7800step0Labels permutation80 hz
    mixedMoment B raw7800step1 raw7800step1Labels = mixedMoment B raw7800step2 raw7800step2Labels := by
      have ha : raw7800step2 = (fun i j => raw7800step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7800step2 raw7800step1; decide +kernel
      have hl : raw7800step2Labels = raw7800step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7800step1 raw7800step1Labels permutation20 permutation4
    mixedMoment B raw7800step2 raw7800step2Labels = mixedMoment B raw7800step3 raw7800step3Labels := by
      have ha : raw7800step3 = -raw7800step2 := by apply Matrix.ext; change ∀ i j, raw7800step3 i j = -(raw7800step2 i j); unfold raw7800step3 raw7800step2; decide +kernel
      have hl : raw7800step3Labels = raw7800step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2134 node2134Labels := by rfl

theorem canonical7801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7801 raw7801Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw7801 raw7801Labels = mixedMoment B raw7801step0 raw7801step0Labels := by
      have hz : ∀ j, raw7801 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7801step0 = (fun i j => raw7801 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7801step0 raw7801; decide +kernel
      have hl : raw7801step0Labels = raw7801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7801 raw7801Labels permutation434 hz
    mixedMoment B raw7801step0 raw7801step0Labels = mixedMoment B raw7801step1 raw7801step1Labels := by
      have hz : ∀ j, raw7801step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7801step1 = (fun i j => raw7801step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7801step1 raw7801step0; decide +kernel
      have hl : raw7801step1Labels = raw7801step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7801step0 raw7801step0Labels permutation80 hz
    mixedMoment B raw7801step1 raw7801step1Labels = mixedMoment B raw7801step2 raw7801step2Labels := by
      have ha : raw7801step2 = (fun i j => raw7801step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7801step2 raw7801step1; decide +kernel
      have hl : raw7801step2Labels = raw7801step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7801step1 raw7801step1Labels permutation12 permutation2
    _ = mixedMoment B node2781 node2781Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical556 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw556 = injectiveMoment H node37 := by
  calc
    injectiveMoment H raw556 = injectiveMoment H raw556step0 := by
      have heq : raw556step0 = (fun i j => raw556 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw556 permutation7 permutation6
    _ = injectiveMoment H node37 := by rfl

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

theorem canonical900 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw900 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw900 = injectiveMoment H raw900step0 := by
      have hz : ∀ j, raw900 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw900step0 = (fun i j => raw900 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw900 permutation5 hz
    _ = injectiveMoment H node3 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical280
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8985 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8985 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8985 = injectiveMoment H raw8985step0 := by
      have hz : ∀ j, raw8985 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw8985step0 = (fun i j => raw8985 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8985 permutation3 hz
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

theorem canonical5210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5210 = injectiveMoment H node4 := by
  rfl

theorem canonical5214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5214 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw5214 = injectiveMoment H raw5214step0 := by
      have hz : ∀ j, raw5214 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw5214step0 = (fun i j => raw5214 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5214 permutation7 hz
    _ = injectiveMoment H node4 := by rfl

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

theorem canonical7683 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7683 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7683 = injectiveMoment H raw7683step0 := by
      have heq : raw7683step0 = (fun i j => raw7683 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7683 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

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

theorem canonical813 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw813 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw813 = injectiveMoment H raw813step0 := by
      have heq : raw813step0 = -raw813 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw813).symm
    injectiveMoment H raw813step0 = injectiveMoment H raw813step1 := by
      have heq : raw813step1 = (fun i j => raw813step0 (permutation4 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw813step0 permutation4 permutation8
    _ = injectiveMoment H node36 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair270 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node270 node270Labels = Sparse.eval singlePairValue270 (familyPairVector B) := by
  have hp := single_label_three B hB node270
  have hl : node270Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node270 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node270 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node270 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node270 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node270 (EqualityPatterns.family3.label 1) = PairSemantics.raw924 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node270 PairSemantics.raw924; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical924 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node270 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node270 (EqualityPatterns.family3.label 2) = PairSemantics.raw8985 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node270 PairSemantics.raw8985; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8985 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node270 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node270 (EqualityPatterns.family3.label 3) = PairSemantics.raw900 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node270 PairSemantics.raw900; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical900 hH).trans (PairSemantics.sound3 hH)
  have hm4 : familyPairMoment B (groupedColumns node270 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value37 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node270 (EqualityPatterns.family3.label 4) = PairSemantics.raw556 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node270 PairSemantics.raw556; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical556 hH).trans (PairSemantics.sound37 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue270, PairSemantics.value0, PairSemantics.value3, PairSemantics.value4, PairSemantics.value10, PairSemantics.value37, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SinglePriority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair420 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node420 node420Labels = Sparse.eval singlePairValue420 (familyPairVector B) := by
  have hp := single_label_three B hB node420
  have hl : node420Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node420 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node420 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node420 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node420 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node420 (EqualityPatterns.family3.label 1) = PairSemantics.raw5214 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node420 PairSemantics.raw5214; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5214 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node420 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node420 (EqualityPatterns.family3.label 2) = PairSemantics.raw7683 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node420 PairSemantics.raw7683; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7683 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node420 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node420 (EqualityPatterns.family3.label 3) = PairSemantics.raw917 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node420 PairSemantics.raw917; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical917 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node420 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value36 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node420 (EqualityPatterns.family3.label 4) = PairSemantics.raw813 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node420 PairSemantics.raw813; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical813 hH).trans (PairSemantics.sound36 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue420, PairSemantics.value0, PairSemantics.value4, PairSemantics.value10, PairSemantics.value11, PairSemantics.value36, Sparse.eval] at hp ⊢
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

theorem singleton2778 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2778 node2778Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node270 node270Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw280 singletonSmall2778
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2778) = raw280Labels := by decide +kernel
  rw [hl, canonical280 B hB] at h
  have hc0 : mixedMoment B raw280 (Fin.cases (0 : Fin 1) singletonSmall2778) =
      mixedMoment B node270 node270Labels := by
    have ha : raw280 = raw281 := by apply Matrix.ext; unfold raw280 raw281; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2778 = raw281Labels := by decide +kernel
    rw [ha, hj, canonical281 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3121 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3121 node3121Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node420 node420Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw404 singletonSmall3121
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3121) = raw404Labels := by decide +kernel
  rw [hl, canonical404 B hB] at h
  have hc0 : mixedMoment B raw404 (Fin.cases (0 : Fin 1) singletonSmall3121) =
      mixedMoment B node420 node420Labels := by
    have ha : raw404 = raw405 := by apply Matrix.ext; unfold raw404 raw405; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3121 = raw405Labels := by decide +kernel
    rw [ha, hj, canonical405 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
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

theorem sound420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node420 node420Labels = Sparse.eval nodeValue420 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue420 (familyPairVector B) := singlePair420 B _hB
    _ = _ := by norm_num [singlePairValue420, nodeValue420, Sparse.eval, mixedVector] <;> ring

theorem sound3633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3633 node3633Labels = Sparse.eval nodeValue3633 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3633) = mixedMoment B node3633 node3633Labels := rfl
  simpa [nodeValue3633, Sparse.eval] using hc.symm

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

theorem sound1088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1088 node1088Labels = Sparse.eval nodeValue1088 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1088) = mixedMoment B node1088 node1088Labels := rfl
  simpa [nodeValue1088, Sparse.eval] using hc.symm

theorem sound1092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1092 node1092Labels = Sparse.eval nodeValue1092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1092) = mixedMoment B node1092 node1092Labels := rfl
  simpa [nodeValue1092, Sparse.eval] using hc.symm

theorem sound1093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1093 node1093Labels = Sparse.eval nodeValue1093 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1093) = mixedMoment B node1093 node1093Labels := rfl
  simpa [nodeValue1093, Sparse.eval] using hc.symm

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

theorem sound1303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1303 node1303Labels = Sparse.eval nodeValue1303 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1303) = mixedMoment B node1303 node1303Labels := rfl
  simpa [nodeValue1303, Sparse.eval] using hc.symm

theorem sound1309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1309 node1309Labels = Sparse.eval nodeValue1309 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1309) = mixedMoment B node1309 node1309Labels := rfl
  simpa [nodeValue1309, Sparse.eval] using hc.symm

theorem sound1310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1310 node1310Labels = Sparse.eval nodeValue1310 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1310) = mixedMoment B node1310 node1310Labels := rfl
  simpa [nodeValue1310, Sparse.eval] using hc.symm

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

theorem sound2033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2033 node2033Labels = Sparse.eval nodeValue2033 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2033) = mixedMoment B node2033 node2033Labels := rfl
  simpa [nodeValue2033, Sparse.eval] using hc.symm

theorem sound2034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2034 node2034Labels = Sparse.eval nodeValue2034 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2034) = mixedMoment B node2034 node2034Labels := rfl
  simpa [nodeValue2034, Sparse.eval] using hc.symm

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

theorem sound2051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2051 node2051Labels = Sparse.eval nodeValue2051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2051) = mixedMoment B node2051 node2051Labels := rfl
  simpa [nodeValue2051, Sparse.eval] using hc.symm

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

theorem sound2134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2134 node2134Labels = Sparse.eval nodeValue2134 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2134) = mixedMoment B node2134 node2134Labels := rfl
  simpa [nodeValue2134, Sparse.eval] using hc.symm

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

theorem sound2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2277 node2277Labels = Sparse.eval nodeValue2277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2277) = mixedMoment B node2277 node2277Labels := rfl
  simpa [nodeValue2277, Sparse.eval] using hc.symm

theorem sound2293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2293 node2293Labels = Sparse.eval nodeValue2293 (mixedVector B) := by
  simpa only [nodeValue2293, Sparse.eval_nil] using zero2293 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node270 node270Labels = Sparse.eval nodeValue270 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue270 (familyPairVector B) := singlePair270 B _hB
    _ = _ := by norm_num [singlePairValue270, nodeValue270, Sparse.eval, mixedVector] <;> ring

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2552 node2552Labels = 0 := by
  exact mixedMoment_alpha B hF node2552 node2552Labels 1 permutation161
    (by decide +kernel)

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

theorem sound2516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2516 node2516Labels = Sparse.eval nodeValue2516 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2516) = mixedMoment B node2516 node2516Labels := rfl
  simpa [nodeValue2516, Sparse.eval] using hc.symm

theorem sound2520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2520 node2520Labels = Sparse.eval nodeValue2520 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2520) = mixedMoment B node2520 node2520Labels := rfl
  simpa [nodeValue2520, Sparse.eval] using hc.symm

theorem sound2521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2521 node2521Labels = Sparse.eval nodeValue2521 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2521) = mixedMoment B node2521 node2521Labels := rfl
  simpa [nodeValue2521, Sparse.eval] using hc.symm

theorem sound2552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2552 node2552Labels = Sparse.eval nodeValue2552 (mixedVector B) := by
  simpa only [nodeValue2552, Sparse.eval_nil] using zero2552 B _hB _hF

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

theorem sound2597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2597 node2597Labels = Sparse.eval nodeValue2597 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2597) = mixedMoment B node2597 node2597Labels := rfl
  simpa [nodeValue2597, Sparse.eval] using hc.symm

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

theorem sound2738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2738 node2738Labels = Sparse.eval nodeValue2738 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2738) = mixedMoment B node2738 node2738Labels := rfl
  simpa [nodeValue2738, Sparse.eval] using hc.symm

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

theorem sound2761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2761 node2761Labels = Sparse.eval nodeValue2761 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2761) = mixedMoment B node2761 node2761Labels := rfl
  simpa [nodeValue2761, Sparse.eval] using hc.symm

theorem sound2777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2777 node2777Labels = Sparse.eval nodeValue2777 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2777) = mixedMoment B node2777 node2777Labels := rfl
  simpa [nodeValue2777, Sparse.eval] using hc.symm

theorem sound2778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2778 node2778Labels = Sparse.eval nodeValue2778 (mixedVector B) := by
  have h := singleton2778 B _hB
  rw [sound270 B _hB _hF] at h
  norm_num [nodeValue2778, nodeValue270, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2780 node2780Labels = Sparse.eval nodeValue2780 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2780) = mixedMoment B node2780 node2780Labels := rfl
  simpa [nodeValue2780, Sparse.eval] using hc.symm

theorem sound2781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2781 node2781Labels = Sparse.eval nodeValue2781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2781) = mixedMoment B node2781 node2781Labels := rfl
  simpa [nodeValue2781, Sparse.eval] using hc.symm

theorem sound2783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2783 node2783Labels = Sparse.eval nodeValue2783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2783) = mixedMoment B node2783 node2783Labels := rfl
  simpa [nodeValue2783, Sparse.eval] using hc.symm

theorem sound2789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2789 node2789Labels = Sparse.eval nodeValue2789 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2789) = mixedMoment B node2789 node2789Labels := rfl
  simpa [nodeValue2789, Sparse.eval] using hc.symm

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

theorem sound3098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3098 node3098Labels = Sparse.eval nodeValue3098 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3098) = mixedMoment B node3098 node3098Labels := rfl
  simpa [nodeValue3098, Sparse.eval] using hc.symm

theorem sound3121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3121 node3121Labels = Sparse.eval nodeValue3121 (mixedVector B) := by
  have h := singleton3121 B _hB
  rw [sound420 B _hB _hF] at h
  norm_num [nodeValue3121, nodeValue420, Sparse.eval] at h ⊢
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

theorem sound3488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3488 node3488Labels = Sparse.eval nodeValue3488 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3488) = mixedMoment B node3488 node3488Labels := rfl
  simpa [nodeValue3488, Sparse.eval] using hc.symm

theorem sound3493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3493 node3493Labels = Sparse.eval nodeValue3493 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3493) = mixedMoment B node3493 node3493Labels := rfl
  simpa [nodeValue3493, Sparse.eval] using hc.symm

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

theorem sound3533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3533 node3533Labels = Sparse.eval nodeValue3533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3533) = mixedMoment B node3533 node3533Labels := rfl
  simpa [nodeValue3533, Sparse.eval] using hc.symm

theorem sound3539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3539 node3539Labels = Sparse.eval nodeValue3539 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3539) = mixedMoment B node3539 node3539Labels := rfl
  simpa [nodeValue3539, Sparse.eval] using hc.symm

theorem sound3548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3548 node3548Labels = Sparse.eval nodeValue3548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3548) = mixedMoment B node3548 node3548Labels := rfl
  simpa [nodeValue3548, Sparse.eval] using hc.symm

theorem sound3582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3582 node3582Labels = Sparse.eval nodeValue3582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3582) = mixedMoment B node3582 node3582Labels := rfl
  simpa [nodeValue3582, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3629 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3629 node3629Labels = 0 := by
  exact mixedMoment_order_one B hB node3629 node3629Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3635 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3635 node3635Labels = 0 := by
  exact mixedMoment_order_one B hB node3635 node3635Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3625 node3625Labels = Sparse.eval nodeValue3625 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3625) = mixedMoment B node3625 node3625Labels := rfl
  simpa [nodeValue3625, Sparse.eval] using hc.symm

theorem sound3629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3629 node3629Labels = Sparse.eval nodeValue3629 (mixedVector B) := by
  simpa only [nodeValue3629, Sparse.eval_nil] using zero3629 B _hB _hF

theorem sound3632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3632 node3632Labels = Sparse.eval nodeValue3632 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3632) = mixedMoment B node3632 node3632Labels := rfl
  simpa [nodeValue3632, Sparse.eval] using hc.symm

theorem sound3635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3635 node3635Labels = Sparse.eval nodeValue3635 (mixedVector B) := by
  simpa only [nodeValue3635, Sparse.eval_nil] using zero3635 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources12
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq401 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm401 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA401 + difference 0 0) (sourceB401 + difference 0 0) sourceC401) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA401 + difference 0 0) (sourceB401 + difference 0 0) sourceC401) = raw6450 := by
      apply Matrix.ext; unfold tripleCharges sourceA401 sourceB401 sourceC401 difference raw6450; decide +kernel
    rw [ha]
    exact (canonical6450 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA401 + difference 0 1) (sourceB401 + difference 1 0) sourceC401) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3488) := by
    have ha : (tripleCharges (sourceA401 + difference 0 1) (sourceB401 + difference 1 0) sourceC401) = raw7551 := by
      apply Matrix.ext; unfold tripleCharges sourceA401 sourceB401 sourceC401 difference raw7551; decide +kernel
    rw [ha]
    exact (canonical7551 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA401 + difference 0 2) (sourceB401 + difference 2 0) sourceC401) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA401 + difference 0 2) (sourceB401 + difference 2 0) sourceC401) = raw6437 := by
      apply Matrix.ext; unfold tripleCharges sourceA401 sourceB401 sourceC401 difference raw6437; decide +kernel
    rw [ha]
    exact (canonical6437 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA401 + difference 0 3) (sourceB401 + difference 3 0) sourceC401) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA401 + difference 0 3) (sourceB401 + difference 3 0) sourceC401) = raw7552 := by
      apply Matrix.ext; unfold tripleCharges sourceA401 sourceB401 sourceC401 difference raw7552; decide +kernel
    rw [ha]
    exact (canonical7552 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA401 + difference 0 4) (sourceB401 + difference 4 0) sourceC401) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3493) := by
    have ha : (tripleCharges (sourceA401 + difference 0 4) (sourceB401 + difference 4 0) sourceC401) = raw7278 := by
      apply Matrix.ext; unfold tripleCharges sourceA401 sourceB401 sourceC401 difference raw7278; decide +kernel
    rw [ha]
    exact (canonical7278 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA401 + difference 0 5) (sourceB401 + difference 5 0) sourceC401) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2552) := by
    have ha : (tripleCharges (sourceA401 + difference 0 5) (sourceB401 + difference 5 0) sourceC401) = raw7553 := by
      apply Matrix.ext; unfold tripleCharges sourceA401 sourceB401 sourceC401 difference raw7553; decide +kernel
    rw [ha]
    exact (canonical7553 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA401 + sourceB401) sourceC401) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA401 + sourceB401) sourceC401) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA401 sourceB401 sourceC401 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA401 sourceB401 sourceC401
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm401, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq402 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm402 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA402 + difference 0 0) (sourceB402 + difference 0 0) sourceC402) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA402 + difference 0 0) (sourceB402 + difference 0 0) sourceC402) = raw6450 := by
      apply Matrix.ext; unfold tripleCharges sourceA402 sourceB402 sourceC402 difference raw6450; decide +kernel
    rw [ha]
    exact (canonical6450 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA402 + difference 1 0) (sourceB402 + difference 0 1) sourceC402) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA402 + difference 1 0) (sourceB402 + difference 0 1) sourceC402) = raw5760 := by
      apply Matrix.ext; unfold tripleCharges sourceA402 sourceB402 sourceC402 difference raw5760; decide +kernel
    rw [ha]
    exact (canonical5760 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA402 + difference 2 0) (sourceB402 + difference 0 2) sourceC402) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2034) := by
    have ha : (tripleCharges (sourceA402 + difference 2 0) (sourceB402 + difference 0 2) sourceC402) = raw7554 := by
      apply Matrix.ext; unfold tripleCharges sourceA402 sourceB402 sourceC402 difference raw7554; decide +kernel
    rw [ha]
    exact (canonical7554 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA402 + difference 3 0) (sourceB402 + difference 0 3) sourceC402) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2034) := by
    have ha : (tripleCharges (sourceA402 + difference 3 0) (sourceB402 + difference 0 3) sourceC402) = raw7096 := by
      apply Matrix.ext; unfold tripleCharges sourceA402 sourceB402 sourceC402 difference raw7096; decide +kernel
    rw [ha]
    exact (canonical7096 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA402 + difference 4 0) (sourceB402 + difference 0 4) sourceC402) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2033) := by
    have ha : (tripleCharges (sourceA402 + difference 4 0) (sourceB402 + difference 0 4) sourceC402) = raw6440 := by
      apply Matrix.ext; unfold tripleCharges sourceA402 sourceB402 sourceC402 difference raw6440; decide +kernel
    rw [ha]
    exact (canonical6440 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA402 + difference 5 0) (sourceB402 + difference 0 5) sourceC402) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2051) := by
    have ha : (tripleCharges (sourceA402 + difference 5 0) (sourceB402 + difference 0 5) sourceC402) = raw7280 := by
      apply Matrix.ext; unfold tripleCharges sourceA402 sourceB402 sourceC402 difference raw7280; decide +kernel
    rw [ha]
    exact (canonical7280 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA402 + sourceB402) sourceC402) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA402 + sourceB402) sourceC402) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA402 sourceB402 sourceC402 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA402 sourceB402 sourceC402
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm402, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq403 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm403 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA403 + difference 1 0) (sourceB403 + difference 0 1) sourceC403) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA403 + difference 1 0) (sourceB403 + difference 0 1) sourceC403) = raw5760 := by
      apply Matrix.ext; unfold tripleCharges sourceA403 sourceB403 sourceC403 difference raw5760; decide +kernel
    rw [ha]
    exact (canonical5760 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA403 + difference 1 1) (sourceB403 + difference 1 1) sourceC403) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA403 + difference 1 1) (sourceB403 + difference 1 1) sourceC403) = raw6450 := by
      apply Matrix.ext; unfold tripleCharges sourceA403 sourceB403 sourceC403 difference raw6450; decide +kernel
    rw [ha]
    exact (canonical6450 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA403 + difference 1 2) (sourceB403 + difference 2 1) sourceC403) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3632) := by
    have ha : (tripleCharges (sourceA403 + difference 1 2) (sourceB403 + difference 2 1) sourceC403) = raw6445 := by
      apply Matrix.ext; unfold tripleCharges sourceA403 sourceB403 sourceC403 difference raw6445; decide +kernel
    rw [ha]
    exact (canonical6445 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA403 + difference 1 3) (sourceB403 + difference 3 1) sourceC403) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3632) := by
    have ha : (tripleCharges (sourceA403 + difference 1 3) (sourceB403 + difference 3 1) sourceC403) = raw7555 := by
      apply Matrix.ext; unfold tripleCharges sourceA403 sourceB403 sourceC403 difference raw7555; decide +kernel
    rw [ha]
    exact (canonical7555 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA403 + difference 1 4) (sourceB403 + difference 4 1) sourceC403) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA403 + difference 1 4) (sourceB403 + difference 4 1) sourceC403) = raw5749 := by
      apply Matrix.ext; unfold tripleCharges sourceA403 sourceB403 sourceC403 difference raw5749; decide +kernel
    rw [ha]
    exact (canonical5749 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA403 + difference 1 5) (sourceB403 + difference 5 1) sourceC403) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA403 + difference 1 5) (sourceB403 + difference 5 1) sourceC403) = raw7556 := by
      apply Matrix.ext; unfold tripleCharges sourceA403 sourceB403 sourceC403 difference raw7556; decide +kernel
    rw [ha]
    exact (canonical7556 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA403 + sourceB403) sourceC403) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA403 + sourceB403) sourceC403) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA403 sourceB403 sourceC403 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA403 sourceB403 sourceC403
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm403, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq412 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm412 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA412 + difference 0 0) (sourceB412 + difference 0 0) sourceC412) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3633) := by
    have ha : (tripleCharges (sourceA412 + difference 0 0) (sourceB412 + difference 0 0) sourceC412) = raw6121 := by
      apply Matrix.ext; unfold tripleCharges sourceA412 sourceB412 sourceC412 difference raw6121; decide +kernel
    rw [ha]
    exact (canonical6121 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA412 + difference 0 1) (sourceB412 + difference 1 0) sourceC412) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA412 + difference 0 1) (sourceB412 + difference 1 0) sourceC412) = raw6104 := by
      apply Matrix.ext; unfold tripleCharges sourceA412 sourceB412 sourceC412 difference raw6104; decide +kernel
    rw [ha]
    exact (canonical6104 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA412 + difference 0 2) (sourceB412 + difference 2 0) sourceC412) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA412 + difference 0 2) (sourceB412 + difference 2 0) sourceC412) = raw7692 := by
      apply Matrix.ext; unfold tripleCharges sourceA412 sourceB412 sourceC412 difference raw7692; decide +kernel
    rw [ha]
    exact (canonical7692 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA412 + difference 0 3) (sourceB412 + difference 3 0) sourceC412) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA412 + difference 0 3) (sourceB412 + difference 3 0) sourceC412) = raw7693 := by
      apply Matrix.ext; unfold tripleCharges sourceA412 sourceB412 sourceC412 difference raw7693; decide +kernel
    rw [ha]
    exact (canonical7693 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA412 + difference 0 4) (sourceB412 + difference 4 0) sourceC412) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3629) := by
    have ha : (tripleCharges (sourceA412 + difference 0 4) (sourceB412 + difference 4 0) sourceC412) = raw7694 := by
      apply Matrix.ext; unfold tripleCharges sourceA412 sourceB412 sourceC412 difference raw7694; decide +kernel
    rw [ha]
    exact (canonical7694 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA412 + difference 0 5) (sourceB412 + difference 5 0) sourceC412) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2783) := by
    have ha : (tripleCharges (sourceA412 + difference 0 5) (sourceB412 + difference 5 0) sourceC412) = raw7695 := by
      apply Matrix.ext; unfold tripleCharges sourceA412 sourceB412 sourceC412 difference raw7695; decide +kernel
    rw [ha]
    exact (canonical7695 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA412 + sourceB412) sourceC412) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA412 + sourceB412) sourceC412) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA412 sourceB412 sourceC412 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA412 sourceB412 sourceC412
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm412, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq413 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm413 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA413 + difference 0 4) (sourceB413 + difference 4 0) sourceC413) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3629) := by
    have ha : (tripleCharges (sourceA413 + difference 0 4) (sourceB413 + difference 4 0) sourceC413) = raw7694 := by
      apply Matrix.ext; unfold tripleCharges sourceA413 sourceB413 sourceC413 difference raw7694; decide +kernel
    rw [ha]
    exact (canonical7694 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA413 + difference 1 4) (sourceB413 + difference 4 1) sourceC413) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3632) := by
    have ha : (tripleCharges (sourceA413 + difference 1 4) (sourceB413 + difference 4 1) sourceC413) = raw7696 := by
      apply Matrix.ext; unfold tripleCharges sourceA413 sourceB413 sourceC413 difference raw7696; decide +kernel
    rw [ha]
    exact (canonical7696 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA413 + difference 2 4) (sourceB413 + difference 4 2) sourceC413) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3632) := by
    have ha : (tripleCharges (sourceA413 + difference 2 4) (sourceB413 + difference 4 2) sourceC413) = raw7555 := by
      apply Matrix.ext; unfold tripleCharges sourceA413 sourceB413 sourceC413 difference raw7555; decide +kernel
    rw [ha]
    exact (canonical7555 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA413 + difference 3 4) (sourceB413 + difference 4 3) sourceC413) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3632) := by
    have ha : (tripleCharges (sourceA413 + difference 3 4) (sourceB413 + difference 4 3) sourceC413) = raw6445 := by
      apply Matrix.ext; unfold tripleCharges sourceA413 sourceB413 sourceC413 difference raw6445; decide +kernel
    rw [ha]
    exact (canonical6445 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA413 + difference 4 4) (sourceB413 + difference 4 4) sourceC413) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3633) := by
    have ha : (tripleCharges (sourceA413 + difference 4 4) (sourceB413 + difference 4 4) sourceC413) = raw6121 := by
      apply Matrix.ext; unfold tripleCharges sourceA413 sourceB413 sourceC413 difference raw6121; decide +kernel
    rw [ha]
    exact (canonical6121 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA413 + difference 5 4) (sourceB413 + difference 4 5) sourceC413) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3635) := by
    have ha : (tripleCharges (sourceA413 + difference 5 4) (sourceB413 + difference 4 5) sourceC413) = raw7697 := by
      apply Matrix.ext; unfold tripleCharges sourceA413 sourceB413 sourceC413 difference raw7697; decide +kernel
    rw [ha]
    exact (canonical7697 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA413 + sourceB413) sourceC413) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA413 + sourceB413) sourceC413) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA413 sourceB413 sourceC413 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA413 sourceB413 sourceC413
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm413, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq414 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm414 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA414 + difference 5 0) (sourceB414 + difference 0 5) sourceC414) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA414 + difference 5 0) (sourceB414 + difference 0 5) sourceC414) = raw7698 := by
      apply Matrix.ext; unfold tripleCharges sourceA414 sourceB414 sourceC414 difference raw7698; decide +kernel
    rw [ha]
    exact (canonical7698 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA414 + difference 5 1) (sourceB414 + difference 1 5) sourceC414) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA414 + difference 5 1) (sourceB414 + difference 1 5) sourceC414) = raw6123 := by
      apply Matrix.ext; unfold tripleCharges sourceA414 sourceB414 sourceC414 difference raw6123; decide +kernel
    rw [ha]
    exact (canonical6123 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA414 + difference 5 2) (sourceB414 + difference 2 5) sourceC414) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA414 + difference 5 2) (sourceB414 + difference 2 5) sourceC414) = raw7699 := by
      apply Matrix.ext; unfold tripleCharges sourceA414 sourceB414 sourceC414 difference raw7699; decide +kernel
    rw [ha]
    exact (canonical7699 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA414 + difference 5 3) (sourceB414 + difference 3 5) sourceC414) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA414 + difference 5 3) (sourceB414 + difference 3 5) sourceC414) = raw7700 := by
      apply Matrix.ext; unfold tripleCharges sourceA414 sourceB414 sourceC414 difference raw7700; decide +kernel
    rw [ha]
    exact (canonical7700 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA414 + difference 5 4) (sourceB414 + difference 4 5) sourceC414) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3635) := by
    have ha : (tripleCharges (sourceA414 + difference 5 4) (sourceB414 + difference 4 5) sourceC414) = raw7697 := by
      apply Matrix.ext; unfold tripleCharges sourceA414 sourceB414 sourceC414 difference raw7697; decide +kernel
    rw [ha]
    exact (canonical7697 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA414 + difference 5 5) (sourceB414 + difference 5 5) sourceC414) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3633) := by
    have ha : (tripleCharges (sourceA414 + difference 5 5) (sourceB414 + difference 5 5) sourceC414) = raw6121 := by
      apply Matrix.ext; unfold tripleCharges sourceA414 sourceB414 sourceC414 difference raw6121; decide +kernel
    rw [ha]
    exact (canonical6121 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA414 + sourceB414) sourceC414) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA414 + sourceB414) sourceC414) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA414 sourceB414 sourceC414 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA414 sourceB414 sourceC414
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm414, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources13
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq417 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm417 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA417 + difference 0 1) (sourceB417 + difference 1 0) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA417 + difference 0 1) (sourceB417 + difference 1 0) sourceC417) = raw7761 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7761; decide +kernel
    rw [ha]
    exact (canonical7761 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA417 + difference 0 2) (sourceB417 + difference 2 0) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA417 + difference 0 2) (sourceB417 + difference 2 0) sourceC417) = raw7762 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7762; decide +kernel
    rw [ha]
    exact (canonical7762 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA417 + difference 0 3) (sourceB417 + difference 3 0) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA417 + difference 0 3) (sourceB417 + difference 3 0) sourceC417) = raw7763 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7763; decide +kernel
    rw [ha]
    exact (canonical7763 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA417 + difference 0 4) (sourceB417 + difference 4 0) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2778) := by
    have ha : (tripleCharges (sourceA417 + difference 0 4) (sourceB417 + difference 4 0) sourceC417) = raw7764 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7764; decide +kernel
    rw [ha]
    exact (canonical7764 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA417 + difference 0 5) (sourceB417 + difference 5 0) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3121) := by
    have ha : (tripleCharges (sourceA417 + difference 0 5) (sourceB417 + difference 5 0) sourceC417) = raw7765 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7765; decide +kernel
    rw [ha]
    exact (canonical7765 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA417 + difference 1 0) (sourceB417 + difference 0 1) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2521) := by
    have ha : (tripleCharges (sourceA417 + difference 1 0) (sourceB417 + difference 0 1) sourceC417) = raw7766 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7766; decide +kernel
    rw [ha]
    exact (canonical7766 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA417 + difference 1 2) (sourceB417 + difference 2 1) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2516) := by
    have ha : (tripleCharges (sourceA417 + difference 1 2) (sourceB417 + difference 2 1) sourceC417) = raw7767 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7767; decide +kernel
    rw [ha]
    exact (canonical7767 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA417 + difference 1 3) (sourceB417 + difference 3 1) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2516) := by
    have ha : (tripleCharges (sourceA417 + difference 1 3) (sourceB417 + difference 3 1) sourceC417) = raw7768 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7768; decide +kernel
    rw [ha]
    exact (canonical7768 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA417 + difference 1 4) (sourceB417 + difference 4 1) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2520) := by
    have ha : (tripleCharges (sourceA417 + difference 1 4) (sourceB417 + difference 4 1) sourceC417) = raw7769 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7769; decide +kernel
    rw [ha]
    exact (canonical7769 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA417 + difference 1 5) (sourceB417 + difference 5 1) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA417 + difference 1 5) (sourceB417 + difference 5 1) sourceC417) = raw7770 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7770; decide +kernel
    rw [ha]
    exact (canonical7770 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA417 + difference 2 0) (sourceB417 + difference 0 2) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2521) := by
    have ha : (tripleCharges (sourceA417 + difference 2 0) (sourceB417 + difference 0 2) sourceC417) = raw7771 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7771; decide +kernel
    rw [ha]
    exact (canonical7771 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA417 + difference 2 1) (sourceB417 + difference 1 2) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2516) := by
    have ha : (tripleCharges (sourceA417 + difference 2 1) (sourceB417 + difference 1 2) sourceC417) = raw7772 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7772; decide +kernel
    rw [ha]
    exact (canonical7772 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA417 + difference 2 3) (sourceB417 + difference 3 2) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2516) := by
    have ha : (tripleCharges (sourceA417 + difference 2 3) (sourceB417 + difference 3 2) sourceC417) = raw7773 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7773; decide +kernel
    rw [ha]
    exact (canonical7773 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA417 + difference 2 4) (sourceB417 + difference 4 2) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2520) := by
    have ha : (tripleCharges (sourceA417 + difference 2 4) (sourceB417 + difference 4 2) sourceC417) = raw7774 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7774; decide +kernel
    rw [ha]
    exact (canonical7774 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA417 + difference 2 5) (sourceB417 + difference 5 2) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA417 + difference 2 5) (sourceB417 + difference 5 2) sourceC417) = raw7775 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7775; decide +kernel
    rw [ha]
    exact (canonical7775 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA417 + difference 3 0) (sourceB417 + difference 0 3) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2521) := by
    have ha : (tripleCharges (sourceA417 + difference 3 0) (sourceB417 + difference 0 3) sourceC417) = raw7776 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7776; decide +kernel
    rw [ha]
    exact (canonical7776 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA417 + difference 3 1) (sourceB417 + difference 1 3) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2516) := by
    have ha : (tripleCharges (sourceA417 + difference 3 1) (sourceB417 + difference 1 3) sourceC417) = raw7777 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7777; decide +kernel
    rw [ha]
    exact (canonical7777 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA417 + difference 3 2) (sourceB417 + difference 2 3) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2516) := by
    have ha : (tripleCharges (sourceA417 + difference 3 2) (sourceB417 + difference 2 3) sourceC417) = raw7778 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7778; decide +kernel
    rw [ha]
    exact (canonical7778 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA417 + difference 3 4) (sourceB417 + difference 4 3) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2520) := by
    have ha : (tripleCharges (sourceA417 + difference 3 4) (sourceB417 + difference 4 3) sourceC417) = raw7779 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7779; decide +kernel
    rw [ha]
    exact (canonical7779 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA417 + difference 3 5) (sourceB417 + difference 5 3) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA417 + difference 3 5) (sourceB417 + difference 5 3) sourceC417) = raw7780 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7780; decide +kernel
    rw [ha]
    exact (canonical7780 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA417 + difference 4 0) (sourceB417 + difference 0 4) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2780) := by
    have ha : (tripleCharges (sourceA417 + difference 4 0) (sourceB417 + difference 0 4) sourceC417) = raw7781 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7781; decide +kernel
    rw [ha]
    exact (canonical7781 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA417 + difference 4 1) (sourceB417 + difference 1 4) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA417 + difference 4 1) (sourceB417 + difference 1 4) sourceC417) = raw7782 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7782; decide +kernel
    rw [ha]
    exact (canonical7782 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA417 + difference 4 2) (sourceB417 + difference 2 4) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA417 + difference 4 2) (sourceB417 + difference 2 4) sourceC417) = raw7783 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7783; decide +kernel
    rw [ha]
    exact (canonical7783 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA417 + difference 4 3) (sourceB417 + difference 3 4) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA417 + difference 4 3) (sourceB417 + difference 3 4) sourceC417) = raw7784 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7784; decide +kernel
    rw [ha]
    exact (canonical7784 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA417 + difference 4 5) (sourceB417 + difference 5 4) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2783) := by
    have ha : (tripleCharges (sourceA417 + difference 4 5) (sourceB417 + difference 5 4) sourceC417) = raw7785 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7785; decide +kernel
    rw [ha]
    exact (canonical7785 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA417 + difference 5 0) (sourceB417 + difference 0 5) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1093) := by
    have ha : (tripleCharges (sourceA417 + difference 5 0) (sourceB417 + difference 0 5) sourceC417) = raw7786 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7786; decide +kernel
    rw [ha]
    exact (canonical7786 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA417 + difference 5 1) (sourceB417 + difference 1 5) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1088) := by
    have ha : (tripleCharges (sourceA417 + difference 5 1) (sourceB417 + difference 1 5) sourceC417) = raw7787 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7787; decide +kernel
    rw [ha]
    exact (canonical7787 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA417 + difference 5 2) (sourceB417 + difference 2 5) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1088) := by
    have ha : (tripleCharges (sourceA417 + difference 5 2) (sourceB417 + difference 2 5) sourceC417) = raw7788 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7788; decide +kernel
    rw [ha]
    exact (canonical7788 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA417 + difference 5 3) (sourceB417 + difference 3 5) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1088) := by
    have ha : (tripleCharges (sourceA417 + difference 5 3) (sourceB417 + difference 3 5) sourceC417) = raw7789 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7789; decide +kernel
    rw [ha]
    exact (canonical7789 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA417 + difference 5 4) (sourceB417 + difference 4 5) sourceC417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1092) := by
    have ha : (tripleCharges (sourceA417 + difference 5 4) (sourceB417 + difference 4 5) sourceC417) = raw7790 := by
      apply Matrix.ext; unfold tripleCharges sourceA417 sourceB417 sourceC417 difference raw7790; decide +kernel
    rw [ha]
    exact (canonical7790 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA417 sourceB417 sourceC417
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm417, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq418 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm418 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA418 + difference 0 0) (sourceB418 + difference 0 0) sourceC418) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2789) := by
    have ha : (tripleCharges (sourceA418 + difference 0 0) (sourceB418 + difference 0 0) sourceC418) = raw7791 := by
      apply Matrix.ext; unfold tripleCharges sourceA418 sourceB418 sourceC418 difference raw7791; decide +kernel
    rw [ha]
    exact (canonical7791 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA418 + difference 1 0) (sourceB418 + difference 0 1) sourceC418) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1303) := by
    have ha : (tripleCharges (sourceA418 + difference 1 0) (sourceB418 + difference 0 1) sourceC418) = raw7792 := by
      apply Matrix.ext; unfold tripleCharges sourceA418 sourceB418 sourceC418 difference raw7792; decide +kernel
    rw [ha]
    exact (canonical7792 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA418 + difference 2 0) (sourceB418 + difference 0 2) sourceC418) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1303) := by
    have ha : (tripleCharges (sourceA418 + difference 2 0) (sourceB418 + difference 0 2) sourceC418) = raw7793 := by
      apply Matrix.ext; unfold tripleCharges sourceA418 sourceB418 sourceC418 difference raw7793; decide +kernel
    rw [ha]
    exact (canonical7793 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA418 + difference 3 0) (sourceB418 + difference 0 3) sourceC418) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1303) := by
    have ha : (tripleCharges (sourceA418 + difference 3 0) (sourceB418 + difference 0 3) sourceC418) = raw7794 := by
      apply Matrix.ext; unfold tripleCharges sourceA418 sourceB418 sourceC418 difference raw7794; decide +kernel
    rw [ha]
    exact (canonical7794 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA418 + difference 4 0) (sourceB418 + difference 0 4) sourceC418) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1310) := by
    have ha : (tripleCharges (sourceA418 + difference 4 0) (sourceB418 + difference 0 4) sourceC418) = raw7795 := by
      apply Matrix.ext; unfold tripleCharges sourceA418 sourceB418 sourceC418 difference raw7795; decide +kernel
    rw [ha]
    exact (canonical7795 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA418 + difference 5 0) (sourceB418 + difference 0 5) sourceC418) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1309) := by
    have ha : (tripleCharges (sourceA418 + difference 5 0) (sourceB418 + difference 0 5) sourceC418) = raw7796 := by
      apply Matrix.ext; unfold tripleCharges sourceA418 sourceB418 sourceC418 difference raw7796; decide +kernel
    rw [ha]
    exact (canonical7796 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA418 + sourceB418) sourceC418) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA418 + sourceB418) sourceC418) = raw7797 := by
      apply Matrix.ext; unfold doubleCharges sourceA418 sourceB418 sourceC418 raw7797; decide +kernel
    rw [ha]
    exact (canonical7797 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA418 sourceB418 sourceC418
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm418, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq419 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm419 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA419 + difference 1 0) (sourceB419 + difference 0 1) sourceC419) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1303) := by
    have ha : (tripleCharges (sourceA419 + difference 1 0) (sourceB419 + difference 0 1) sourceC419) = raw7792 := by
      apply Matrix.ext; unfold tripleCharges sourceA419 sourceB419 sourceC419 difference raw7792; decide +kernel
    rw [ha]
    exact (canonical7792 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA419 + difference 1 1) (sourceB419 + difference 1 1) sourceC419) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2789) := by
    have ha : (tripleCharges (sourceA419 + difference 1 1) (sourceB419 + difference 1 1) sourceC419) = raw7791 := by
      apply Matrix.ext; unfold tripleCharges sourceA419 sourceB419 sourceC419 difference raw7791; decide +kernel
    rw [ha]
    exact (canonical7791 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA419 + difference 1 2) (sourceB419 + difference 2 1) sourceC419) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2597) := by
    have ha : (tripleCharges (sourceA419 + difference 1 2) (sourceB419 + difference 2 1) sourceC419) = raw7798 := by
      apply Matrix.ext; unfold tripleCharges sourceA419 sourceB419 sourceC419 difference raw7798; decide +kernel
    rw [ha]
    exact (canonical7798 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA419 + difference 1 3) (sourceB419 + difference 3 1) sourceC419) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2597) := by
    have ha : (tripleCharges (sourceA419 + difference 1 3) (sourceB419 + difference 3 1) sourceC419) = raw7799 := by
      apply Matrix.ext; unfold tripleCharges sourceA419 sourceB419 sourceC419 difference raw7799; decide +kernel
    rw [ha]
    exact (canonical7799 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA419 + difference 1 4) (sourceB419 + difference 4 1) sourceC419) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2134) := by
    have ha : (tripleCharges (sourceA419 + difference 1 4) (sourceB419 + difference 4 1) sourceC419) = raw7800 := by
      apply Matrix.ext; unfold tripleCharges sourceA419 sourceB419 sourceC419 difference raw7800; decide +kernel
    rw [ha]
    exact (canonical7800 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA419 + difference 1 5) (sourceB419 + difference 5 1) sourceC419) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA419 + difference 1 5) (sourceB419 + difference 5 1) sourceC419) = raw7801 := by
      apply Matrix.ext; unfold tripleCharges sourceA419 sourceB419 sourceC419 difference raw7801; decide +kernel
    rw [ha]
    exact (canonical7801 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA419 + sourceB419) sourceC419) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA419 + sourceB419) sourceC419) = raw7797 := by
      apply Matrix.ext; unfold doubleCharges sourceA419 sourceB419 sourceC419 raw7797; decide +kernel
    rw [ha]
    exact (canonical7797 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA419 sourceB419 sourceC419
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm419, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck336 : Integer.Sparse.reindex keyMap MixedData.row336 = numericRow336 := by decide +kernel

theorem numericCheck336 (x : Master → ℝ) : Integer.Sparse.eval numericRow336 x =
    (1 : ℝ) * reducedSource336 x := by
  norm_num [numericRow336, reducedSource336, Integer.Sparse.eval, Sparse.eval, nodeValue2552, nodeValue3488, nodeValue3493, nodeValue3533, nodeValue3539, nodeValue4084]

theorem reindexCheck337 : Integer.Sparse.reindex keyMap MixedData.row337 = numericRow337 := by decide +kernel

theorem numericCheck337 (x : Master → ℝ) : Integer.Sparse.eval numericRow337 x =
    (1 : ℝ) * reducedSource337 x := by
  norm_num [numericRow337, reducedSource337, Integer.Sparse.eval, Sparse.eval, nodeValue2033, nodeValue2034, nodeValue2051, nodeValue2277, nodeValue3539, nodeValue4084]

theorem reindexCheck338 : Integer.Sparse.reindex keyMap MixedData.row338 = numericRow338 := by decide +kernel

theorem numericCheck338 (x : Master → ℝ) : Integer.Sparse.eval numericRow338 x =
    (1 : ℝ) * reducedSource338 x := by
  norm_num [numericRow338, reducedSource338, Integer.Sparse.eval, Sparse.eval, nodeValue2277, nodeValue2738, nodeValue3539, nodeValue3625, nodeValue3632, nodeValue4084]

theorem reindexCheck346 : Integer.Sparse.reindex keyMap MixedData.row346 = numericRow346 := by decide +kernel

theorem numericCheck346 (x : Master → ℝ) : Integer.Sparse.eval numericRow346 x =
    (1 : ℝ) * reducedSource346 x := by
  norm_num [numericRow346, reducedSource346, Integer.Sparse.eval, Sparse.eval, nodeValue2783, nodeValue3582, nodeValue3629, nodeValue3633, nodeValue4084]

theorem reindexCheck347 : Integer.Sparse.reindex keyMap MixedData.row347 = numericRow347 := by decide +kernel

theorem numericCheck347 (x : Master → ℝ) : Integer.Sparse.eval numericRow347 x =
    (1 : ℝ) * reducedSource347 x := by
  norm_num [numericRow347, reducedSource347, Integer.Sparse.eval, Sparse.eval, nodeValue3629, nodeValue3632, nodeValue3633, nodeValue3635, nodeValue4084]

theorem reindexCheck348 : Integer.Sparse.reindex keyMap MixedData.row348 = numericRow348 := by decide +kernel

theorem numericCheck348 (x : Master → ℝ) : Integer.Sparse.eval numericRow348 x =
    (1 : ℝ) * reducedSource348 x := by
  norm_num [numericRow348, reducedSource348, Integer.Sparse.eval, Sparse.eval, nodeValue2293, nodeValue3548, nodeValue3633, nodeValue3635, nodeValue4084]

theorem reindexCheck349 : Integer.Sparse.reindex keyMap MixedData.row349 = numericRow349 := by decide +kernel

theorem numericCheck349 (x : Master → ℝ) : Integer.Sparse.eval numericRow349 x =
    (720 : ℝ) * reducedSource349 x := by
  norm_num [numericRow349, reducedSource349, Integer.Sparse.eval, Sparse.eval, nodeValue1088, nodeValue1092, nodeValue1093, nodeValue2516, nodeValue2520, nodeValue2521, nodeValue2761, nodeValue2777, nodeValue2778, nodeValue2780, nodeValue2783, nodeValue3098, nodeValue3121]
  ring

theorem reindexCheck350 : Integer.Sparse.reindex keyMap MixedData.row350 = numericRow350 := by decide +kernel

theorem numericCheck350 (x : Master → ℝ) : Integer.Sparse.eval numericRow350 x =
    (1 : ℝ) * reducedSource350 x := by
  norm_num [numericRow350, reducedSource350, Integer.Sparse.eval, Sparse.eval, nodeValue1303, nodeValue1309, nodeValue1310, nodeValue2789, nodeValue4084]

theorem reindexCheck351 : Integer.Sparse.reindex keyMap MixedData.row351 = numericRow351 := by decide +kernel

theorem numericCheck351 (x : Master → ℝ) : Integer.Sparse.eval numericRow351 x =
    (1 : ℝ) * reducedSource351 x := by
  norm_num [numericRow351, reducedSource351, Integer.Sparse.eval, Sparse.eval, nodeValue1303, nodeValue2134, nodeValue2597, nodeValue2781, nodeValue2789, nodeValue4084]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero336 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource336 (mixedVector B) = 0 := by
  have h2552 : mixedVector B (Sum.inr 2552) = Sparse.eval nodeValue2552 (mixedVector B) := by
    change mixedMoment B node2552 node2552Labels = _
    exact sound2552 B hB hF
  have h3488 : mixedVector B (Sum.inr 3488) = Sparse.eval nodeValue3488 (mixedVector B) := by
    change mixedMoment B node3488 node3488Labels = _
    exact sound3488 B hB hF
  have h3493 : mixedVector B (Sum.inr 3493) = Sparse.eval nodeValue3493 (mixedVector B) := by
    change mixedMoment B node3493 node3493Labels = _
    exact sound3493 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3539 : mixedVector B (Sum.inr 3539) = Sparse.eval nodeValue3539 (mixedVector B) := by
    change mixedMoment B node3539 node3539Labels = _
    exact sound3539 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm401, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2552, h3488, h3493, h3533, h3539, h4084, reducedSource336] using sourceEq401 B hB

theorem rowSound336 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row336 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck336, numericCheck336, reducedZero336 B hB hF, mul_zero]

theorem reducedZero337 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource337 (mixedVector B) = 0 := by
  have h2033 : mixedVector B (Sum.inr 2033) = Sparse.eval nodeValue2033 (mixedVector B) := by
    change mixedMoment B node2033 node2033Labels = _
    exact sound2033 B hB hF
  have h2034 : mixedVector B (Sum.inr 2034) = Sparse.eval nodeValue2034 (mixedVector B) := by
    change mixedMoment B node2034 node2034Labels = _
    exact sound2034 B hB hF
  have h2051 : mixedVector B (Sum.inr 2051) = Sparse.eval nodeValue2051 (mixedVector B) := by
    change mixedMoment B node2051 node2051Labels = _
    exact sound2051 B hB hF
  have h2277 : mixedVector B (Sum.inr 2277) = Sparse.eval nodeValue2277 (mixedVector B) := by
    change mixedMoment B node2277 node2277Labels = _
    exact sound2277 B hB hF
  have h3539 : mixedVector B (Sum.inr 3539) = Sparse.eval nodeValue3539 (mixedVector B) := by
    change mixedMoment B node3539 node3539Labels = _
    exact sound3539 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm402, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2033, h2034, h2051, h2277, h3539, h4084, reducedSource337] using sourceEq402 B hB

theorem rowSound337 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row337 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck337, numericCheck337, reducedZero337 B hB hF, mul_zero]

theorem reducedZero338 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource338 (mixedVector B) = 0 := by
  have h2277 : mixedVector B (Sum.inr 2277) = Sparse.eval nodeValue2277 (mixedVector B) := by
    change mixedMoment B node2277 node2277Labels = _
    exact sound2277 B hB hF
  have h2738 : mixedVector B (Sum.inr 2738) = Sparse.eval nodeValue2738 (mixedVector B) := by
    change mixedMoment B node2738 node2738Labels = _
    exact sound2738 B hB hF
  have h3539 : mixedVector B (Sum.inr 3539) = Sparse.eval nodeValue3539 (mixedVector B) := by
    change mixedMoment B node3539 node3539Labels = _
    exact sound3539 B hB hF
  have h3625 : mixedVector B (Sum.inr 3625) = Sparse.eval nodeValue3625 (mixedVector B) := by
    change mixedMoment B node3625 node3625Labels = _
    exact sound3625 B hB hF
  have h3632 : mixedVector B (Sum.inr 3632) = Sparse.eval nodeValue3632 (mixedVector B) := by
    change mixedMoment B node3632 node3632Labels = _
    exact sound3632 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm403, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2277, h2738, h3539, h3625, h3632, h4084, reducedSource338] using sourceEq403 B hB

theorem rowSound338 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row338 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck338, numericCheck338, reducedZero338 B hB hF, mul_zero]

theorem reducedZero346 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource346 (mixedVector B) = 0 := by
  have h2783 : mixedVector B (Sum.inr 2783) = Sparse.eval nodeValue2783 (mixedVector B) := by
    change mixedMoment B node2783 node2783Labels = _
    exact sound2783 B hB hF
  have h3582 : mixedVector B (Sum.inr 3582) = Sparse.eval nodeValue3582 (mixedVector B) := by
    change mixedMoment B node3582 node3582Labels = _
    exact sound3582 B hB hF
  have h3629 : mixedVector B (Sum.inr 3629) = Sparse.eval nodeValue3629 (mixedVector B) := by
    change mixedMoment B node3629 node3629Labels = _
    exact sound3629 B hB hF
  have h3633 : mixedVector B (Sum.inr 3633) = Sparse.eval nodeValue3633 (mixedVector B) := by
    change mixedMoment B node3633 node3633Labels = _
    exact sound3633 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm412, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2783, h3582, h3629, h3633, h4084, reducedSource346] using sourceEq412 B hB

theorem rowSound346 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row346 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck346, numericCheck346, reducedZero346 B hB hF, mul_zero]

theorem reducedZero347 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource347 (mixedVector B) = 0 := by
  have h3629 : mixedVector B (Sum.inr 3629) = Sparse.eval nodeValue3629 (mixedVector B) := by
    change mixedMoment B node3629 node3629Labels = _
    exact sound3629 B hB hF
  have h3632 : mixedVector B (Sum.inr 3632) = Sparse.eval nodeValue3632 (mixedVector B) := by
    change mixedMoment B node3632 node3632Labels = _
    exact sound3632 B hB hF
  have h3633 : mixedVector B (Sum.inr 3633) = Sparse.eval nodeValue3633 (mixedVector B) := by
    change mixedMoment B node3633 node3633Labels = _
    exact sound3633 B hB hF
  have h3635 : mixedVector B (Sum.inr 3635) = Sparse.eval nodeValue3635 (mixedVector B) := by
    change mixedMoment B node3635 node3635Labels = _
    exact sound3635 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm413, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3629, h3632, h3633, h3635, h4084, reducedSource347] using sourceEq413 B hB

theorem rowSound347 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row347 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck347, numericCheck347, reducedZero347 B hB hF, mul_zero]

theorem reducedZero348 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource348 (mixedVector B) = 0 := by
  have h2293 : mixedVector B (Sum.inr 2293) = Sparse.eval nodeValue2293 (mixedVector B) := by
    change mixedMoment B node2293 node2293Labels = _
    exact sound2293 B hB hF
  have h3548 : mixedVector B (Sum.inr 3548) = Sparse.eval nodeValue3548 (mixedVector B) := by
    change mixedMoment B node3548 node3548Labels = _
    exact sound3548 B hB hF
  have h3633 : mixedVector B (Sum.inr 3633) = Sparse.eval nodeValue3633 (mixedVector B) := by
    change mixedMoment B node3633 node3633Labels = _
    exact sound3633 B hB hF
  have h3635 : mixedVector B (Sum.inr 3635) = Sparse.eval nodeValue3635 (mixedVector B) := by
    change mixedMoment B node3635 node3635Labels = _
    exact sound3635 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm414, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2293, h3548, h3633, h3635, h4084, reducedSource348] using sourceEq414 B hB

theorem rowSound348 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row348 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck348, numericCheck348, reducedZero348 B hB hF, mul_zero]

theorem reducedZero349 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource349 (mixedVector B) = 0 := by
  have h1088 : mixedVector B (Sum.inr 1088) = Sparse.eval nodeValue1088 (mixedVector B) := by
    change mixedMoment B node1088 node1088Labels = _
    exact sound1088 B hB hF
  have h1092 : mixedVector B (Sum.inr 1092) = Sparse.eval nodeValue1092 (mixedVector B) := by
    change mixedMoment B node1092 node1092Labels = _
    exact sound1092 B hB hF
  have h1093 : mixedVector B (Sum.inr 1093) = Sparse.eval nodeValue1093 (mixedVector B) := by
    change mixedMoment B node1093 node1093Labels = _
    exact sound1093 B hB hF
  have h2516 : mixedVector B (Sum.inr 2516) = Sparse.eval nodeValue2516 (mixedVector B) := by
    change mixedMoment B node2516 node2516Labels = _
    exact sound2516 B hB hF
  have h2520 : mixedVector B (Sum.inr 2520) = Sparse.eval nodeValue2520 (mixedVector B) := by
    change mixedMoment B node2520 node2520Labels = _
    exact sound2520 B hB hF
  have h2521 : mixedVector B (Sum.inr 2521) = Sparse.eval nodeValue2521 (mixedVector B) := by
    change mixedMoment B node2521 node2521Labels = _
    exact sound2521 B hB hF
  have h2761 : mixedVector B (Sum.inr 2761) = Sparse.eval nodeValue2761 (mixedVector B) := by
    change mixedMoment B node2761 node2761Labels = _
    exact sound2761 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h2778 : mixedVector B (Sum.inr 2778) = Sparse.eval nodeValue2778 (mixedVector B) := by
    change mixedMoment B node2778 node2778Labels = _
    exact sound2778 B hB hF
  have h2780 : mixedVector B (Sum.inr 2780) = Sparse.eval nodeValue2780 (mixedVector B) := by
    change mixedMoment B node2780 node2780Labels = _
    exact sound2780 B hB hF
  have h2783 : mixedVector B (Sum.inr 2783) = Sparse.eval nodeValue2783 (mixedVector B) := by
    change mixedMoment B node2783 node2783Labels = _
    exact sound2783 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h3121 : mixedVector B (Sum.inr 3121) = Sparse.eval nodeValue3121 (mixedVector B) := by
    change mixedMoment B node3121 node3121Labels = _
    exact sound3121 B hB hF
  simpa only [sourceForm417, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1088, h1092, h1093, h2516, h2520, h2521, h2761, h2777, h2778, h2780, h2783, h3098, h3121, reducedSource349] using sourceEq417 B hB

theorem rowSound349 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row349 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck349, numericCheck349, reducedZero349 B hB hF, mul_zero]

theorem reducedZero350 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource350 (mixedVector B) = 0 := by
  have h1303 : mixedVector B (Sum.inr 1303) = Sparse.eval nodeValue1303 (mixedVector B) := by
    change mixedMoment B node1303 node1303Labels = _
    exact sound1303 B hB hF
  have h1309 : mixedVector B (Sum.inr 1309) = Sparse.eval nodeValue1309 (mixedVector B) := by
    change mixedMoment B node1309 node1309Labels = _
    exact sound1309 B hB hF
  have h1310 : mixedVector B (Sum.inr 1310) = Sparse.eval nodeValue1310 (mixedVector B) := by
    change mixedMoment B node1310 node1310Labels = _
    exact sound1310 B hB hF
  have h2789 : mixedVector B (Sum.inr 2789) = Sparse.eval nodeValue2789 (mixedVector B) := by
    change mixedMoment B node2789 node2789Labels = _
    exact sound2789 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm418, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1303, h1309, h1310, h2789, h4084, reducedSource350] using sourceEq418 B hB

theorem rowSound350 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row350 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck350, numericCheck350, reducedZero350 B hB hF, mul_zero]

theorem reducedZero351 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource351 (mixedVector B) = 0 := by
  have h1303 : mixedVector B (Sum.inr 1303) = Sparse.eval nodeValue1303 (mixedVector B) := by
    change mixedMoment B node1303 node1303Labels = _
    exact sound1303 B hB hF
  have h2134 : mixedVector B (Sum.inr 2134) = Sparse.eval nodeValue2134 (mixedVector B) := by
    change mixedMoment B node2134 node2134Labels = _
    exact sound2134 B hB hF
  have h2597 : mixedVector B (Sum.inr 2597) = Sparse.eval nodeValue2597 (mixedVector B) := by
    change mixedMoment B node2597 node2597Labels = _
    exact sound2597 B hB hF
  have h2781 : mixedVector B (Sum.inr 2781) = Sparse.eval nodeValue2781 (mixedVector B) := by
    change mixedMoment B node2781 node2781Labels = _
    exact sound2781 B hB hF
  have h2789 : mixedVector B (Sum.inr 2789) = Sparse.eval nodeValue2789 (mixedVector B) := by
    change mixedMoment B node2789 node2789Labels = _
    exact sound2789 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm419, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1303, h2134, h2597, h2781, h2789, h4084, reducedSource351] using sourceEq419 B hB

theorem rowSound351 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row351 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck351, numericCheck351, reducedZero351 B hB hF, mul_zero]

theorem sourceRowsAt336 : MixedData.sourceRows (336 : Fin 2425) =
    MixedData.row336 := by decide +kernel

theorem sourceRowsAt337 : MixedData.sourceRows (337 : Fin 2425) =
    MixedData.row337 := by decide +kernel

theorem sourceRowsAt338 : MixedData.sourceRows (338 : Fin 2425) =
    MixedData.row338 := by decide +kernel

theorem sourceRowsAt339 : MixedData.sourceRows (339 : Fin 2425) =
    MixedData.row339 := by decide +kernel

theorem sourceRowsAt340 : MixedData.sourceRows (340 : Fin 2425) =
    MixedData.row340 := by decide +kernel

theorem sourceRowsAt341 : MixedData.sourceRows (341 : Fin 2425) =
    MixedData.row341 := by decide +kernel

theorem sourceRowsAt342 : MixedData.sourceRows (342 : Fin 2425) =
    MixedData.row342 := by decide +kernel

theorem sourceRowsAt343 : MixedData.sourceRows (343 : Fin 2425) =
    MixedData.row343 := by decide +kernel

theorem sourceRowsAt344 : MixedData.sourceRows (344 : Fin 2425) =
    MixedData.row344 := by decide +kernel

theorem sourceRowsAt345 : MixedData.sourceRows (345 : Fin 2425) =
    MixedData.row345 := by decide +kernel

theorem sourceRowsAt346 : MixedData.sourceRows (346 : Fin 2425) =
    MixedData.row346 := by decide +kernel

theorem sourceRowsAt347 : MixedData.sourceRows (347 : Fin 2425) =
    MixedData.row347 := by decide +kernel

theorem sourceRowsAt348 : MixedData.sourceRows (348 : Fin 2425) =
    MixedData.row348 := by decide +kernel

theorem sourceRowsAt349 : MixedData.sourceRows (349 : Fin 2425) =
    MixedData.row349 := by decide +kernel

theorem sourceRowsAt350 : MixedData.sourceRows (350 : Fin 2425) =
    MixedData.row350 := by decide +kernel

theorem sourceRowsAt351 : MixedData.sourceRows (351 : Fin 2425) =
    MixedData.row351 := by decide +kernel

theorem chunkSound21_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 21) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 336 ∨ k.val = 337 ∨ k.val = 338 ∨ k.val = 339 ∨ k.val = 340 ∨ k.val = 341 ∨ k.val = 342 ∨ k.val = 343 ∨ k.val = 344 ∨ k.val = 345 ∨ k.val = 346 ∨ k.val = 347 ∨ k.val = 348 ∨ k.val = 349 ∨ k.val = 350 ∨ k.val = 351 := by omega
  rcases heq with h336 | h337 | h338 | h339 | h340 | h341 | h342 | h343 | h344 | h345 | h346 | h347 | h348 | h349 | h350 | h351
  · have he : k = (336 : Fin 2425) := Fin.ext h336
    subst k
    rw [sourceRowsAt336]
    exact rowSound336 B hB hF
  · have he : k = (337 : Fin 2425) := Fin.ext h337
    subst k
    rw [sourceRowsAt337]
    exact rowSound337 B hB hF
  · have he : k = (338 : Fin 2425) := Fin.ext h338
    subst k
    rw [sourceRowsAt338]
    exact rowSound338 B hB hF
  · have he : k = (339 : Fin 2425) := Fin.ext h339
    subst k
    rw [sourceRowsAt339]
    exact rowSound339_e B hB hF
  · have he : k = (340 : Fin 2425) := Fin.ext h340
    subst k
    rw [sourceRowsAt340]
    exact rowSound340_e B hB hF
  · have he : k = (341 : Fin 2425) := Fin.ext h341
    subst k
    rw [sourceRowsAt341]
    exact rowSound341_e B hB hF
  · have he : k = (342 : Fin 2425) := Fin.ext h342
    subst k
    rw [sourceRowsAt342]
    exact rowSound342_e B hB hF
  · have he : k = (343 : Fin 2425) := Fin.ext h343
    subst k
    rw [sourceRowsAt343]
    exact rowSound343_e B hB hF
  · have he : k = (344 : Fin 2425) := Fin.ext h344
    subst k
    rw [sourceRowsAt344]
    exact rowSound344_e B hB hF
  · have he : k = (345 : Fin 2425) := Fin.ext h345
    subst k
    rw [sourceRowsAt345]
    exact rowSound345_e B hB hF
  · have he : k = (346 : Fin 2425) := Fin.ext h346
    subst k
    rw [sourceRowsAt346]
    exact rowSound346 B hB hF
  · have he : k = (347 : Fin 2425) := Fin.ext h347
    subst k
    rw [sourceRowsAt347]
    exact rowSound347 B hB hF
  · have he : k = (348 : Fin 2425) := Fin.ext h348
    subst k
    rw [sourceRowsAt348]
    exact rowSound348 B hB hF
  · have he : k = (349 : Fin 2425) := Fin.ext h349
    subst k
    rw [sourceRowsAt349]
    exact rowSound349 B hB hF
  · have he : k = (350 : Fin 2425) := Fin.ext h350
    subst k
    rw [sourceRowsAt350]
    exact rowSound350 B hB hF
  · have he : k = (351 : Fin 2425) := Fin.ext h351
    subst k
    rw [sourceRowsAt351]
    exact rowSound351 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound21_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound21_e_oai
