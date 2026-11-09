-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound3_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:19:40.05713+00:00
-- url     : https://prove2.me/submissions/47cde6a4-4250-40bb-bab7-24c21bce8523

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E109
import Definitions.Def_OAIQ106E110
import Definitions.Def_OAIQ106E111
import Definitions.Def_OAIQ106E115
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound58_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3715 raw3715Labels = mixedMoment B node2284 node2284Labels := by
  calc
    mixedMoment B raw3715 raw3715Labels = mixedMoment B raw3715step0 raw3715step0Labels := by
      have hz : ∀ j, raw3715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3715step0 = (fun i j => raw3715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3715step0 raw3715; decide +kernel
      have hl : raw3715step0Labels = raw3715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3715 raw3715Labels permutation346 hz
    mixedMoment B raw3715step0 raw3715step0Labels = mixedMoment B raw3715step1 raw3715step1Labels := by
      have hz : ∀ j, raw3715step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3715step1 = (fun i j => raw3715step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3715step1 raw3715step0; decide +kernel
      have hl : raw3715step1Labels = raw3715step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3715step0 raw3715step0Labels permutation56 hz
    mixedMoment B raw3715step1 raw3715step1Labels = mixedMoment B raw3715step2 raw3715step2Labels := by
      have ha : raw3715step2 = (fun i j => raw3715step1 (permutation26 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3715step2 raw3715step1; decide +kernel
      have hl : raw3715step2Labels = raw3715step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3715step1 raw3715step1Labels permutation26 permutation2
    _ = mixedMoment B node2284 node2284Labels := by rfl

theorem canonical3716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3716 raw3716Labels = mixedMoment B node2055 node2055Labels := by
  calc
    mixedMoment B raw3716 raw3716Labels = mixedMoment B raw3716step0 raw3716step0Labels := by
      have hz : ∀ j, raw3716 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3716step0 = (fun i j => raw3716 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3716step0 raw3716; decide +kernel
      have hl : raw3716step0Labels = raw3716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3716 raw3716Labels permutation346 hz
    mixedMoment B raw3716step0 raw3716step0Labels = mixedMoment B raw3716step1 raw3716step1Labels := by
      have ha : raw3716step1 = (fun i j => raw3716step0 (permutation136 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3716step1 raw3716step0; decide +kernel
      have hl : raw3716step1Labels = raw3716step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3716step0 raw3716step0Labels permutation136 permutation2
    _ = mixedMoment B node2055 node2055Labels := by rfl

theorem canonical3719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3719 raw3719Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw3719 raw3719Labels = mixedMoment B raw3719step0 raw3719step0Labels := by
      have hz : ∀ j, raw3719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3719step0 = (fun i j => raw3719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3719step0 raw3719; decide +kernel
      have hl : raw3719step0Labels = raw3719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3719 raw3719Labels permutation346 hz
    mixedMoment B raw3719step0 raw3719step0Labels = mixedMoment B raw3719step1 raw3719step1Labels := by
      have hz : ∀ j, raw3719step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3719step1 = (fun i j => raw3719step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3719step1 raw3719step0; decide +kernel
      have hl : raw3719step1Labels = raw3719step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3719step0 raw3719step0Labels permutation56 hz
    mixedMoment B raw3719step1 raw3719step1Labels = mixedMoment B raw3719step2 raw3719step2Labels := by
      have ha : raw3719step2 = (fun i j => raw3719step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3719step2 raw3719step1; decide +kernel
      have hl : raw3719step2Labels = raw3719step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3719step1 raw3719step1Labels permutation29 permutation2
    _ = mixedMoment B node2290 node2290Labels := by rfl

theorem canonical3721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3721 raw3721Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw3721 raw3721Labels = mixedMoment B raw3721step0 raw3721step0Labels := by
      have hz : ∀ j, raw3721 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3721step0 = (fun i j => raw3721 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3721step0 raw3721; decide +kernel
      have hl : raw3721step0Labels = raw3721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3721 raw3721Labels permutation520 hz
    mixedMoment B raw3721step0 raw3721step0Labels = mixedMoment B raw3721step1 raw3721step1Labels := by
      have hz : ∀ j, raw3721step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3721step1 = (fun i j => raw3721step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3721step1 raw3721step0; decide +kernel
      have hl : raw3721step1Labels = raw3721step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3721step0 raw3721step0Labels permutation104 hz
    mixedMoment B raw3721step1 raw3721step1Labels = mixedMoment B raw3721step2 raw3721step2Labels := by
      have hz : ∀ j, raw3721step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3721step2 = (fun i j => raw3721step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3721step2 raw3721step1; decide +kernel
      have hl : raw3721step2Labels = raw3721step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3721step1 raw3721step1Labels permutation20 hz
    mixedMoment B raw3721step2 raw3721step2Labels = mixedMoment B raw3721step3 raw3721step3Labels := by
      have hz : ∀ j, raw3721step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw3721step3 = (fun i j => raw3721step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw3721step3 raw3721step2; decide +kernel
      have hl : raw3721step3Labels = raw3721step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3721step2 raw3721step2Labels permutation4 hz
    mixedMoment B raw3721step3 raw3721step3Labels = mixedMoment B raw3721step4 raw3721step4Labels := by
      have ha : raw3721step4 = (fun i j => raw3721step3 (permutation1 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3721step4 raw3721step3; decide +kernel
      have hl : raw3721step4Labels = raw3721step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3721step3 raw3721step3Labels permutation1 permutation0
    _ = mixedMoment B node4085 node4085Labels := by rfl

theorem canonical3724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3724 raw3724Labels = mixedMoment B node1068 node1068Labels := by
  calc
    mixedMoment B raw3724 raw3724Labels = mixedMoment B raw3724step0 raw3724step0Labels := by
      have hz : ∀ j, raw3724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3724step0 = (fun i j => raw3724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3724step0 raw3724; decide +kernel
      have hl : raw3724step0Labels = raw3724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3724 raw3724Labels permutation346 hz
    mixedMoment B raw3724step0 raw3724step0Labels = mixedMoment B raw3724step1 raw3724step1Labels := by
      have hz : ∀ j, raw3724step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3724step1 = (fun i j => raw3724step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3724step1 raw3724step0; decide +kernel
      have hl : raw3724step1Labels = raw3724step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3724step0 raw3724step0Labels permutation56 hz
    mixedMoment B raw3724step1 raw3724step1Labels = mixedMoment B raw3724step2 raw3724step2Labels := by
      have ha : raw3724step2 = (fun i j => raw3724step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3724step2 raw3724step1; decide +kernel
      have hl : raw3724step2Labels = raw3724step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3724step1 raw3724step1Labels permutation12 permutation4
    mixedMoment B raw3724step2 raw3724step2Labels = mixedMoment B raw3724step3 raw3724step3Labels := by
      have ha : raw3724step3 = -raw3724step2 := by apply Matrix.ext; change ∀ i j, raw3724step3 i j = -(raw3724step2 i j); unfold raw3724step3 raw3724step2; decide +kernel
      have hl : raw3724step3Labels = raw3724step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1068 node1068Labels := by rfl

theorem canonical3731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3731 raw3731Labels = mixedMoment B node2040 node2040Labels := by
  calc
    mixedMoment B raw3731 raw3731Labels = mixedMoment B raw3731step0 raw3731step0Labels := by
      have ha : raw3731step0 = (fun i j => raw3731 (permutation602 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3731step0 raw3731; decide +kernel
      have hl : raw3731step0Labels = raw3731Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3731 raw3731Labels permutation602 permutation2
    _ = mixedMoment B node2040 node2040Labels := by rfl

theorem canonical3732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3732 raw3732Labels = mixedMoment B node2042 node2042Labels := by
  calc
    mixedMoment B raw3732 raw3732Labels = mixedMoment B raw3732step0 raw3732step0Labels := by
      have hz : ∀ j, raw3732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3732step0 = (fun i j => raw3732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3732step0 raw3732; decide +kernel
      have hl : raw3732step0Labels = raw3732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3732 raw3732Labels permutation346 hz
    mixedMoment B raw3732step0 raw3732step0Labels = mixedMoment B raw3732step1 raw3732step1Labels := by
      have ha : raw3732step1 = (fun i j => raw3732step0 (permutation134 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3732step1 raw3732step0; decide +kernel
      have hl : raw3732step1Labels = raw3732step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3732step0 raw3732step0Labels permutation134 permutation2
    _ = mixedMoment B node2042 node2042Labels := by rfl

theorem canonical3733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3733 raw3733Labels = mixedMoment B node2041 node2041Labels := by
  calc
    mixedMoment B raw3733 raw3733Labels = mixedMoment B raw3733step0 raw3733step0Labels := by
      have hz : ∀ j, raw3733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3733step0 = (fun i j => raw3733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3733step0 raw3733; decide +kernel
      have hl : raw3733step0Labels = raw3733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3733 raw3733Labels permutation346 hz
    mixedMoment B raw3733step0 raw3733step0Labels = mixedMoment B raw3733step1 raw3733step1Labels := by
      have ha : raw3733step1 = (fun i j => raw3733step0 (permutation134 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3733step1 raw3733step0; decide +kernel
      have hl : raw3733step1Labels = raw3733step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3733step0 raw3733step0Labels permutation134 permutation2
    _ = mixedMoment B node2041 node2041Labels := by rfl

theorem canonical3734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3734 raw3734Labels = mixedMoment B node2055 node2055Labels := by
  calc
    mixedMoment B raw3734 raw3734Labels = mixedMoment B raw3734step0 raw3734step0Labels := by
      have hz : ∀ j, raw3734 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3734step0 = (fun i j => raw3734 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3734step0 raw3734; decide +kernel
      have hl : raw3734step0Labels = raw3734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3734 raw3734Labels permutation346 hz
    mixedMoment B raw3734step0 raw3734step0Labels = mixedMoment B raw3734step1 raw3734step1Labels := by
      have ha : raw3734step1 = (fun i j => raw3734step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3734step1 raw3734step0; decide +kernel
      have hl : raw3734step1Labels = raw3734step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3734step0 raw3734step0Labels permutation33 permutation4
    mixedMoment B raw3734step1 raw3734step1Labels = mixedMoment B raw3734step2 raw3734step2Labels := by
      have ha : raw3734step2 = -raw3734step1 := by apply Matrix.ext; change ∀ i j, raw3734step2 i j = -(raw3734step1 i j); unfold raw3734step2 raw3734step1; decide +kernel
      have hl : raw3734step2Labels = raw3734step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2055 node2055Labels := by rfl

theorem canonical3735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3735 raw3735Labels = mixedMoment B node2042 node2042Labels := by
  calc
    mixedMoment B raw3735 raw3735Labels = mixedMoment B raw3735step0 raw3735step0Labels := by
      have hz : ∀ j, raw3735 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3735step0 = (fun i j => raw3735 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3735step0 raw3735; decide +kernel
      have hl : raw3735step0Labels = raw3735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3735 raw3735Labels permutation265 hz
    mixedMoment B raw3735step0 raw3735step0Labels = mixedMoment B raw3735step1 raw3735step1Labels := by
      have ha : raw3735step1 = (fun i j => raw3735step0 (permutation134 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3735step1 raw3735step0; decide +kernel
      have hl : raw3735step1Labels = raw3735step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3735step0 raw3735step0Labels permutation134 permutation2
    _ = mixedMoment B node2042 node2042Labels := by rfl

theorem canonical3736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3736 raw3736Labels = mixedMoment B node2284 node2284Labels := by
  calc
    mixedMoment B raw3736 raw3736Labels = mixedMoment B raw3736step0 raw3736step0Labels := by
      have hz : ∀ j, raw3736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3736step0 = (fun i j => raw3736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3736step0 raw3736; decide +kernel
      have hl : raw3736step0Labels = raw3736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3736 raw3736Labels permutation346 hz
    mixedMoment B raw3736step0 raw3736step0Labels = mixedMoment B raw3736step1 raw3736step1Labels := by
      have hz : ∀ j, raw3736step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3736step1 = (fun i j => raw3736step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3736step1 raw3736step0; decide +kernel
      have hl : raw3736step1Labels = raw3736step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3736step0 raw3736step0Labels permutation56 hz
    mixedMoment B raw3736step1 raw3736step1Labels = mixedMoment B raw3736step2 raw3736step2Labels := by
      have ha : raw3736step2 = (fun i j => raw3736step1 (permutation27 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3736step2 raw3736step1; decide +kernel
      have hl : raw3736step2Labels = raw3736step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3736step1 raw3736step1Labels permutation27 permutation2
    _ = mixedMoment B node2284 node2284Labels := by rfl

theorem canonical3737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3737 raw3737Labels = mixedMoment B node1068 node1068Labels := by
  calc
    mixedMoment B raw3737 raw3737Labels = mixedMoment B raw3737step0 raw3737step0Labels := by
      have hz : ∀ j, raw3737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3737step0 = (fun i j => raw3737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3737step0 raw3737; decide +kernel
      have hl : raw3737step0Labels = raw3737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3737 raw3737Labels permutation346 hz
    mixedMoment B raw3737step0 raw3737step0Labels = mixedMoment B raw3737step1 raw3737step1Labels := by
      have hz : ∀ j, raw3737step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3737step1 = (fun i j => raw3737step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3737step1 raw3737step0; decide +kernel
      have hl : raw3737step1Labels = raw3737step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3737step0 raw3737step0Labels permutation56 hz
    mixedMoment B raw3737step1 raw3737step1Labels = mixedMoment B raw3737step2 raw3737step2Labels := by
      have ha : raw3737step2 = (fun i j => raw3737step1 (permutation26 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3737step2 raw3737step1; decide +kernel
      have hl : raw3737step2Labels = raw3737step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3737step1 raw3737step1Labels permutation26 permutation2
    _ = mixedMoment B node1068 node1068Labels := by rfl

theorem canonical3828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3828 raw3828Labels = mixedMoment B node2235 node2235Labels := by
  calc
    mixedMoment B raw3828 raw3828Labels = mixedMoment B raw3828step0 raw3828step0Labels := by
      have hz : ∀ j, raw3828 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3828step0 = (fun i j => raw3828 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3828step0 raw3828; decide +kernel
      have hl : raw3828step0Labels = raw3828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3828 raw3828Labels permutation265 hz
    _ = mixedMoment B node2235 node2235Labels := by rfl

theorem canonical3829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3829 raw3829Labels = mixedMoment B node3155 node3155Labels := by
  calc
    mixedMoment B raw3829 raw3829Labels = mixedMoment B raw3829step0 raw3829step0Labels := by
      have ha : raw3829step0 = (fun i j => raw3829 (permutation590 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3829step0 raw3829; decide +kernel
      have hl : raw3829step0Labels = raw3829Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3829 raw3829Labels permutation590 permutation4
    _ = mixedMoment B node3155 node3155Labels := by rfl

theorem canonical3830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3830 raw3830Labels = mixedMoment B node3158 node3158Labels := by
  calc
    mixedMoment B raw3830 raw3830Labels = mixedMoment B raw3830step0 raw3830step0Labels := by
      have hz : ∀ j, raw3830 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3830step0 = (fun i j => raw3830 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3830step0 raw3830; decide +kernel
      have hl : raw3830step0Labels = raw3830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3830 raw3830Labels permutation265 hz
    mixedMoment B raw3830step0 raw3830step0Labels = mixedMoment B raw3830step1 raw3830step1Labels := by
      have ha : raw3830step1 = (fun i j => raw3830step0 (permutation131 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3830step1 raw3830step0; decide +kernel
      have hl : raw3830step1Labels = raw3830step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3830step0 raw3830step0Labels permutation131 permutation4
    _ = mixedMoment B node3158 node3158Labels := by rfl

theorem canonical3831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3831 raw3831Labels = mixedMoment B node3158 node3158Labels := by
  calc
    mixedMoment B raw3831 raw3831Labels = mixedMoment B raw3831step0 raw3831step0Labels := by
      have hz : ∀ j, raw3831 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3831step0 = (fun i j => raw3831 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3831step0 raw3831; decide +kernel
      have hl : raw3831step0Labels = raw3831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3831 raw3831Labels permutation265 hz
    mixedMoment B raw3831step0 raw3831step0Labels = mixedMoment B raw3831step1 raw3831step1Labels := by
      have ha : raw3831step1 = (fun i j => raw3831step0 (permutation129 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3831step1 raw3831step0; decide +kernel
      have hl : raw3831step1Labels = raw3831step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3831step0 raw3831step0Labels permutation129 permutation4
    _ = mixedMoment B node3158 node3158Labels := by rfl

theorem canonical3832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3832 raw3832Labels = mixedMoment B node3158 node3158Labels := by
  calc
    mixedMoment B raw3832 raw3832Labels = mixedMoment B raw3832step0 raw3832step0Labels := by
      have hz : ∀ j, raw3832 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3832step0 = (fun i j => raw3832 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3832step0 raw3832; decide +kernel
      have hl : raw3832step0Labels = raw3832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3832 raw3832Labels permutation265 hz
    mixedMoment B raw3832step0 raw3832step0Labels = mixedMoment B raw3832step1 raw3832step1Labels := by
      have ha : raw3832step1 = (fun i j => raw3832step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3832step1 raw3832step0; decide +kernel
      have hl : raw3832step1Labels = raw3832step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3832step0 raw3832step0Labels permutation128 permutation4
    _ = mixedMoment B node3158 node3158Labels := by rfl

theorem canonical3833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3833 raw3833Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw3833 raw3833Labels = mixedMoment B raw3833step0 raw3833step0Labels := by
      have hz : ∀ j, raw3833 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3833step0 = (fun i j => raw3833 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3833step0 raw3833; decide +kernel
      have hl : raw3833step0Labels = raw3833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3833 raw3833Labels permutation265 hz
    _ = mixedMoment B node3619 node3619Labels := by rfl

theorem canonical3834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3834 raw3834Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw3834 raw3834Labels = mixedMoment B raw3834step0 raw3834step0Labels := by
      have hz : ∀ j, raw3834 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3834step0 = (fun i j => raw3834 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3834step0 raw3834; decide +kernel
      have hl : raw3834step0Labels = raw3834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3834 raw3834Labels permutation590 hz
    mixedMoment B raw3834step0 raw3834step0Labels = mixedMoment B raw3834step1 raw3834step1Labels := by
      have hz : ∀ j, raw3834step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3834step1 = (fun i j => raw3834step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3834step1 raw3834step0; decide +kernel
      have hl : raw3834step1Labels = raw3834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3834step0 raw3834step0Labels permutation56 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical3835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3835 raw3835Labels = mixedMoment B node1014 node1014Labels := by
  calc
    mixedMoment B raw3835 raw3835Labels = mixedMoment B raw3835step0 raw3835step0Labels := by
      have ha : raw3835step0 = (fun i j => raw3835 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3835step0 raw3835; decide +kernel
      have hl : raw3835step0Labels = raw3835Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3835 raw3835Labels permutation184 permutation2
    _ = mixedMoment B node1014 node1014Labels := by rfl

theorem canonical3836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3836 raw3836Labels = mixedMoment B node1024 node1024Labels := by
  calc
    mixedMoment B raw3836 raw3836Labels = mixedMoment B raw3836step0 raw3836step0Labels := by
      have hz : ∀ j, raw3836 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3836step0 = (fun i j => raw3836 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3836step0 raw3836; decide +kernel
      have hl : raw3836step0Labels = raw3836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3836 raw3836Labels permutation265 hz
    mixedMoment B raw3836step0 raw3836step0Labels = mixedMoment B raw3836step1 raw3836step1Labels := by
      have ha : raw3836step1 = (fun i j => raw3836step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3836step1 raw3836step0; decide +kernel
      have hl : raw3836step1Labels = raw3836step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3836step0 raw3836step0Labels permutation40 permutation2
    _ = mixedMoment B node1024 node1024Labels := by rfl

theorem canonical3837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3837 raw3837Labels = mixedMoment B node1024 node1024Labels := by
  calc
    mixedMoment B raw3837 raw3837Labels = mixedMoment B raw3837step0 raw3837step0Labels := by
      have hz : ∀ j, raw3837 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3837step0 = (fun i j => raw3837 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3837step0 raw3837; decide +kernel
      have hl : raw3837step0Labels = raw3837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3837 raw3837Labels permutation265 hz
    mixedMoment B raw3837step0 raw3837step0Labels = mixedMoment B raw3837step1 raw3837step1Labels := by
      have ha : raw3837step1 = (fun i j => raw3837step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3837step1 raw3837step0; decide +kernel
      have hl : raw3837step1Labels = raw3837step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3837step0 raw3837step0Labels permutation34 permutation2
    _ = mixedMoment B node1024 node1024Labels := by rfl

theorem canonical3838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3838 raw3838Labels = mixedMoment B node1024 node1024Labels := by
  calc
    mixedMoment B raw3838 raw3838Labels = mixedMoment B raw3838step0 raw3838step0Labels := by
      have hz : ∀ j, raw3838 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3838step0 = (fun i j => raw3838 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3838step0 raw3838; decide +kernel
      have hl : raw3838step0Labels = raw3838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3838 raw3838Labels permutation265 hz
    _ = mixedMoment B node1024 node1024Labels := by rfl

theorem canonical3839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3839 raw3839Labels = mixedMoment B node1016 node1016Labels := by
  calc
    mixedMoment B raw3839 raw3839Labels = mixedMoment B raw3839step0 raw3839step0Labels := by
      have hz : ∀ j, raw3839 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3839step0 = (fun i j => raw3839 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3839step0 raw3839; decide +kernel
      have hl : raw3839step0Labels = raw3839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3839 raw3839Labels permutation265 hz
    _ = mixedMoment B node1016 node1016Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3840 raw3840Labels = mixedMoment B node2083 node2083Labels := by
  calc
    mixedMoment B raw3840 raw3840Labels = mixedMoment B raw3840step0 raw3840step0Labels := by
      have ha : raw3840step0 = (fun i j => raw3840 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3840step0 raw3840; decide +kernel
      have hl : raw3840step0Labels = raw3840Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3840 raw3840Labels permutation184 permutation2
    _ = mixedMoment B node2083 node2083Labels := by rfl

theorem canonical3841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3841 raw3841Labels = mixedMoment B node2083 node2083Labels := by
  calc
    mixedMoment B raw3841 raw3841Labels = mixedMoment B raw3841step0 raw3841step0Labels := by
      have ha : raw3841step0 = (fun i j => raw3841 (permutation208 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3841step0 raw3841; decide +kernel
      have hl : raw3841step0Labels = raw3841Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3841 raw3841Labels permutation208 permutation2
    _ = mixedMoment B node2083 node2083Labels := by rfl

theorem canonical3842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3842 raw3842Labels = mixedMoment B node2083 node2083Labels := by
  calc
    mixedMoment B raw3842 raw3842Labels = mixedMoment B raw3842step0 raw3842step0Labels := by
      have ha : raw3842step0 = (fun i j => raw3842 (permutation232 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3842step0 raw3842; decide +kernel
      have hl : raw3842step0Labels = raw3842Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3842 raw3842Labels permutation232 permutation2
    _ = mixedMoment B node2083 node2083Labels := by rfl

theorem canonical3843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3843 raw3843Labels = mixedMoment B node2233 node2233Labels := by
  calc
    mixedMoment B raw3843 raw3843Labels = mixedMoment B raw3843step0 raw3843step0Labels := by
      have ha : raw3843step0 = (fun i j => raw3843 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3843step0 raw3843; decide +kernel
      have hl : raw3843step0Labels = raw3843Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3843 raw3843Labels permutation184 permutation2
    _ = mixedMoment B node2233 node2233Labels := by rfl

theorem canonical3844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3844 raw3844Labels = mixedMoment B node2010 node2010Labels := by
  calc
    mixedMoment B raw3844 raw3844Labels = mixedMoment B raw3844step0 raw3844step0Labels := by
      have ha : raw3844step0 = (fun i j => raw3844 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3844step0 raw3844; decide +kernel
      have hl : raw3844step0Labels = raw3844Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3844 raw3844Labels permutation160 permutation2
    _ = mixedMoment B node2010 node2010Labels := by rfl

theorem canonical3845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3845 raw3845Labels = mixedMoment B node2010 node2010Labels := by
  calc
    mixedMoment B raw3845 raw3845Labels = mixedMoment B raw3845step0 raw3845step0Labels := by
      have ha : raw3845step0 = (fun i j => raw3845 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3845step0 raw3845; decide +kernel
      have hl : raw3845step0Labels = raw3845Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3845 raw3845Labels permutation154 permutation2
    _ = mixedMoment B node2010 node2010Labels := by rfl

theorem canonical3846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3846 raw3846Labels = mixedMoment B node2010 node2010Labels := by
  calc
    _ = mixedMoment B node2010 node2010Labels := by rfl

theorem canonical3847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3847 raw3847Labels = mixedMoment B node1457 node1457Labels := by
  calc
    mixedMoment B raw3847 raw3847Labels = mixedMoment B raw3847step0 raw3847step0Labels := by
      have ha : raw3847step0 = (fun i j => raw3847 (permutation590 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3847step0 raw3847; decide +kernel
      have hl : raw3847step0Labels = raw3847Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3847 raw3847Labels permutation590 permutation4
    _ = mixedMoment B node1457 node1457Labels := by rfl

theorem canonical3848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3848 raw3848Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw3848 raw3848Labels = mixedMoment B raw3848step0 raw3848step0Labels := by
      have hz : ∀ j, raw3848 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3848step0 = (fun i j => raw3848 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3848step0 raw3848; decide +kernel
      have hl : raw3848step0Labels = raw3848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3848 raw3848Labels permutation265 hz
    mixedMoment B raw3848step0 raw3848step0Labels = mixedMoment B raw3848step1 raw3848step1Labels := by
      have ha : raw3848step1 = (fun i j => raw3848step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3848step1 raw3848step0; decide +kernel
      have hl : raw3848step1Labels = raw3848step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3848step0 raw3848step0Labels permutation40 permutation2
    _ = mixedMoment B node2092 node2092Labels := by rfl

theorem canonical3849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3849 raw3849Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw3849 raw3849Labels = mixedMoment B raw3849step0 raw3849step0Labels := by
      have hz : ∀ j, raw3849 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3849step0 = (fun i j => raw3849 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3849step0 raw3849; decide +kernel
      have hl : raw3849step0Labels = raw3849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3849 raw3849Labels permutation265 hz
    mixedMoment B raw3849step0 raw3849step0Labels = mixedMoment B raw3849step1 raw3849step1Labels := by
      have ha : raw3849step1 = (fun i j => raw3849step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3849step1 raw3849step0; decide +kernel
      have hl : raw3849step1Labels = raw3849step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3849step0 raw3849step0Labels permutation46 permutation2
    _ = mixedMoment B node2092 node2092Labels := by rfl

theorem canonical3850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3850 raw3850Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw3850 raw3850Labels = mixedMoment B raw3850step0 raw3850step0Labels := by
      have hz : ∀ j, raw3850 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3850step0 = (fun i j => raw3850 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3850step0 raw3850; decide +kernel
      have hl : raw3850step0Labels = raw3850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3850 raw3850Labels permutation265 hz
    mixedMoment B raw3850step0 raw3850step0Labels = mixedMoment B raw3850step1 raw3850step1Labels := by
      have ha : raw3850step1 = (fun i j => raw3850step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3850step1 raw3850step0; decide +kernel
      have hl : raw3850step1Labels = raw3850step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3850step0 raw3850step0Labels permutation40 permutation2
    _ = mixedMoment B node2245 node2245Labels := by rfl

theorem canonical3851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3851 raw3851Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw3851 raw3851Labels = mixedMoment B raw3851step0 raw3851step0Labels := by
      have hz : ∀ j, raw3851 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3851step0 = (fun i j => raw3851 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3851step0 raw3851; decide +kernel
      have hl : raw3851step0Labels = raw3851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3851 raw3851Labels permutation265 hz
    mixedMoment B raw3851step0 raw3851step0Labels = mixedMoment B raw3851step1 raw3851step1Labels := by
      have ha : raw3851step1 = (fun i j => raw3851step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3851step1 raw3851step0; decide +kernel
      have hl : raw3851step1Labels = raw3851step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3851step0 raw3851step0Labels permutation34 permutation2
    _ = mixedMoment B node2092 node2092Labels := by rfl

theorem canonical3852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3852 raw3852Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw3852 raw3852Labels = mixedMoment B raw3852step0 raw3852step0Labels := by
      have hz : ∀ j, raw3852 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3852step0 = (fun i j => raw3852 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3852step0 raw3852; decide +kernel
      have hl : raw3852step0Labels = raw3852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3852 raw3852Labels permutation265 hz
    _ = mixedMoment B node2092 node2092Labels := by rfl

theorem canonical3853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3853 raw3853Labels = mixedMoment B node1460 node1460Labels := by
  calc
    mixedMoment B raw3853 raw3853Labels = mixedMoment B raw3853step0 raw3853step0Labels := by
      have hz : ∀ j, raw3853 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3853step0 = (fun i j => raw3853 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3853step0 raw3853; decide +kernel
      have hl : raw3853step0Labels = raw3853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3853 raw3853Labels permutation265 hz
    mixedMoment B raw3853step0 raw3853step0Labels = mixedMoment B raw3853step1 raw3853step1Labels := by
      have ha : raw3853step1 = (fun i j => raw3853step0 (permutation131 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3853step1 raw3853step0; decide +kernel
      have hl : raw3853step1Labels = raw3853step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3853step0 raw3853step0Labels permutation131 permutation4
    _ = mixedMoment B node1460 node1460Labels := by rfl

theorem canonical3854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3854 raw3854Labels = mixedMoment B node1460 node1460Labels := by
  calc
    mixedMoment B raw3854 raw3854Labels = mixedMoment B raw3854step0 raw3854step0Labels := by
      have hz : ∀ j, raw3854 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3854step0 = (fun i j => raw3854 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3854step0 raw3854; decide +kernel
      have hl : raw3854step0Labels = raw3854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3854 raw3854Labels permutation265 hz
    mixedMoment B raw3854step0 raw3854step0Labels = mixedMoment B raw3854step1 raw3854step1Labels := by
      have ha : raw3854step1 = (fun i j => raw3854step0 (permutation129 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3854step1 raw3854step0; decide +kernel
      have hl : raw3854step1Labels = raw3854step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3854step0 raw3854step0Labels permutation129 permutation4
    _ = mixedMoment B node1460 node1460Labels := by rfl

theorem canonical3855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3855 raw3855Labels = mixedMoment B node1460 node1460Labels := by
  calc
    mixedMoment B raw3855 raw3855Labels = mixedMoment B raw3855step0 raw3855step0Labels := by
      have hz : ∀ j, raw3855 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3855step0 = (fun i j => raw3855 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3855step0 raw3855; decide +kernel
      have hl : raw3855step0Labels = raw3855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3855 raw3855Labels permutation265 hz
    mixedMoment B raw3855step0 raw3855step0Labels = mixedMoment B raw3855step1 raw3855step1Labels := by
      have ha : raw3855step1 = (fun i j => raw3855step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3855step1 raw3855step0; decide +kernel
      have hl : raw3855step1Labels = raw3855step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3855step0 raw3855step0Labels permutation128 permutation4
    _ = mixedMoment B node1460 node1460Labels := by rfl

theorem canonical3900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3900 raw3900Labels = mixedMoment B node2283 node2283Labels := by
  calc
    mixedMoment B raw3900 raw3900Labels = mixedMoment B raw3900step0 raw3900step0Labels := by
      have hz : ∀ j, raw3900 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3900step0 = (fun i j => raw3900 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3900step0 raw3900; decide +kernel
      have hl : raw3900step0Labels = raw3900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3900 raw3900Labels permutation265 hz
    mixedMoment B raw3900step0 raw3900step0Labels = mixedMoment B raw3900step1 raw3900step1Labels := by
      have ha : raw3900step1 = (fun i j => raw3900step0 (permutation128 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3900step1 raw3900step0; decide +kernel
      have hl : raw3900step1Labels = raw3900step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3900step0 raw3900step0Labels permutation128 permutation2
    _ = mixedMoment B node2283 node2283Labels := by rfl

theorem canonical3901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3901 raw3901Labels = mixedMoment B node2050 node2050Labels := by
  calc
    mixedMoment B raw3901 raw3901Labels = mixedMoment B raw3901step0 raw3901step0Labels := by
      have ha : raw3901step0 = (fun i j => raw3901 (permutation609 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3901step0 raw3901; decide +kernel
      have hl : raw3901step0Labels = raw3901Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3901 raw3901Labels permutation609 permutation2
    _ = mixedMoment B node2050 node2050Labels := by rfl

theorem canonical3902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3902 raw3902Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw3902 raw3902Labels = mixedMoment B raw3902step0 raw3902step0Labels := by
      have hz : ∀ j, raw3902 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3902step0 = (fun i j => raw3902 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3902step0 raw3902; decide +kernel
      have hl : raw3902step0Labels = raw3902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3902 raw3902Labels permutation434 hz
    mixedMoment B raw3902step0 raw3902step0Labels = mixedMoment B raw3902step1 raw3902step1Labels := by
      have hz : ∀ j, raw3902step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3902step1 = (fun i j => raw3902step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3902step1 raw3902step0; decide +kernel
      have hl : raw3902step1Labels = raw3902step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3902step0 raw3902step0Labels permutation56 hz
    mixedMoment B raw3902step1 raw3902step1Labels = mixedMoment B raw3902step2 raw3902step2Labels := by
      have ha : raw3902step2 = (fun i j => raw3902step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3902step2 raw3902step1; decide +kernel
      have hl : raw3902step2Labels = raw3902step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3902step1 raw3902step1Labels permutation29 permutation2
    _ = mixedMoment B node2290 node2290Labels := by rfl

theorem canonical3903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3903 raw3903Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw3903 raw3903Labels = mixedMoment B raw3903step0 raw3903step0Labels := by
      have hz : ∀ j, raw3903 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3903step0 = (fun i j => raw3903 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3903step0 raw3903; decide +kernel
      have hl : raw3903step0Labels = raw3903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3903 raw3903Labels permutation520 hz
    mixedMoment B raw3903step0 raw3903step0Labels = mixedMoment B raw3903step1 raw3903step1Labels := by
      have hz : ∀ j, raw3903step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3903step1 = (fun i j => raw3903step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3903step1 raw3903step0; decide +kernel
      have hl : raw3903step1Labels = raw3903step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3903step0 raw3903step0Labels permutation56 hz
    mixedMoment B raw3903step1 raw3903step1Labels = mixedMoment B raw3903step2 raw3903step2Labels := by
      have ha : raw3903step2 = (fun i j => raw3903step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3903step2 raw3903step1; decide +kernel
      have hl : raw3903step2Labels = raw3903step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3903step1 raw3903step1Labels permutation29 permutation2
    _ = mixedMoment B node2290 node2290Labels := by rfl

theorem canonical3904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3904 raw3904Labels = mixedMoment B node1078 node1078Labels := by
  calc
    mixedMoment B raw3904 raw3904Labels = mixedMoment B raw3904step0 raw3904step0Labels := by
      have hz : ∀ j, raw3904 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3904step0 = (fun i j => raw3904 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3904step0 raw3904; decide +kernel
      have hl : raw3904step0Labels = raw3904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3904 raw3904Labels permutation265 hz
    mixedMoment B raw3904step0 raw3904step0Labels = mixedMoment B raw3904step1 raw3904step1Labels := by
      have ha : raw3904step1 = (fun i j => raw3904step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3904step1 raw3904step0; decide +kernel
      have hl : raw3904step1Labels = raw3904step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3904step0 raw3904step0Labels permutation137 permutation2
    _ = mixedMoment B node1078 node1078Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3972 raw3972Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw3972 raw3972Labels = mixedMoment B raw3972step0 raw3972step0Labels := by
      have hz : ∀ j, raw3972 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3972step0 = (fun i j => raw3972 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3972step0 raw3972; decide +kernel
      have hl : raw3972step0Labels = raw3972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3972 raw3972Labels permutation434 hz
    mixedMoment B raw3972step0 raw3972step0Labels = mixedMoment B raw3972step1 raw3972step1Labels := by
      have hz : ∀ j, raw3972step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3972step1 = (fun i j => raw3972step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3972step1 raw3972step0; decide +kernel
      have hl : raw3972step1Labels = raw3972step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3972step0 raw3972step0Labels permutation80 hz
    mixedMoment B raw3972step1 raw3972step1Labels = mixedMoment B raw3972step2 raw3972step2Labels := by
      have ha : raw3972step2 = (fun i j => raw3972step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3972step2 raw3972step1; decide +kernel
      have hl : raw3972step2Labels = raw3972step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3972step1 raw3972step1Labels permutation28 permutation5
    mixedMoment B raw3972step2 raw3972step2Labels = mixedMoment B raw3972step3 raw3972step3Labels := by
      have ha : raw3972step3 = raw3972step2 := by apply Matrix.ext; unfold raw3972step3 raw3972step2; decide +kernel
      have hl : raw3972step2Labels = labelEmbedding1 ∘ raw3972step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3972step2 raw3972step2Labels raw3972step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3626 node3626Labels := by rfl

theorem canonical3973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3973 raw3973Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw3973 raw3973Labels = mixedMoment B raw3973step0 raw3973step0Labels := by
      have hz : ∀ j, raw3973 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3973step0 = (fun i j => raw3973 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3973step0 raw3973; decide +kernel
      have hl : raw3973step0Labels = raw3973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3973 raw3973Labels permutation434 hz
    mixedMoment B raw3973step0 raw3973step0Labels = mixedMoment B raw3973step1 raw3973step1Labels := by
      have ha : raw3973step1 = (fun i j => raw3973step0 (permutation134 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3973step1 raw3973step0; decide +kernel
      have hl : raw3973step1Labels = raw3973step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3973step0 raw3973step0Labels permutation134 permutation5
    mixedMoment B raw3973step1 raw3973step1Labels = mixedMoment B raw3973step2 raw3973step2Labels := by
      have ha : raw3973step2 = raw3973step1 := by apply Matrix.ext; unfold raw3973step2 raw3973step1; decide +kernel
      have hl : raw3973step1Labels = labelEmbedding1 ∘ raw3973step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3973step1 raw3973step1Labels raw3973step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

theorem canonical3974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3974 raw3974Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw3974 raw3974Labels = mixedMoment B raw3974step0 raw3974step0Labels := by
      have hz : ∀ j, raw3974 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3974step0 = (fun i j => raw3974 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3974step0 raw3974; decide +kernel
      have hl : raw3974step0Labels = raw3974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3974 raw3974Labels permutation346 hz
    mixedMoment B raw3974step0 raw3974step0Labels = mixedMoment B raw3974step1 raw3974step1Labels := by
      have ha : raw3974step1 = (fun i j => raw3974step0 (permutation134 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3974step1 raw3974step0; decide +kernel
      have hl : raw3974step1Labels = raw3974step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3974step0 raw3974step0Labels permutation134 permutation5
    mixedMoment B raw3974step1 raw3974step1Labels = mixedMoment B raw3974step2 raw3974step2Labels := by
      have ha : raw3974step2 = raw3974step1 := by apply Matrix.ext; unfold raw3974step2 raw3974step1; decide +kernel
      have hl : raw3974step1Labels = labelEmbedding1 ∘ raw3974step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3974step1 raw3974step1Labels raw3974step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

theorem canonical3975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3975 raw3975Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw3975 raw3975Labels = mixedMoment B raw3975step0 raw3975step0Labels := by
      have hz : ∀ j, raw3975 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3975step0 = (fun i j => raw3975 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3975step0 raw3975; decide +kernel
      have hl : raw3975step0Labels = raw3975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3975 raw3975Labels permutation434 hz
    mixedMoment B raw3975step0 raw3975step0Labels = mixedMoment B raw3975step1 raw3975step1Labels := by
      have hz : ∀ j, raw3975step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3975step1 = (fun i j => raw3975step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3975step1 raw3975step0; decide +kernel
      have hl : raw3975step1Labels = raw3975step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3975step0 raw3975step0Labels permutation80 hz
    mixedMoment B raw3975step1 raw3975step1Labels = mixedMoment B raw3975step2 raw3975step2Labels := by
      have ha : raw3975step2 = (fun i j => raw3975step1 (permutation20 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3975step2 raw3975step1; decide +kernel
      have hl : raw3975step2Labels = raw3975step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3975step1 raw3975step1Labels permutation20 permutation5
    mixedMoment B raw3975step2 raw3975step2Labels = mixedMoment B raw3975step3 raw3975step3Labels := by
      have ha : raw3975step3 = -raw3975step2 := by apply Matrix.ext; change ∀ i j, raw3975step3 i j = -(raw3975step2 i j); unfold raw3975step3 raw3975step2; decide +kernel
      have hl : raw3975step3Labels = raw3975step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3975step3 raw3975step3Labels = mixedMoment B raw3975step4 raw3975step4Labels := by
      have ha : raw3975step4 = raw3975step3 := by apply Matrix.ext; unfold raw3975step4 raw3975step3; decide +kernel
      have hl : raw3975step3Labels = labelEmbedding1 ∘ raw3975step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3975step3 raw3975step3Labels raw3975step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3052 node3052Labels := by rfl

theorem canonical3976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3976 raw3976Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw3976 raw3976Labels = mixedMoment B raw3976step0 raw3976step0Labels := by
      have hz : ∀ j, raw3976 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3976step0 = (fun i j => raw3976 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3976step0 raw3976; decide +kernel
      have hl : raw3976step0Labels = raw3976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3976 raw3976Labels permutation434 hz
    mixedMoment B raw3976step0 raw3976step0Labels = mixedMoment B raw3976step1 raw3976step1Labels := by
      have hz : ∀ j, raw3976step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3976step1 = (fun i j => raw3976step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3976step1 raw3976step0; decide +kernel
      have hl : raw3976step1Labels = raw3976step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3976step0 raw3976step0Labels permutation80 hz
    mixedMoment B raw3976step1 raw3976step1Labels = mixedMoment B raw3976step2 raw3976step2Labels := by
      have ha : raw3976step2 = (fun i j => raw3976step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3976step2 raw3976step1; decide +kernel
      have hl : raw3976step2Labels = raw3976step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3976step1 raw3976step1Labels permutation9 permutation7
    mixedMoment B raw3976step2 raw3976step2Labels = mixedMoment B raw3976step3 raw3976step3Labels := by
      have ha : raw3976step3 = -raw3976step2 := by apply Matrix.ext; change ∀ i j, raw3976step3 i j = -(raw3976step2 i j); unfold raw3976step3 raw3976step2; decide +kernel
      have hl : raw3976step3Labels = raw3976step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3976step3 raw3976step3Labels = mixedMoment B raw3976step4 raw3976step4Labels := by
      have ha : raw3976step4 = raw3976step3 := by apply Matrix.ext; unfold raw3976step4 raw3976step3; decide +kernel
      have hl : raw3976step3Labels = labelEmbedding1 ∘ raw3976step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3976step3 raw3976step3Labels raw3976step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3862 node3862Labels := by rfl

theorem canonical3977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3977 raw3977Labels = mixedMoment B node3247 node3247Labels := by
  calc
    mixedMoment B raw3977 raw3977Labels = mixedMoment B raw3977step0 raw3977step0Labels := by
      have hz : ∀ j, raw3977 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3977step0 = (fun i j => raw3977 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3977step0 raw3977; decide +kernel
      have hl : raw3977step0Labels = raw3977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3977 raw3977Labels permutation434 hz
    mixedMoment B raw3977step0 raw3977step0Labels = mixedMoment B raw3977step1 raw3977step1Labels := by
      have hz : ∀ j, raw3977step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3977step1 = (fun i j => raw3977step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3977step1 raw3977step0; decide +kernel
      have hl : raw3977step1Labels = raw3977step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3977step0 raw3977step0Labels permutation80 hz
    mixedMoment B raw3977step1 raw3977step1Labels = mixedMoment B raw3977step2 raw3977step2Labels := by
      have ha : raw3977step2 = (fun i j => raw3977step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3977step2 raw3977step1; decide +kernel
      have hl : raw3977step2Labels = raw3977step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3977step1 raw3977step1Labels permutation10 permutation5
    mixedMoment B raw3977step2 raw3977step2Labels = mixedMoment B raw3977step3 raw3977step3Labels := by
      have ha : raw3977step3 = -raw3977step2 := by apply Matrix.ext; change ∀ i j, raw3977step3 i j = -(raw3977step2 i j); unfold raw3977step3 raw3977step2; decide +kernel
      have hl : raw3977step3Labels = raw3977step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3977step3 raw3977step3Labels = mixedMoment B raw3977step4 raw3977step4Labels := by
      have ha : raw3977step4 = raw3977step3 := by apply Matrix.ext; unfold raw3977step4 raw3977step3; decide +kernel
      have hl : raw3977step3Labels = labelEmbedding1 ∘ raw3977step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3977step3 raw3977step3Labels raw3977step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3247 node3247Labels := by rfl

theorem canonical3978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3978 raw3978Labels = mixedMoment B node3358 node3358Labels := by
  calc
    mixedMoment B raw3978 raw3978Labels = mixedMoment B raw3978step0 raw3978step0Labels := by
      have hz : ∀ j, raw3978 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3978step0 = (fun i j => raw3978 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3978step0 raw3978; decide +kernel
      have hl : raw3978step0Labels = raw3978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3978 raw3978Labels permutation434 hz
    mixedMoment B raw3978step0 raw3978step0Labels = mixedMoment B raw3978step1 raw3978step1Labels := by
      have ha : raw3978step1 = (fun i j => raw3978step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3978step1 raw3978step0; decide +kernel
      have hl : raw3978step1Labels = raw3978step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3978step0 raw3978step0Labels permutation136 permutation5
    mixedMoment B raw3978step1 raw3978step1Labels = mixedMoment B raw3978step2 raw3978step2Labels := by
      have ha : raw3978step2 = raw3978step1 := by apply Matrix.ext; unfold raw3978step2 raw3978step1; decide +kernel
      have hl : raw3978step1Labels = labelEmbedding1 ∘ raw3978step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3978step1 raw3978step1Labels raw3978step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3358 node3358Labels := by rfl

theorem canonical3979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3979 raw3979Labels = mixedMoment B node3358 node3358Labels := by
  calc
    mixedMoment B raw3979 raw3979Labels = mixedMoment B raw3979step0 raw3979step0Labels := by
      have hz : ∀ j, raw3979 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3979step0 = (fun i j => raw3979 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3979step0 raw3979; decide +kernel
      have hl : raw3979step0Labels = raw3979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3979 raw3979Labels permutation346 hz
    mixedMoment B raw3979step0 raw3979step0Labels = mixedMoment B raw3979step1 raw3979step1Labels := by
      have ha : raw3979step1 = (fun i j => raw3979step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3979step1 raw3979step0; decide +kernel
      have hl : raw3979step1Labels = raw3979step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3979step0 raw3979step0Labels permutation136 permutation5
    mixedMoment B raw3979step1 raw3979step1Labels = mixedMoment B raw3979step2 raw3979step2Labels := by
      have ha : raw3979step2 = raw3979step1 := by apply Matrix.ext; unfold raw3979step2 raw3979step1; decide +kernel
      have hl : raw3979step1Labels = labelEmbedding1 ∘ raw3979step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3979step1 raw3979step1Labels raw3979step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3358 node3358Labels := by rfl

theorem canonical3980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3980 raw3980Labels = mixedMoment B node2842 node2842Labels := by
  calc
    mixedMoment B raw3980 raw3980Labels = mixedMoment B raw3980step0 raw3980step0Labels := by
      have hz : ∀ j, raw3980 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3980step0 = (fun i j => raw3980 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3980step0 raw3980; decide +kernel
      have hl : raw3980step0Labels = raw3980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3980 raw3980Labels permutation434 hz
    mixedMoment B raw3980step0 raw3980step0Labels = mixedMoment B raw3980step1 raw3980step1Labels := by
      have hz : ∀ j, raw3980step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3980step1 = (fun i j => raw3980step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3980step1 raw3980step0; decide +kernel
      have hl : raw3980step1Labels = raw3980step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3980step0 raw3980step0Labels permutation80 hz
    mixedMoment B raw3980step1 raw3980step1Labels = mixedMoment B raw3980step2 raw3980step2Labels := by
      have ha : raw3980step2 = (fun i j => raw3980step1 (permutation20 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3980step2 raw3980step1; decide +kernel
      have hl : raw3980step2Labels = raw3980step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3980step1 raw3980step1Labels permutation20 permutation5
    mixedMoment B raw3980step2 raw3980step2Labels = mixedMoment B raw3980step3 raw3980step3Labels := by
      have ha : raw3980step3 = -raw3980step2 := by apply Matrix.ext; change ∀ i j, raw3980step3 i j = -(raw3980step2 i j); unfold raw3980step3 raw3980step2; decide +kernel
      have hl : raw3980step3Labels = raw3980step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3980step3 raw3980step3Labels = mixedMoment B raw3980step4 raw3980step4Labels := by
      have ha : raw3980step4 = raw3980step3 := by apply Matrix.ext; unfold raw3980step4 raw3980step3; decide +kernel
      have hl : raw3980step3Labels = labelEmbedding1 ∘ raw3980step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3980step3 raw3980step3Labels raw3980step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2842 node2842Labels := by rfl

theorem canonical3981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3981 raw3981Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw3981 raw3981Labels = mixedMoment B raw3981step0 raw3981step0Labels := by
      have hz : ∀ j, raw3981 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3981step0 = (fun i j => raw3981 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3981step0 raw3981; decide +kernel
      have hl : raw3981step0Labels = raw3981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3981 raw3981Labels permutation434 hz
    mixedMoment B raw3981step0 raw3981step0Labels = mixedMoment B raw3981step1 raw3981step1Labels := by
      have hz : ∀ j, raw3981step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3981step1 = (fun i j => raw3981step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3981step1 raw3981step0; decide +kernel
      have hl : raw3981step1Labels = raw3981step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3981step0 raw3981step0Labels permutation80 hz
    mixedMoment B raw3981step1 raw3981step1Labels = mixedMoment B raw3981step2 raw3981step2Labels := by
      have ha : raw3981step2 = (fun i j => raw3981step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3981step2 raw3981step1; decide +kernel
      have hl : raw3981step2Labels = raw3981step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3981step1 raw3981step1Labels permutation9 permutation7
    mixedMoment B raw3981step2 raw3981step2Labels = mixedMoment B raw3981step3 raw3981step3Labels := by
      have ha : raw3981step3 = -raw3981step2 := by apply Matrix.ext; change ∀ i j, raw3981step3 i j = -(raw3981step2 i j); unfold raw3981step3 raw3981step2; decide +kernel
      have hl : raw3981step3Labels = raw3981step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3981step3 raw3981step3Labels = mixedMoment B raw3981step4 raw3981step4Labels := by
      have ha : raw3981step4 = raw3981step3 := by apply Matrix.ext; unfold raw3981step4 raw3981step3; decide +kernel
      have hl : raw3981step3Labels = labelEmbedding1 ∘ raw3981step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3981step3 raw3981step3Labels raw3981step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3584 node3584Labels := by rfl

theorem canonical3982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3982 raw3982Labels = mixedMoment B node3242 node3242Labels := by
  calc
    mixedMoment B raw3982 raw3982Labels = mixedMoment B raw3982step0 raw3982step0Labels := by
      have hz : ∀ j, raw3982 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3982step0 = (fun i j => raw3982 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3982step0 raw3982; decide +kernel
      have hl : raw3982step0Labels = raw3982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3982 raw3982Labels permutation434 hz
    mixedMoment B raw3982step0 raw3982step0Labels = mixedMoment B raw3982step1 raw3982step1Labels := by
      have ha : raw3982step1 = (fun i j => raw3982step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3982step1 raw3982step0; decide +kernel
      have hl : raw3982step1Labels = raw3982step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3982step0 raw3982step0Labels permutation44 permutation5
    mixedMoment B raw3982step1 raw3982step1Labels = mixedMoment B raw3982step2 raw3982step2Labels := by
      have ha : raw3982step2 = -raw3982step1 := by apply Matrix.ext; change ∀ i j, raw3982step2 i j = -(raw3982step1 i j); unfold raw3982step2 raw3982step1; decide +kernel
      have hl : raw3982step2Labels = raw3982step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3982step2 raw3982step2Labels = mixedMoment B raw3982step3 raw3982step3Labels := by
      have ha : raw3982step3 = raw3982step2 := by apply Matrix.ext; unfold raw3982step3 raw3982step2; decide +kernel
      have hl : raw3982step2Labels = labelEmbedding1 ∘ raw3982step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3982step2 raw3982step2Labels raw3982step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3242 node3242Labels := by rfl

theorem canonical3983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3983 raw3983Labels = mixedMoment B node3472 node3472Labels := by
  calc
    mixedMoment B raw3983 raw3983Labels = mixedMoment B raw3983step0 raw3983step0Labels := by
      have hz : ∀ j, raw3983 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3983step0 = (fun i j => raw3983 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3983step0 raw3983; decide +kernel
      have hl : raw3983step0Labels = raw3983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3983 raw3983Labels permutation434 hz
    mixedMoment B raw3983step0 raw3983step0Labels = mixedMoment B raw3983step1 raw3983step1Labels := by
      have ha : raw3983step1 = (fun i j => raw3983step0 (permutation142 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3983step1 raw3983step0; decide +kernel
      have hl : raw3983step1Labels = raw3983step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3983step0 raw3983step0Labels permutation142 permutation5
    mixedMoment B raw3983step1 raw3983step1Labels = mixedMoment B raw3983step2 raw3983step2Labels := by
      have ha : raw3983step2 = raw3983step1 := by apply Matrix.ext; unfold raw3983step2 raw3983step1; decide +kernel
      have hl : raw3983step1Labels = labelEmbedding1 ∘ raw3983step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3983step1 raw3983step1Labels raw3983step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3472 node3472Labels := by rfl

theorem canonical3984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3984 raw3984Labels = mixedMoment B node3437 node3437Labels := by
  calc
    mixedMoment B raw3984 raw3984Labels = mixedMoment B raw3984step0 raw3984step0Labels := by
      have ha : raw3984step0 = (fun i j => raw3984 (permutation631 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3984step0 raw3984; decide +kernel
      have hl : raw3984step0Labels = raw3984Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3984 raw3984Labels permutation631 permutation5
    mixedMoment B raw3984step0 raw3984step0Labels = mixedMoment B raw3984step1 raw3984step1Labels := by
      have ha : raw3984step1 = raw3984step0 := by apply Matrix.ext; unfold raw3984step1 raw3984step0; decide +kernel
      have hl : raw3984step0Labels = labelEmbedding1 ∘ raw3984step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3984step0 raw3984step0Labels raw3984step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3437 node3437Labels := by rfl

theorem canonical3985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3985 raw3985Labels = mixedMoment B node2837 node2837Labels := by
  calc
    mixedMoment B raw3985 raw3985Labels = mixedMoment B raw3985step0 raw3985step0Labels := by
      have hz : ∀ j, raw3985 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3985step0 = (fun i j => raw3985 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3985step0 raw3985; decide +kernel
      have hl : raw3985step0Labels = raw3985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3985 raw3985Labels permutation434 hz
    mixedMoment B raw3985step0 raw3985step0Labels = mixedMoment B raw3985step1 raw3985step1Labels := by
      have ha : raw3985step1 = (fun i j => raw3985step0 (permutation104 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3985step1 raw3985step0; decide +kernel
      have hl : raw3985step1Labels = raw3985step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3985step0 raw3985step0Labels permutation104 permutation5
    mixedMoment B raw3985step1 raw3985step1Labels = mixedMoment B raw3985step2 raw3985step2Labels := by
      have ha : raw3985step2 = -raw3985step1 := by apply Matrix.ext; change ∀ i j, raw3985step2 i j = -(raw3985step1 i j); unfold raw3985step2 raw3985step1; decide +kernel
      have hl : raw3985step2Labels = raw3985step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3985step2 raw3985step2Labels = mixedMoment B raw3985step3 raw3985step3Labels := by
      have ha : raw3985step3 = raw3985step2 := by apply Matrix.ext; unfold raw3985step3 raw3985step2; decide +kernel
      have hl : raw3985step2Labels = labelEmbedding1 ∘ raw3985step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3985step2 raw3985step2Labels raw3985step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2837 node2837Labels := by rfl

theorem canonical3986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3986 raw3986Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw3986 raw3986Labels = mixedMoment B raw3986step0 raw3986step0Labels := by
      have hz : ∀ j, raw3986 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3986step0 = (fun i j => raw3986 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3986step0 raw3986; decide +kernel
      have hl : raw3986step0Labels = raw3986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3986 raw3986Labels permutation434 hz
    mixedMoment B raw3986step0 raw3986step0Labels = mixedMoment B raw3986step1 raw3986step1Labels := by
      have ha : raw3986step1 = (fun i j => raw3986step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3986step1 raw3986step0; decide +kernel
      have hl : raw3986step1Labels = raw3986step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3986step0 raw3986step0Labels permutation33 permutation7
    mixedMoment B raw3986step1 raw3986step1Labels = mixedMoment B raw3986step2 raw3986step2Labels := by
      have ha : raw3986step2 = -raw3986step1 := by apply Matrix.ext; change ∀ i j, raw3986step2 i j = -(raw3986step1 i j); unfold raw3986step2 raw3986step1; decide +kernel
      have hl : raw3986step2Labels = raw3986step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3986step2 raw3986step2Labels = mixedMoment B raw3986step3 raw3986step3Labels := by
      have ha : raw3986step3 = raw3986step2 := by apply Matrix.ext; unfold raw3986step3 raw3986step2; decide +kernel
      have hl : raw3986step2Labels = labelEmbedding1 ∘ raw3986step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3986step2 raw3986step2Labels raw3986step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

theorem canonical3987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3987 raw3987Labels = mixedMoment B node3242 node3242Labels := by
  calc
    mixedMoment B raw3987 raw3987Labels = mixedMoment B raw3987step0 raw3987step0Labels := by
      have hz : ∀ j, raw3987 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3987step0 = (fun i j => raw3987 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3987step0 raw3987; decide +kernel
      have hl : raw3987step0Labels = raw3987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3987 raw3987Labels permutation346 hz
    mixedMoment B raw3987step0 raw3987step0Labels = mixedMoment B raw3987step1 raw3987step1Labels := by
      have ha : raw3987step1 = (fun i j => raw3987step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3987step1 raw3987step0; decide +kernel
      have hl : raw3987step1Labels = raw3987step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3987step0 raw3987step0Labels permutation44 permutation5
    mixedMoment B raw3987step1 raw3987step1Labels = mixedMoment B raw3987step2 raw3987step2Labels := by
      have ha : raw3987step2 = -raw3987step1 := by apply Matrix.ext; change ∀ i j, raw3987step2 i j = -(raw3987step1 i j); unfold raw3987step2 raw3987step1; decide +kernel
      have hl : raw3987step2Labels = raw3987step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3987step2 raw3987step2Labels = mixedMoment B raw3987step3 raw3987step3Labels := by
      have ha : raw3987step3 = raw3987step2 := by apply Matrix.ext; unfold raw3987step3 raw3987step2; decide +kernel
      have hl : raw3987step2Labels = labelEmbedding1 ∘ raw3987step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3987step2 raw3987step2Labels raw3987step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3242 node3242Labels := by rfl

theorem canonical3988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3988 raw3988Labels = mixedMoment B node3472 node3472Labels := by
  calc
    mixedMoment B raw3988 raw3988Labels = mixedMoment B raw3988step0 raw3988step0Labels := by
      have hz : ∀ j, raw3988 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3988step0 = (fun i j => raw3988 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3988step0 raw3988; decide +kernel
      have hl : raw3988step0Labels = raw3988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3988 raw3988Labels permutation346 hz
    mixedMoment B raw3988step0 raw3988step0Labels = mixedMoment B raw3988step1 raw3988step1Labels := by
      have ha : raw3988step1 = (fun i j => raw3988step0 (permutation142 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3988step1 raw3988step0; decide +kernel
      have hl : raw3988step1Labels = raw3988step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3988step0 raw3988step0Labels permutation142 permutation5
    mixedMoment B raw3988step1 raw3988step1Labels = mixedMoment B raw3988step2 raw3988step2Labels := by
      have ha : raw3988step2 = raw3988step1 := by apply Matrix.ext; unfold raw3988step2 raw3988step1; decide +kernel
      have hl : raw3988step1Labels = labelEmbedding1 ∘ raw3988step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3988step1 raw3988step1Labels raw3988step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3472 node3472Labels := by rfl

theorem canonical3989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3989 raw3989Labels = mixedMoment B node3437 node3437Labels := by
  calc
    mixedMoment B raw3989 raw3989Labels = mixedMoment B raw3989step0 raw3989step0Labels := by
      have ha : raw3989step0 = (fun i j => raw3989 (permutation652 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3989step0 raw3989; decide +kernel
      have hl : raw3989step0Labels = raw3989Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3989 raw3989Labels permutation652 permutation5
    mixedMoment B raw3989step0 raw3989step0Labels = mixedMoment B raw3989step1 raw3989step1Labels := by
      have ha : raw3989step1 = raw3989step0 := by apply Matrix.ext; unfold raw3989step1 raw3989step0; decide +kernel
      have hl : raw3989step0Labels = labelEmbedding1 ∘ raw3989step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3989step0 raw3989step0Labels raw3989step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3437 node3437Labels := by rfl

theorem canonical3990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3990 raw3990Labels = mixedMoment B node2837 node2837Labels := by
  calc
    mixedMoment B raw3990 raw3990Labels = mixedMoment B raw3990step0 raw3990step0Labels := by
      have hz : ∀ j, raw3990 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3990step0 = (fun i j => raw3990 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3990step0 raw3990; decide +kernel
      have hl : raw3990step0Labels = raw3990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3990 raw3990Labels permutation346 hz
    mixedMoment B raw3990step0 raw3990step0Labels = mixedMoment B raw3990step1 raw3990step1Labels := by
      have ha : raw3990step1 = (fun i j => raw3990step0 (permutation104 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3990step1 raw3990step0; decide +kernel
      have hl : raw3990step1Labels = raw3990step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3990step0 raw3990step0Labels permutation104 permutation5
    mixedMoment B raw3990step1 raw3990step1Labels = mixedMoment B raw3990step2 raw3990step2Labels := by
      have ha : raw3990step2 = -raw3990step1 := by apply Matrix.ext; change ∀ i j, raw3990step2 i j = -(raw3990step1 i j); unfold raw3990step2 raw3990step1; decide +kernel
      have hl : raw3990step2Labels = raw3990step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3990step2 raw3990step2Labels = mixedMoment B raw3990step3 raw3990step3Labels := by
      have ha : raw3990step3 = raw3990step2 := by apply Matrix.ext; unfold raw3990step3 raw3990step2; decide +kernel
      have hl : raw3990step2Labels = labelEmbedding1 ∘ raw3990step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3990step2 raw3990step2Labels raw3990step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2837 node2837Labels := by rfl

theorem canonical3991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3991 raw3991Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw3991 raw3991Labels = mixedMoment B raw3991step0 raw3991step0Labels := by
      have hz : ∀ j, raw3991 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3991step0 = (fun i j => raw3991 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3991step0 raw3991; decide +kernel
      have hl : raw3991step0Labels = raw3991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3991 raw3991Labels permutation346 hz
    mixedMoment B raw3991step0 raw3991step0Labels = mixedMoment B raw3991step1 raw3991step1Labels := by
      have ha : raw3991step1 = (fun i j => raw3991step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3991step1 raw3991step0; decide +kernel
      have hl : raw3991step1Labels = raw3991step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3991step0 raw3991step0Labels permutation33 permutation7
    mixedMoment B raw3991step1 raw3991step1Labels = mixedMoment B raw3991step2 raw3991step2Labels := by
      have ha : raw3991step2 = -raw3991step1 := by apply Matrix.ext; change ∀ i j, raw3991step2 i j = -(raw3991step1 i j); unfold raw3991step2 raw3991step1; decide +kernel
      have hl : raw3991step2Labels = raw3991step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3991step2 raw3991step2Labels = mixedMoment B raw3991step3 raw3991step3Labels := by
      have ha : raw3991step3 = raw3991step2 := by apply Matrix.ext; unfold raw3991step3 raw3991step2; decide +kernel
      have hl : raw3991step2Labels = labelEmbedding1 ∘ raw3991step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3991step2 raw3991step2Labels raw3991step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

theorem canonical3992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3992 raw3992Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw3992 raw3992Labels = mixedMoment B raw3992step0 raw3992step0Labels := by
      have hz : ∀ j, raw3992 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3992step0 = (fun i j => raw3992 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3992step0 raw3992; decide +kernel
      have hl : raw3992step0Labels = raw3992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3992 raw3992Labels permutation434 hz
    mixedMoment B raw3992step0 raw3992step0Labels = mixedMoment B raw3992step1 raw3992step1Labels := by
      have hz : ∀ j, raw3992step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3992step1 = (fun i j => raw3992step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3992step1 raw3992step0; decide +kernel
      have hl : raw3992step1Labels = raw3992step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3992step0 raw3992step0Labels permutation80 hz
    mixedMoment B raw3992step1 raw3992step1Labels = mixedMoment B raw3992step2 raw3992step2Labels := by
      have ha : raw3992step2 = (fun i j => raw3992step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3992step2 raw3992step1; decide +kernel
      have hl : raw3992step2Labels = raw3992step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3992step1 raw3992step1Labels permutation9 permutation7
    mixedMoment B raw3992step2 raw3992step2Labels = mixedMoment B raw3992step3 raw3992step3Labels := by
      have ha : raw3992step3 = -raw3992step2 := by apply Matrix.ext; change ∀ i j, raw3992step3 i j = -(raw3992step2 i j); unfold raw3992step3 raw3992step2; decide +kernel
      have hl : raw3992step3Labels = raw3992step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3992step3 raw3992step3Labels = mixedMoment B raw3992step4 raw3992step4Labels := by
      have ha : raw3992step4 = raw3992step3 := by apply Matrix.ext; unfold raw3992step4 raw3992step3; decide +kernel
      have hl : raw3992step3Labels = labelEmbedding1 ∘ raw3992step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3992step3 raw3992step3Labels raw3992step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3302 node3302Labels := by rfl

theorem canonical3993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3993 raw3993Labels = mixedMoment B node3486 node3486Labels := by
  calc
    mixedMoment B raw3993 raw3993Labels = mixedMoment B raw3993step0 raw3993step0Labels := by
      have hz : ∀ j, raw3993 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3993step0 = (fun i j => raw3993 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3993step0 raw3993; decide +kernel
      have hl : raw3993step0Labels = raw3993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3993 raw3993Labels permutation434 hz
    mixedMoment B raw3993step0 raw3993step0Labels = mixedMoment B raw3993step1 raw3993step1Labels := by
      have hz : ∀ j, raw3993step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3993step1 = (fun i j => raw3993step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3993step1 raw3993step0; decide +kernel
      have hl : raw3993step1Labels = raw3993step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3993step0 raw3993step0Labels permutation80 hz
    mixedMoment B raw3993step1 raw3993step1Labels = mixedMoment B raw3993step2 raw3993step2Labels := by
      have ha : raw3993step2 = (fun i j => raw3993step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3993step2 raw3993step1; decide +kernel
      have hl : raw3993step2Labels = raw3993step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3993step1 raw3993step1Labels permutation9 permutation7
    mixedMoment B raw3993step2 raw3993step2Labels = mixedMoment B raw3993step3 raw3993step3Labels := by
      have ha : raw3993step3 = -raw3993step2 := by apply Matrix.ext; change ∀ i j, raw3993step3 i j = -(raw3993step2 i j); unfold raw3993step3 raw3993step2; decide +kernel
      have hl : raw3993step3Labels = raw3993step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3993step3 raw3993step3Labels = mixedMoment B raw3993step4 raw3993step4Labels := by
      have ha : raw3993step4 = raw3993step3 := by apply Matrix.ext; unfold raw3993step4 raw3993step3; decide +kernel
      have hl : raw3993step3Labels = labelEmbedding1 ∘ raw3993step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3993step3 raw3993step3Labels raw3993step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3486 node3486Labels := by rfl

theorem canonical3994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3994 raw3994Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw3994 raw3994Labels = mixedMoment B raw3994step0 raw3994step0Labels := by
      have hz : ∀ j, raw3994 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3994step0 = (fun i j => raw3994 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3994step0 raw3994; decide +kernel
      have hl : raw3994step0Labels = raw3994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3994 raw3994Labels permutation434 hz
    mixedMoment B raw3994step0 raw3994step0Labels = mixedMoment B raw3994step1 raw3994step1Labels := by
      have ha : raw3994step1 = (fun i j => raw3994step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3994step1 raw3994step0; decide +kernel
      have hl : raw3994step1Labels = raw3994step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3994step0 raw3994step0Labels permutation33 permutation7
    mixedMoment B raw3994step1 raw3994step1Labels = mixedMoment B raw3994step2 raw3994step2Labels := by
      have ha : raw3994step2 = -raw3994step1 := by apply Matrix.ext; change ∀ i j, raw3994step2 i j = -(raw3994step1 i j); unfold raw3994step2 raw3994step1; decide +kernel
      have hl : raw3994step2Labels = raw3994step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3994step2 raw3994step2Labels = mixedMoment B raw3994step3 raw3994step3Labels := by
      have ha : raw3994step3 = raw3994step2 := by apply Matrix.ext; unfold raw3994step3 raw3994step2; decide +kernel
      have hl : raw3994step2Labels = labelEmbedding1 ∘ raw3994step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3994step2 raw3994step2Labels raw3994step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

theorem canonical3995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3995 raw3995Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw3995 raw3995Labels = mixedMoment B raw3995step0 raw3995step0Labels := by
      have hz : ∀ j, raw3995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3995step0 = (fun i j => raw3995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3995step0 raw3995; decide +kernel
      have hl : raw3995step0Labels = raw3995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3995 raw3995Labels permutation346 hz
    mixedMoment B raw3995step0 raw3995step0Labels = mixedMoment B raw3995step1 raw3995step1Labels := by
      have ha : raw3995step1 = (fun i j => raw3995step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3995step1 raw3995step0; decide +kernel
      have hl : raw3995step1Labels = raw3995step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3995step0 raw3995step0Labels permutation33 permutation7
    mixedMoment B raw3995step1 raw3995step1Labels = mixedMoment B raw3995step2 raw3995step2Labels := by
      have ha : raw3995step2 = -raw3995step1 := by apply Matrix.ext; change ∀ i j, raw3995step2 i j = -(raw3995step1 i j); unfold raw3995step2 raw3995step1; decide +kernel
      have hl : raw3995step2Labels = raw3995step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3995step2 raw3995step2Labels = mixedMoment B raw3995step3 raw3995step3Labels := by
      have ha : raw3995step3 = raw3995step2 := by apply Matrix.ext; unfold raw3995step3 raw3995step2; decide +kernel
      have hl : raw3995step2Labels = labelEmbedding1 ∘ raw3995step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3995step2 raw3995step2Labels raw3995step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

theorem canonical3996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3996 raw3996Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw3996 raw3996Labels = mixedMoment B raw3996step0 raw3996step0Labels := by
      have hz : ∀ j, raw3996 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3996step0 = (fun i j => raw3996 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3996step0 raw3996; decide +kernel
      have hl : raw3996step0Labels = raw3996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3996 raw3996Labels permutation434 hz
    mixedMoment B raw3996step0 raw3996step0Labels = mixedMoment B raw3996step1 raw3996step1Labels := by
      have hz : ∀ j, raw3996step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3996step1 = (fun i j => raw3996step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3996step1 raw3996step0; decide +kernel
      have hl : raw3996step1Labels = raw3996step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3996step0 raw3996step0Labels permutation80 hz
    mixedMoment B raw3996step1 raw3996step1Labels = mixedMoment B raw3996step2 raw3996step2Labels := by
      have ha : raw3996step2 = (fun i j => raw3996step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3996step2 raw3996step1; decide +kernel
      have hl : raw3996step2Labels = raw3996step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3996step1 raw3996step1Labels permutation9 permutation7
    mixedMoment B raw3996step2 raw3996step2Labels = mixedMoment B raw3996step3 raw3996step3Labels := by
      have ha : raw3996step3 = -raw3996step2 := by apply Matrix.ext; change ∀ i j, raw3996step3 i j = -(raw3996step2 i j); unfold raw3996step3 raw3996step2; decide +kernel
      have hl : raw3996step3Labels = raw3996step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3996step3 raw3996step3Labels = mixedMoment B raw3996step4 raw3996step4Labels := by
      have ha : raw3996step4 = raw3996step3 := by apply Matrix.ext; unfold raw3996step4 raw3996step3; decide +kernel
      have hl : raw3996step3Labels = labelEmbedding1 ∘ raw3996step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3996step3 raw3996step3Labels raw3996step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3548 node3548Labels := by rfl

theorem canonical3997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3997 raw3997Labels = mixedMoment B node1629 node1629Labels := by
  calc
    mixedMoment B raw3997 raw3997Labels = mixedMoment B raw3997step0 raw3997step0Labels := by
      have hz : ∀ j, raw3997 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3997step0 = (fun i j => raw3997 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3997step0 raw3997; decide +kernel
      have hl : raw3997step0Labels = raw3997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3997 raw3997Labels permutation434 hz
    mixedMoment B raw3997step0 raw3997step0Labels = mixedMoment B raw3997step1 raw3997step1Labels := by
      have hz : ∀ j, raw3997step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3997step1 = (fun i j => raw3997step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3997step1 raw3997step0; decide +kernel
      have hl : raw3997step1Labels = raw3997step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3997step0 raw3997step0Labels permutation80 hz
    mixedMoment B raw3997step1 raw3997step1Labels = mixedMoment B raw3997step2 raw3997step2Labels := by
      have ha : raw3997step2 = (fun i j => raw3997step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3997step2 raw3997step1; decide +kernel
      have hl : raw3997step2Labels = raw3997step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3997step1 raw3997step1Labels permutation29 permutation5
    mixedMoment B raw3997step2 raw3997step2Labels = mixedMoment B raw3997step3 raw3997step3Labels := by
      have ha : raw3997step3 = raw3997step2 := by apply Matrix.ext; unfold raw3997step3 raw3997step2; decide +kernel
      have hl : raw3997step2Labels = labelEmbedding1 ∘ raw3997step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3997step2 raw3997step2Labels raw3997step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1629 node1629Labels := by rfl

theorem canonical3998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3998 raw3998Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw3998 raw3998Labels = mixedMoment B raw3998step0 raw3998step0Labels := by
      have hz : ∀ j, raw3998 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3998step0 = (fun i j => raw3998 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3998step0 raw3998; decide +kernel
      have hl : raw3998step0Labels = raw3998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3998 raw3998Labels permutation434 hz
    mixedMoment B raw3998step0 raw3998step0Labels = mixedMoment B raw3998step1 raw3998step1Labels := by
      have hz : ∀ j, raw3998step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3998step1 = (fun i j => raw3998step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3998step1 raw3998step0; decide +kernel
      have hl : raw3998step1Labels = raw3998step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3998step0 raw3998step0Labels permutation80 hz
    mixedMoment B raw3998step1 raw3998step1Labels = mixedMoment B raw3998step2 raw3998step2Labels := by
      have ha : raw3998step2 = (fun i j => raw3998step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3998step2 raw3998step1; decide +kernel
      have hl : raw3998step2Labels = raw3998step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3998step1 raw3998step1Labels permutation28 permutation5
    mixedMoment B raw3998step2 raw3998step2Labels = mixedMoment B raw3998step3 raw3998step3Labels := by
      have ha : raw3998step3 = raw3998step2 := by apply Matrix.ext; unfold raw3998step3 raw3998step2; decide +kernel
      have hl : raw3998step2Labels = labelEmbedding1 ∘ raw3998step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3998step2 raw3998step2Labels raw3998step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1729 node1729Labels := by rfl

theorem canonical3999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3999 raw3999Labels = mixedMoment B node1624 node1624Labels := by
  calc
    mixedMoment B raw3999 raw3999Labels = mixedMoment B raw3999step0 raw3999step0Labels := by
      have hz : ∀ j, raw3999 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3999step0 = (fun i j => raw3999 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3999step0 raw3999; decide +kernel
      have hl : raw3999step0Labels = raw3999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3999 raw3999Labels permutation434 hz
    mixedMoment B raw3999step0 raw3999step0Labels = mixedMoment B raw3999step1 raw3999step1Labels := by
      have ha : raw3999step1 = (fun i j => raw3999step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3999step1 raw3999step0; decide +kernel
      have hl : raw3999step1Labels = raw3999step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3999step0 raw3999step0Labels permutation136 permutation5
    mixedMoment B raw3999step1 raw3999step1Labels = mixedMoment B raw3999step2 raw3999step2Labels := by
      have ha : raw3999step2 = raw3999step1 := by apply Matrix.ext; unfold raw3999step2 raw3999step1; decide +kernel
      have hl : raw3999step1Labels = labelEmbedding1 ∘ raw3999step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3999step1 raw3999step1Labels raw3999step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1624 node1624Labels := by rfl

theorem canonical4000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4000 raw4000Labels = mixedMoment B node1624 node1624Labels := by
  calc
    mixedMoment B raw4000 raw4000Labels = mixedMoment B raw4000step0 raw4000step0Labels := by
      have hz : ∀ j, raw4000 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4000step0 = (fun i j => raw4000 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4000step0 raw4000; decide +kernel
      have hl : raw4000step0Labels = raw4000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4000 raw4000Labels permutation346 hz
    mixedMoment B raw4000step0 raw4000step0Labels = mixedMoment B raw4000step1 raw4000step1Labels := by
      have ha : raw4000step1 = (fun i j => raw4000step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4000step1 raw4000step0; decide +kernel
      have hl : raw4000step1Labels = raw4000step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4000step0 raw4000step0Labels permutation136 permutation5
    mixedMoment B raw4000step1 raw4000step1Labels = mixedMoment B raw4000step2 raw4000step2Labels := by
      have ha : raw4000step2 = raw4000step1 := by apply Matrix.ext; unfold raw4000step2 raw4000step1; decide +kernel
      have hl : raw4000step1Labels = labelEmbedding1 ∘ raw4000step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4000step1 raw4000step1Labels raw4000step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1624 node1624Labels := by rfl

theorem canonical4001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4001 raw4001Labels = mixedMoment B node1628 node1628Labels := by
  calc
    mixedMoment B raw4001 raw4001Labels = mixedMoment B raw4001step0 raw4001step0Labels := by
      have hz : ∀ j, raw4001 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4001step0 = (fun i j => raw4001 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4001step0 raw4001; decide +kernel
      have hl : raw4001step0Labels = raw4001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4001 raw4001Labels permutation434 hz
    mixedMoment B raw4001step0 raw4001step0Labels = mixedMoment B raw4001step1 raw4001step1Labels := by
      have hz : ∀ j, raw4001step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4001step1 = (fun i j => raw4001step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4001step1 raw4001step0; decide +kernel
      have hl : raw4001step1Labels = raw4001step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4001step0 raw4001step0Labels permutation80 hz
    mixedMoment B raw4001step1 raw4001step1Labels = mixedMoment B raw4001step2 raw4001step2Labels := by
      have ha : raw4001step2 = (fun i j => raw4001step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4001step2 raw4001step1; decide +kernel
      have hl : raw4001step2Labels = raw4001step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4001step1 raw4001step1Labels permutation28 permutation5
    mixedMoment B raw4001step2 raw4001step2Labels = mixedMoment B raw4001step3 raw4001step3Labels := by
      have ha : raw4001step3 = raw4001step2 := by apply Matrix.ext; unfold raw4001step3 raw4001step2; decide +kernel
      have hl : raw4001step2Labels = labelEmbedding1 ∘ raw4001step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4001step2 raw4001step2Labels raw4001step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1628 node1628Labels := by rfl

theorem canonical4002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4002 raw4002Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw4002 raw4002Labels = mixedMoment B raw4002step0 raw4002step0Labels := by
      have hz : ∀ j, raw4002 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4002step0 = (fun i j => raw4002 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4002step0 raw4002; decide +kernel
      have hl : raw4002step0Labels = raw4002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4002 raw4002Labels permutation434 hz
    mixedMoment B raw4002step0 raw4002step0Labels = mixedMoment B raw4002step1 raw4002step1Labels := by
      have hz : ∀ j, raw4002step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4002step1 = (fun i j => raw4002step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4002step1 raw4002step0; decide +kernel
      have hl : raw4002step1Labels = raw4002step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4002step0 raw4002step0Labels permutation80 hz
    _ = mixedMoment B node2734 node2734Labels := by rfl

theorem canonical4003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4003 raw4003Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw4003 raw4003Labels = mixedMoment B raw4003step0 raw4003step0Labels := by
      have hz : ∀ j, raw4003 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4003step0 = (fun i j => raw4003 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4003step0 raw4003; decide +kernel
      have hl : raw4003step0Labels = raw4003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4003 raw4003Labels permutation434 hz
    mixedMoment B raw4003step0 raw4003step0Labels = mixedMoment B raw4003step1 raw4003step1Labels := by
      have hz : ∀ j, raw4003step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4003step1 = (fun i j => raw4003step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4003step1 raw4003step0; decide +kernel
      have hl : raw4003step1Labels = raw4003step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4003step0 raw4003step0Labels permutation80 hz
    mixedMoment B raw4003step1 raw4003step1Labels = mixedMoment B raw4003step2 raw4003step2Labels := by
      have ha : raw4003step2 = (fun i j => raw4003step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4003step2 raw4003step1; decide +kernel
      have hl : raw4003step2Labels = raw4003step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4003step1 raw4003step1Labels permutation31 permutation2
    mixedMoment B raw4003step2 raw4003step2Labels = mixedMoment B raw4003step3 raw4003step3Labels := by
      have ha : raw4003step3 = -raw4003step2 := by apply Matrix.ext; change ∀ i j, raw4003step3 i j = -(raw4003step2 i j); unfold raw4003step3 raw4003step2; decide +kernel
      have hl : raw4003step3Labels = raw4003step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3054 node3054Labels := by rfl

theorem canonical4004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4004 raw4004Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw4004 raw4004Labels = mixedMoment B raw4004step0 raw4004step0Labels := by
      have hz : ∀ j, raw4004 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4004step0 = (fun i j => raw4004 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4004step0 raw4004; decide +kernel
      have hl : raw4004step0Labels = raw4004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4004 raw4004Labels permutation434 hz
    mixedMoment B raw4004step0 raw4004step0Labels = mixedMoment B raw4004step1 raw4004step1Labels := by
      have ha : raw4004step1 = (fun i j => raw4004step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4004step1 raw4004step0; decide +kernel
      have hl : raw4004step1Labels = raw4004step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4004step0 raw4004step0Labels permutation149 permutation2
    mixedMoment B raw4004step1 raw4004step1Labels = mixedMoment B raw4004step2 raw4004step2Labels := by
      have ha : raw4004step2 = -raw4004step1 := by apply Matrix.ext; change ∀ i j, raw4004step2 i j = -(raw4004step1 i j); unfold raw4004step2 raw4004step1; decide +kernel
      have hl : raw4004step2Labels = raw4004step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3038 node3038Labels := by rfl

theorem canonical4005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4005 raw4005Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw4005 raw4005Labels = mixedMoment B raw4005step0 raw4005step0Labels := by
      have hz : ∀ j, raw4005 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4005step0 = (fun i j => raw4005 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4005step0 raw4005; decide +kernel
      have hl : raw4005step0Labels = raw4005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4005 raw4005Labels permutation346 hz
    mixedMoment B raw4005step0 raw4005step0Labels = mixedMoment B raw4005step1 raw4005step1Labels := by
      have ha : raw4005step1 = (fun i j => raw4005step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4005step1 raw4005step0; decide +kernel
      have hl : raw4005step1Labels = raw4005step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4005step0 raw4005step0Labels permutation149 permutation2
    mixedMoment B raw4005step1 raw4005step1Labels = mixedMoment B raw4005step2 raw4005step2Labels := by
      have ha : raw4005step2 = -raw4005step1 := by apply Matrix.ext; change ∀ i j, raw4005step2 i j = -(raw4005step1 i j); unfold raw4005step2 raw4005step1; decide +kernel
      have hl : raw4005step2Labels = raw4005step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3038 node3038Labels := by rfl

theorem canonical4006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4006 raw4006Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw4006 raw4006Labels = mixedMoment B raw4006step0 raw4006step0Labels := by
      have hz : ∀ j, raw4006 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4006step0 = (fun i j => raw4006 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4006step0 raw4006; decide +kernel
      have hl : raw4006step0Labels = raw4006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4006 raw4006Labels permutation434 hz
    mixedMoment B raw4006step0 raw4006step0Labels = mixedMoment B raw4006step1 raw4006step1Labels := by
      have hz : ∀ j, raw4006step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4006step1 = (fun i j => raw4006step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4006step1 raw4006step0; decide +kernel
      have hl : raw4006step1Labels = raw4006step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4006step0 raw4006step0Labels permutation80 hz
    mixedMoment B raw4006step1 raw4006step1Labels = mixedMoment B raw4006step2 raw4006step2Labels := by
      have ha : raw4006step2 = (fun i j => raw4006step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4006step2 raw4006step1; decide +kernel
      have hl : raw4006step2Labels = raw4006step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4006step1 raw4006step1Labels permutation20 permutation4
    mixedMoment B raw4006step2 raw4006step2Labels = mixedMoment B raw4006step3 raw4006step3Labels := by
      have ha : raw4006step3 = -raw4006step2 := by apply Matrix.ext; change ∀ i j, raw4006step3 i j = -(raw4006step2 i j); unfold raw4006step3 raw4006step2; decide +kernel
      have hl : raw4006step3Labels = raw4006step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2777 node2777Labels := by rfl

theorem canonical4007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4007 raw4007Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw4007 raw4007Labels = mixedMoment B raw4007step0 raw4007step0Labels := by
      have hz : ∀ j, raw4007 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4007step0 = (fun i j => raw4007 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4007step0 raw4007; decide +kernel
      have hl : raw4007step0Labels = raw4007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4007 raw4007Labels permutation434 hz
    mixedMoment B raw4007step0 raw4007step0Labels = mixedMoment B raw4007step1 raw4007step1Labels := by
      have hz : ∀ j, raw4007step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4007step1 = (fun i j => raw4007step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4007step1 raw4007step0; decide +kernel
      have hl : raw4007step1Labels = raw4007step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4007step0 raw4007step0Labels permutation80 hz
    _ = mixedMoment B node3907 node3907Labels := by rfl

theorem canonical4008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4008 raw4008Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw4008 raw4008Labels = mixedMoment B raw4008step0 raw4008step0Labels := by
      have hz : ∀ j, raw4008 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4008step0 = (fun i j => raw4008 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4008step0 raw4008; decide +kernel
      have hl : raw4008step0Labels = raw4008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4008 raw4008Labels permutation434 hz
    mixedMoment B raw4008step0 raw4008step0Labels = mixedMoment B raw4008step1 raw4008step1Labels := by
      have hz : ∀ j, raw4008step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4008step1 = (fun i j => raw4008step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4008step1 raw4008step0; decide +kernel
      have hl : raw4008step1Labels = raw4008step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4008step0 raw4008step0Labels permutation80 hz
    mixedMoment B raw4008step1 raw4008step1Labels = mixedMoment B raw4008step2 raw4008step2Labels := by
      have ha : raw4008step2 = (fun i j => raw4008step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw4008step2 raw4008step1; decide +kernel
      have hl : raw4008step2Labels = raw4008step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4008step1 raw4008step1Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical4009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4009 raw4009Labels = mixedMoment B node1279 node1279Labels := by
  calc
    mixedMoment B raw4009 raw4009Labels = mixedMoment B raw4009step0 raw4009step0Labels := by
      have hz : ∀ j, raw4009 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4009step0 = (fun i j => raw4009 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4009step0 raw4009; decide +kernel
      have hl : raw4009step0Labels = raw4009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4009 raw4009Labels permutation434 hz
    mixedMoment B raw4009step0 raw4009step0Labels = mixedMoment B raw4009step1 raw4009step1Labels := by
      have hz : ∀ j, raw4009step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4009step1 = (fun i j => raw4009step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4009step1 raw4009step0; decide +kernel
      have hl : raw4009step1Labels = raw4009step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4009step0 raw4009step0Labels permutation80 hz
    mixedMoment B raw4009step1 raw4009step1Labels = mixedMoment B raw4009step2 raw4009step2Labels := by
      have ha : raw4009step2 = (fun i j => raw4009step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4009step2 raw4009step1; decide +kernel
      have hl : raw4009step2Labels = raw4009step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4009step1 raw4009step1Labels permutation10 permutation2
    _ = mixedMoment B node1279 node1279Labels := by rfl

theorem canonical4010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4010 raw4010Labels = mixedMoment B node1224 node1224Labels := by
  calc
    mixedMoment B raw4010 raw4010Labels = mixedMoment B raw4010step0 raw4010step0Labels := by
      have hz : ∀ j, raw4010 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4010step0 = (fun i j => raw4010 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4010step0 raw4010; decide +kernel
      have hl : raw4010step0Labels = raw4010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4010 raw4010Labels permutation434 hz
    mixedMoment B raw4010step0 raw4010step0Labels = mixedMoment B raw4010step1 raw4010step1Labels := by
      have ha : raw4010step1 = (fun i j => raw4010step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4010step1 raw4010step0; decide +kernel
      have hl : raw4010step1Labels = raw4010step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4010step0 raw4010step0Labels permutation34 permutation2
    _ = mixedMoment B node1224 node1224Labels := by rfl

theorem canonical4011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4011 raw4011Labels = mixedMoment B node1224 node1224Labels := by
  calc
    mixedMoment B raw4011 raw4011Labels = mixedMoment B raw4011step0 raw4011step0Labels := by
      have hz : ∀ j, raw4011 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4011step0 = (fun i j => raw4011 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4011step0 raw4011; decide +kernel
      have hl : raw4011step0Labels = raw4011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4011 raw4011Labels permutation346 hz
    mixedMoment B raw4011step0 raw4011step0Labels = mixedMoment B raw4011step1 raw4011step1Labels := by
      have ha : raw4011step1 = (fun i j => raw4011step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4011step1 raw4011step0; decide +kernel
      have hl : raw4011step1Labels = raw4011step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4011step0 raw4011step0Labels permutation34 permutation2
    _ = mixedMoment B node1224 node1224Labels := by rfl

theorem canonical4012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4012 raw4012Labels = mixedMoment B node1243 node1243Labels := by
  calc
    mixedMoment B raw4012 raw4012Labels = mixedMoment B raw4012step0 raw4012step0Labels := by
      have hz : ∀ j, raw4012 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4012step0 = (fun i j => raw4012 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4012step0 raw4012; decide +kernel
      have hl : raw4012step0Labels = raw4012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4012 raw4012Labels permutation434 hz
    mixedMoment B raw4012step0 raw4012step0Labels = mixedMoment B raw4012step1 raw4012step1Labels := by
      have hz : ∀ j, raw4012step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4012step1 = (fun i j => raw4012step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4012step1 raw4012step0; decide +kernel
      have hl : raw4012step1Labels = raw4012step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4012step0 raw4012step0Labels permutation80 hz
    _ = mixedMoment B node1243 node1243Labels := by rfl

theorem canonical4013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4013 raw4013Labels = mixedMoment B node1227 node1227Labels := by
  calc
    mixedMoment B raw4013 raw4013Labels = mixedMoment B raw4013step0 raw4013step0Labels := by
      have hz : ∀ j, raw4013 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4013step0 = (fun i j => raw4013 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4013step0 raw4013; decide +kernel
      have hl : raw4013step0Labels = raw4013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4013 raw4013Labels permutation434 hz
    mixedMoment B raw4013step0 raw4013step0Labels = mixedMoment B raw4013step1 raw4013step1Labels := by
      have hz : ∀ j, raw4013step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4013step1 = (fun i j => raw4013step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4013step1 raw4013step0; decide +kernel
      have hl : raw4013step1Labels = raw4013step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4013step0 raw4013step0Labels permutation80 hz
    _ = mixedMoment B node1227 node1227Labels := by rfl

theorem canonical4014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4014 raw4014Labels = mixedMoment B node2579 node2579Labels := by
  calc
    mixedMoment B raw4014 raw4014Labels = mixedMoment B raw4014step0 raw4014step0Labels := by
      have hz : ∀ j, raw4014 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4014step0 = (fun i j => raw4014 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4014step0 raw4014; decide +kernel
      have hl : raw4014step0Labels = raw4014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4014 raw4014Labels permutation434 hz
    mixedMoment B raw4014step0 raw4014step0Labels = mixedMoment B raw4014step1 raw4014step1Labels := by
      have ha : raw4014step1 = (fun i j => raw4014step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4014step1 raw4014step0; decide +kernel
      have hl : raw4014step1Labels = raw4014step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4014step0 raw4014step0Labels permutation40 permutation2
    _ = mixedMoment B node2579 node2579Labels := by rfl

theorem canonical4015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4015 raw4015Labels = mixedMoment B node2579 node2579Labels := by
  calc
    mixedMoment B raw4015 raw4015Labels = mixedMoment B raw4015step0 raw4015step0Labels := by
      have hz : ∀ j, raw4015 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4015step0 = (fun i j => raw4015 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4015step0 raw4015; decide +kernel
      have hl : raw4015step0Labels = raw4015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4015 raw4015Labels permutation346 hz
    mixedMoment B raw4015step0 raw4015step0Labels = mixedMoment B raw4015step1 raw4015step1Labels := by
      have ha : raw4015step1 = (fun i j => raw4015step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4015step1 raw4015step0; decide +kernel
      have hl : raw4015step1Labels = raw4015step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4015step0 raw4015step0Labels permutation40 permutation2
    _ = mixedMoment B node2579 node2579Labels := by rfl

theorem canonical4016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4016 raw4016Labels = mixedMoment B node2651 node2651Labels := by
  calc
    mixedMoment B raw4016 raw4016Labels = mixedMoment B raw4016step0 raw4016step0Labels := by
      have hz : ∀ j, raw4016 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4016step0 = (fun i j => raw4016 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4016step0 raw4016; decide +kernel
      have hl : raw4016step0Labels = raw4016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4016 raw4016Labels permutation434 hz
    mixedMoment B raw4016step0 raw4016step0Labels = mixedMoment B raw4016step1 raw4016step1Labels := by
      have hz : ∀ j, raw4016step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4016step1 = (fun i j => raw4016step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4016step1 raw4016step0; decide +kernel
      have hl : raw4016step1Labels = raw4016step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4016step0 raw4016step0Labels permutation80 hz
    mixedMoment B raw4016step1 raw4016step1Labels = mixedMoment B raw4016step2 raw4016step2Labels := by
      have ha : raw4016step2 = (fun i j => raw4016step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4016step2 raw4016step1; decide +kernel
      have hl : raw4016step2Labels = raw4016step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4016step1 raw4016step1Labels permutation10 permutation2
    _ = mixedMoment B node2651 node2651Labels := by rfl

theorem canonical4017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4017 raw4017Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw4017 raw4017Labels = mixedMoment B raw4017step0 raw4017step0Labels := by
      have hz : ∀ j, raw4017 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4017step0 = (fun i j => raw4017 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4017step0 raw4017; decide +kernel
      have hl : raw4017step0Labels = raw4017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4017 raw4017Labels permutation434 hz
    mixedMoment B raw4017step0 raw4017step0Labels = mixedMoment B raw4017step1 raw4017step1Labels := by
      have hz : ∀ j, raw4017step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4017step1 = (fun i j => raw4017step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4017step1 raw4017step0; decide +kernel
      have hl : raw4017step1Labels = raw4017step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4017step0 raw4017step0Labels permutation80 hz
    mixedMoment B raw4017step1 raw4017step1Labels = mixedMoment B raw4017step2 raw4017step2Labels := by
      have ha : raw4017step2 = (fun i j => raw4017step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4017step2 raw4017step1; decide +kernel
      have hl : raw4017step2Labels = raw4017step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4017step1 raw4017step1Labels permutation10 permutation2
    _ = mixedMoment B node2774 node2774Labels := by rfl

theorem canonical4018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4018 raw4018Labels = mixedMoment B node2495 node2495Labels := by
  calc
    mixedMoment B raw4018 raw4018Labels = mixedMoment B raw4018step0 raw4018step0Labels := by
      have hz : ∀ j, raw4018 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4018step0 = (fun i j => raw4018 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4018step0 raw4018; decide +kernel
      have hl : raw4018step0Labels = raw4018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4018 raw4018Labels permutation434 hz
    mixedMoment B raw4018step0 raw4018step0Labels = mixedMoment B raw4018step1 raw4018step1Labels := by
      have ha : raw4018step1 = (fun i j => raw4018step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4018step1 raw4018step0; decide +kernel
      have hl : raw4018step1Labels = raw4018step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4018step0 raw4018step0Labels permutation34 permutation2
    _ = mixedMoment B node2495 node2495Labels := by rfl

theorem canonical4019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4019 raw4019Labels = mixedMoment B node2495 node2495Labels := by
  calc
    mixedMoment B raw4019 raw4019Labels = mixedMoment B raw4019step0 raw4019step0Labels := by
      have hz : ∀ j, raw4019 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4019step0 = (fun i j => raw4019 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4019step0 raw4019; decide +kernel
      have hl : raw4019step0Labels = raw4019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4019 raw4019Labels permutation346 hz
    mixedMoment B raw4019step0 raw4019step0Labels = mixedMoment B raw4019step1 raw4019step1Labels := by
      have ha : raw4019step1 = (fun i j => raw4019step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4019step1 raw4019step0; decide +kernel
      have hl : raw4019step1Labels = raw4019step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4019step0 raw4019step0Labels permutation34 permutation2
    _ = mixedMoment B node2495 node2495Labels := by rfl

theorem canonical4020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4020 raw4020Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw4020 raw4020Labels = mixedMoment B raw4020step0 raw4020step0Labels := by
      have hz : ∀ j, raw4020 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4020step0 = (fun i j => raw4020 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4020step0 raw4020; decide +kernel
      have hl : raw4020step0Labels = raw4020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4020 raw4020Labels permutation434 hz
    mixedMoment B raw4020step0 raw4020step0Labels = mixedMoment B raw4020step1 raw4020step1Labels := by
      have hz : ∀ j, raw4020step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4020step1 = (fun i j => raw4020step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4020step1 raw4020step0; decide +kernel
      have hl : raw4020step1Labels = raw4020step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4020step0 raw4020step0Labels permutation80 hz
    _ = mixedMoment B node2519 node2519Labels := by rfl

theorem canonical4021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4021 raw4021Labels = mixedMoment B node1372 node1372Labels := by
  calc
    mixedMoment B raw4021 raw4021Labels = mixedMoment B raw4021step0 raw4021step0Labels := by
      have hz : ∀ j, raw4021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4021step0 = (fun i j => raw4021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4021step0 raw4021; decide +kernel
      have hl : raw4021step0Labels = raw4021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4021 raw4021Labels permutation434 hz
    mixedMoment B raw4021step0 raw4021step0Labels = mixedMoment B raw4021step1 raw4021step1Labels := by
      have hz : ∀ j, raw4021step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4021step1 = (fun i j => raw4021step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4021step1 raw4021step0; decide +kernel
      have hl : raw4021step1Labels = raw4021step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4021step0 raw4021step0Labels permutation80 hz
    mixedMoment B raw4021step1 raw4021step1Labels = mixedMoment B raw4021step2 raw4021step2Labels := by
      have ha : raw4021step2 = (fun i j => raw4021step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4021step2 raw4021step1; decide +kernel
      have hl : raw4021step2Labels = raw4021step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4021step1 raw4021step1Labels permutation31 permutation2
    mixedMoment B raw4021step2 raw4021step2Labels = mixedMoment B raw4021step3 raw4021step3Labels := by
      have ha : raw4021step3 = -raw4021step2 := by apply Matrix.ext; change ∀ i j, raw4021step3 i j = -(raw4021step2 i j); unfold raw4021step3 raw4021step2; decide +kernel
      have hl : raw4021step3Labels = raw4021step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1372 node1372Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw536 raw536Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw536 raw536Labels = mixedMoment B raw536step0 raw536step0Labels := by
      have ha : raw536step0 = (fun i j => raw536 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw536step0 raw536; decide +kernel
      have hl : raw536step0Labels = raw536Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw536 raw536Labels permutation8 permutation5
    mixedMoment B raw536step0 raw536step0Labels = mixedMoment B raw536step1 raw536step1Labels := by
      have ha : raw536step1 = raw536step0 := by apply Matrix.ext; unfold raw536step1 raw536step0; decide +kernel
      have hl : raw536step0Labels = labelEmbedding1 ∘ raw536step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw536step0 raw536step0Labels raw536step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3862 node3862Labels := by rfl

theorem canonical537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw537 raw537Labels = mixedMoment B node496 node496Labels := by
  calc
    mixedMoment B raw537 raw537Labels = mixedMoment B raw537step0 raw537step0Labels := by
      have ha : raw537step0 = (fun i j => raw537 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw537step0 raw537; decide +kernel
      have hl : raw537step0Labels = raw537Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw537 raw537Labels permutation8 permutation5
    _ = mixedMoment B node496 node496Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3963 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3963 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw3963 = injectiveMoment H raw3963step0 := by
      have heq : raw3963step0 = -raw3963 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3963).symm
    injectiveMoment H raw3963step0 = injectiveMoment H raw3963step1 := by
      have heq : raw3963step1 = (fun i j => raw3963step0 (permutation10 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3963step0 permutation10 permutation8
    _ = injectiveMoment H node203 := by rfl

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

theorem canonical5141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5141 = injectiveMoment H node46 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5185 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5185 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw5185 = injectiveMoment H raw5185step0 := by
      have hz : ∀ j, raw5185 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5185step0 = (fun i j => raw5185 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5185 permutation27 hz
    injectiveMoment H raw5185step0 = injectiveMoment H raw5185step1 := by
      have hz : ∀ j, raw5185step0 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5185step1 = (fun i j => raw5185step0 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5185step0 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical281
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9013 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9013 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9013 = injectiveMoment H raw9013step0 := by
      have hz : ∀ j, raw9013 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9013step0 = (fun i j => raw9013 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9013 permutation9 hz
    injectiveMoment H raw9013step0 = injectiveMoment H raw9013step1 := by
      have heq : raw9013step1 = (fun i j => raw9013step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9013step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound3
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound203 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node203 = Sparse.eval value203 (momentVector H) := by
  have heq : pivotMatrix203 = (fun u v => node203 (pivotPermutation203 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node203 = injectiveMoment H pivotMatrix203 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix203 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix203 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix203 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (0 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix203 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (1 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix203 (2 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (2 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node203 + (injectiveMoment H (mergeFirst pivotMatrix203 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix203 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix203 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value203, value36, value41, value62, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

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

theorem singlePair496 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node496 node496Labels = Sparse.eval singlePairValue496 (familyPairVector B) := by
  have hp := single_label_three B hB node496
  have hl : node496Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node496 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node496 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node496 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node496 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node496 (EqualityPatterns.family3.label 1) = PairSemantics.raw5185 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node496 PairSemantics.raw5185; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5185 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node496 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node496 (EqualityPatterns.family3.label 2) = PairSemantics.raw9013 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node496 PairSemantics.raw9013; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9013 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node496 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node496 (EqualityPatterns.family3.label 3) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node496 PairSemantics.raw5141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node496 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value203 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node496 (EqualityPatterns.family3.label 4) = PairSemantics.raw3963 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node496 PairSemantics.raw3963; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3963 hH).trans (PairSemantics.sound203 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue496, PairSemantics.value0, PairSemantics.value4, PairSemantics.value11, PairSemantics.value46, PairSemantics.value203, Sparse.eval] at hp ⊢
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

theorem singleton3862 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3862 node3862Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node496 node496Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw536 singletonSmall3862
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3862) = raw536Labels := by decide +kernel
  rw [hl, canonical536 B hB] at h
  have hc0 : mixedMoment B raw536 (Fin.cases (0 : Fin 1) singletonSmall3862) =
      mixedMoment B node496 node496Labels := by
    have ha : raw536 = raw537 := by apply Matrix.ext; unfold raw536 raw537; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3862 = raw537Labels := by decide +kernel
    rw [ha, hj, canonical537 B hB]
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

theorem sound496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node496 node496Labels = Sparse.eval nodeValue496 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue496 (familyPairVector B) := singlePair496 B _hB
    _ = _ := by norm_num [singlePairValue496, nodeValue496, Sparse.eval, mixedVector] <;> ring

theorem sound3054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3054 node3054Labels = Sparse.eval nodeValue3054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3054) = mixedMoment B node3054 node3054Labels := rfl
  simpa [nodeValue3054, Sparse.eval] using hc.symm

theorem sound3626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3626 node3626Labels = Sparse.eval nodeValue3626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3626) = mixedMoment B node3626 node3626Labels := rfl
  simpa [nodeValue3626, Sparse.eval] using hc.symm

theorem sound3862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3862 node3862Labels = Sparse.eval nodeValue3862 (mixedVector B) := by
  have h := singleton3862 B _hB
  rw [sound496 B _hB _hF] at h
  norm_num [nodeValue3862, nodeValue496, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3907 node3907Labels = Sparse.eval nodeValue3907 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3907) = mixedMoment B node3907 node3907Labels := rfl
  simpa [nodeValue3907, Sparse.eval] using hc.symm

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

theorem sound1014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1014 node1014Labels = Sparse.eval nodeValue1014 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1014) = mixedMoment B node1014 node1014Labels := rfl
  simpa [nodeValue1014, Sparse.eval] using hc.symm

theorem sound1016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1016 node1016Labels = Sparse.eval nodeValue1016 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1016) = mixedMoment B node1016 node1016Labels := rfl
  simpa [nodeValue1016, Sparse.eval] using hc.symm

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

theorem sound1024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1024 node1024Labels = Sparse.eval nodeValue1024 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1024) = mixedMoment B node1024 node1024Labels := rfl
  simpa [nodeValue1024, Sparse.eval] using hc.symm

theorem sound1068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1068 node1068Labels = Sparse.eval nodeValue1068 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1068) = mixedMoment B node1068 node1068Labels := rfl
  simpa [nodeValue1068, Sparse.eval] using hc.symm

theorem sound1078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1078 node1078Labels = Sparse.eval nodeValue1078 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1078) = mixedMoment B node1078 node1078Labels := rfl
  simpa [nodeValue1078, Sparse.eval] using hc.symm

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

theorem sound1224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1224 node1224Labels = Sparse.eval nodeValue1224 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1224) = mixedMoment B node1224 node1224Labels := rfl
  simpa [nodeValue1224, Sparse.eval] using hc.symm

theorem sound1227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1227 node1227Labels = Sparse.eval nodeValue1227 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1227) = mixedMoment B node1227 node1227Labels := rfl
  simpa [nodeValue1227, Sparse.eval] using hc.symm

theorem sound1243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1243 node1243Labels = Sparse.eval nodeValue1243 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1243) = mixedMoment B node1243 node1243Labels := rfl
  simpa [nodeValue1243, Sparse.eval] using hc.symm

theorem sound1279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1279 node1279Labels = Sparse.eval nodeValue1279 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1279) = mixedMoment B node1279 node1279Labels := rfl
  simpa [nodeValue1279, Sparse.eval] using hc.symm

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

theorem sound1372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1372 node1372Labels = Sparse.eval nodeValue1372 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1372) = mixedMoment B node1372 node1372Labels := rfl
  simpa [nodeValue1372, Sparse.eval] using hc.symm

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

theorem sound1457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1457 node1457Labels = Sparse.eval nodeValue1457 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1457) = mixedMoment B node1457 node1457Labels := rfl
  simpa [nodeValue1457, Sparse.eval] using hc.symm

theorem sound1460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1460 node1460Labels = Sparse.eval nodeValue1460 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1460) = mixedMoment B node1460 node1460Labels := rfl
  simpa [nodeValue1460, Sparse.eval] using hc.symm

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

theorem sound1624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1624 node1624Labels = Sparse.eval nodeValue1624 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1624) = mixedMoment B node1624 node1624Labels := rfl
  simpa [nodeValue1624, Sparse.eval] using hc.symm

theorem sound1628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1628 node1628Labels = Sparse.eval nodeValue1628 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1628) = mixedMoment B node1628 node1628Labels := rfl
  simpa [nodeValue1628, Sparse.eval] using hc.symm

theorem sound1629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1629 node1629Labels = Sparse.eval nodeValue1629 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1629) = mixedMoment B node1629 node1629Labels := rfl
  simpa [nodeValue1629, Sparse.eval] using hc.symm

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

theorem sound1729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1729 node1729Labels = Sparse.eval nodeValue1729 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1729) = mixedMoment B node1729 node1729Labels := rfl
  simpa [nodeValue1729, Sparse.eval] using hc.symm

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

theorem sound2010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2010 node2010Labels = Sparse.eval nodeValue2010 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2010) = mixedMoment B node2010 node2010Labels := rfl
  simpa [nodeValue2010, Sparse.eval] using hc.symm

theorem sound2040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2040 node2040Labels = Sparse.eval nodeValue2040 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2040) = mixedMoment B node2040 node2040Labels := rfl
  simpa [nodeValue2040, Sparse.eval] using hc.symm

theorem sound2041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2041 node2041Labels = Sparse.eval nodeValue2041 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2041) = mixedMoment B node2041 node2041Labels := rfl
  simpa [nodeValue2041, Sparse.eval] using hc.symm

theorem sound2042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2042 node2042Labels = Sparse.eval nodeValue2042 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2042) = mixedMoment B node2042 node2042Labels := rfl
  simpa [nodeValue2042, Sparse.eval] using hc.symm

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

theorem sound2050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2050 node2050Labels = Sparse.eval nodeValue2050 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2050) = mixedMoment B node2050 node2050Labels := rfl
  simpa [nodeValue2050, Sparse.eval] using hc.symm

theorem sound2055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2055 node2055Labels = Sparse.eval nodeValue2055 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2055) = mixedMoment B node2055 node2055Labels := rfl
  simpa [nodeValue2055, Sparse.eval] using hc.symm

theorem sound2083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2083 node2083Labels = Sparse.eval nodeValue2083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2083) = mixedMoment B node2083 node2083Labels := rfl
  simpa [nodeValue2083, Sparse.eval] using hc.symm

theorem sound2092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2092 node2092Labels = Sparse.eval nodeValue2092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2092) = mixedMoment B node2092 node2092Labels := rfl
  simpa [nodeValue2092, Sparse.eval] using hc.symm

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

theorem sound2233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2233 node2233Labels = Sparse.eval nodeValue2233 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2233) = mixedMoment B node2233 node2233Labels := rfl
  simpa [nodeValue2233, Sparse.eval] using hc.symm

theorem sound2235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2235 node2235Labels = Sparse.eval nodeValue2235 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2235) = mixedMoment B node2235 node2235Labels := rfl
  simpa [nodeValue2235, Sparse.eval] using hc.symm

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

theorem sound2245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2245 node2245Labels = Sparse.eval nodeValue2245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2245) = mixedMoment B node2245 node2245Labels := rfl
  simpa [nodeValue2245, Sparse.eval] using hc.symm

theorem sound2283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2283 node2283Labels = Sparse.eval nodeValue2283 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2283) = mixedMoment B node2283 node2283Labels := rfl
  simpa [nodeValue2283, Sparse.eval] using hc.symm

theorem sound2284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2284 node2284Labels = Sparse.eval nodeValue2284 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2284) = mixedMoment B node2284 node2284Labels := rfl
  simpa [nodeValue2284, Sparse.eval] using hc.symm

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

theorem sound2495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2495 node2495Labels = Sparse.eval nodeValue2495 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2495) = mixedMoment B node2495 node2495Labels := rfl
  simpa [nodeValue2495, Sparse.eval] using hc.symm

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

theorem sound2519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2519 node2519Labels = Sparse.eval nodeValue2519 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2519) = mixedMoment B node2519 node2519Labels := rfl
  simpa [nodeValue2519, Sparse.eval] using hc.symm

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

theorem sound2579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2579 node2579Labels = Sparse.eval nodeValue2579 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2579) = mixedMoment B node2579 node2579Labels := rfl
  simpa [nodeValue2579, Sparse.eval] using hc.symm

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

theorem sound2651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2651 node2651Labels = Sparse.eval nodeValue2651 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2651) = mixedMoment B node2651 node2651Labels := rfl
  simpa [nodeValue2651, Sparse.eval] using hc.symm

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

theorem sound2734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2734 node2734Labels = Sparse.eval nodeValue2734 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2734) = mixedMoment B node2734 node2734Labels := rfl
  simpa [nodeValue2734, Sparse.eval] using hc.symm

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

theorem sound2774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2774 node2774Labels = Sparse.eval nodeValue2774 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2774) = mixedMoment B node2774 node2774Labels := rfl
  simpa [nodeValue2774, Sparse.eval] using hc.symm

theorem sound2777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2777 node2777Labels = Sparse.eval nodeValue2777 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2777) = mixedMoment B node2777 node2777Labels := rfl
  simpa [nodeValue2777, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2837 node2837Labels = Sparse.eval nodeValue2837 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2837) = mixedMoment B node2837 node2837Labels := rfl
  simpa [nodeValue2837, Sparse.eval] using hc.symm

theorem sound2842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2842 node2842Labels = Sparse.eval nodeValue2842 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2842) = mixedMoment B node2842 node2842Labels := rfl
  simpa [nodeValue2842, Sparse.eval] using hc.symm

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

theorem sound3038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3038 node3038Labels = Sparse.eval nodeValue3038 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3038) = mixedMoment B node3038 node3038Labels := rfl
  simpa [nodeValue3038, Sparse.eval] using hc.symm

theorem sound3052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3052 node3052Labels = Sparse.eval nodeValue3052 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3052) = mixedMoment B node3052 node3052Labels := rfl
  simpa [nodeValue3052, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3155 node3155Labels = Sparse.eval nodeValue3155 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3155) = mixedMoment B node3155 node3155Labels := rfl
  simpa [nodeValue3155, Sparse.eval] using hc.symm

theorem sound3158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3158 node3158Labels = Sparse.eval nodeValue3158 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3158) = mixedMoment B node3158 node3158Labels := rfl
  simpa [nodeValue3158, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3242 node3242Labels = Sparse.eval nodeValue3242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3242) = mixedMoment B node3242 node3242Labels := rfl
  simpa [nodeValue3242, Sparse.eval] using hc.symm

theorem sound3247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3247 node3247Labels = Sparse.eval nodeValue3247 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3247) = mixedMoment B node3247 node3247Labels := rfl
  simpa [nodeValue3247, Sparse.eval] using hc.symm

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

theorem sound3302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3302 node3302Labels = Sparse.eval nodeValue3302 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3302) = mixedMoment B node3302 node3302Labels := rfl
  simpa [nodeValue3302, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3358 node3358Labels = Sparse.eval nodeValue3358 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3358) = mixedMoment B node3358 node3358Labels := rfl
  simpa [nodeValue3358, Sparse.eval] using hc.symm

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

theorem sound3437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3437 node3437Labels = Sparse.eval nodeValue3437 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3437) = mixedMoment B node3437 node3437Labels := rfl
  simpa [nodeValue3437, Sparse.eval] using hc.symm

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

theorem sound3472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3472 node3472Labels = Sparse.eval nodeValue3472 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3472) = mixedMoment B node3472 node3472Labels := rfl
  simpa [nodeValue3472, Sparse.eval] using hc.symm

theorem sound3486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3486 node3486Labels = Sparse.eval nodeValue3486 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3486) = mixedMoment B node3486 node3486Labels := rfl
  simpa [nodeValue3486, Sparse.eval] using hc.symm

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

theorem sound3523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3523 node3523Labels = Sparse.eval nodeValue3523 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3523) = mixedMoment B node3523 node3523Labels := rfl
  simpa [nodeValue3523, Sparse.eval] using hc.symm

theorem sound3535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3535 node3535Labels = Sparse.eval nodeValue3535 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3535) = mixedMoment B node3535 node3535Labels := rfl
  simpa [nodeValue3535, Sparse.eval] using hc.symm

theorem sound3541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3541 node3541Labels = Sparse.eval nodeValue3541 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3541) = mixedMoment B node3541 node3541Labels := rfl
  simpa [nodeValue3541, Sparse.eval] using hc.symm

theorem sound3548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3548 node3548Labels = Sparse.eval nodeValue3548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3548) = mixedMoment B node3548 node3548Labels := rfl
  simpa [nodeValue3548, Sparse.eval] using hc.symm

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

theorem sound3584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3584 node3584Labels = Sparse.eval nodeValue3584 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3584) = mixedMoment B node3584 node3584Labels := rfl
  simpa [nodeValue3584, Sparse.eval] using hc.symm

theorem sound3619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3619 node3619Labels = Sparse.eval nodeValue3619 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3619) = mixedMoment B node3619 node3619Labels := rfl
  simpa [nodeValue3619, Sparse.eval] using hc.symm

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

theorem sound4085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4085 node4085Labels = Sparse.eval nodeValue4085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4085) = mixedMoment B node4085 node4085Labels := rfl
  simpa [nodeValue4085, Sparse.eval] using hc.symm

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources1
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq54 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm54 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA54 + difference 0 1) (sourceB54 + difference 1 0) sourceC54) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2055) := by
    have ha : (tripleCharges (sourceA54 + difference 0 1) (sourceB54 + difference 1 0) sourceC54) = raw3716 := by
      apply Matrix.ext; unfold tripleCharges sourceA54 sourceB54 sourceC54 difference raw3716; decide +kernel
    rw [ha]
    exact (canonical3716 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA54 + difference 1 1) (sourceB54 + difference 1 1) sourceC54) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2284) := by
    have ha : (tripleCharges (sourceA54 + difference 1 1) (sourceB54 + difference 1 1) sourceC54) = raw3715 := by
      apply Matrix.ext; unfold tripleCharges sourceA54 sourceB54 sourceC54 difference raw3715; decide +kernel
    rw [ha]
    exact (canonical3715 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA54 + difference 2 1) (sourceB54 + difference 1 2) sourceC54) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2040) := by
    have ha : (tripleCharges (sourceA54 + difference 2 1) (sourceB54 + difference 1 2) sourceC54) = raw3731 := by
      apply Matrix.ext; unfold tripleCharges sourceA54 sourceB54 sourceC54 difference raw3731; decide +kernel
    rw [ha]
    exact (canonical3731 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA54 + difference 3 1) (sourceB54 + difference 1 3) sourceC54) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2042) := by
    have ha : (tripleCharges (sourceA54 + difference 3 1) (sourceB54 + difference 1 3) sourceC54) = raw3732 := by
      apply Matrix.ext; unfold tripleCharges sourceA54 sourceB54 sourceC54 difference raw3732; decide +kernel
    rw [ha]
    exact (canonical3732 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA54 + difference 4 1) (sourceB54 + difference 1 4) sourceC54) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2041) := by
    have ha : (tripleCharges (sourceA54 + difference 4 1) (sourceB54 + difference 1 4) sourceC54) = raw3733 := by
      apply Matrix.ext; unfold tripleCharges sourceA54 sourceB54 sourceC54 difference raw3733; decide +kernel
    rw [ha]
    exact (canonical3733 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA54 + difference 5 1) (sourceB54 + difference 1 5) sourceC54) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2055) := by
    have ha : (tripleCharges (sourceA54 + difference 5 1) (sourceB54 + difference 1 5) sourceC54) = raw3734 := by
      apply Matrix.ext; unfold tripleCharges sourceA54 sourceB54 sourceC54 difference raw3734; decide +kernel
    rw [ha]
    exact (canonical3734 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA54 + sourceB54) sourceC54) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA54 + sourceB54) sourceC54) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA54 sourceB54 sourceC54 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA54 sourceB54 sourceC54
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm54, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq55 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm55 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA55 + difference 3 0) (sourceB55 + difference 0 3) sourceC55) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1068) := by
    have ha : (tripleCharges (sourceA55 + difference 3 0) (sourceB55 + difference 0 3) sourceC55) = raw3724 := by
      apply Matrix.ext; unfold tripleCharges sourceA55 sourceB55 sourceC55 difference raw3724; decide +kernel
    rw [ha]
    exact (canonical3724 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA55 + difference 3 1) (sourceB55 + difference 1 3) sourceC55) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2042) := by
    have ha : (tripleCharges (sourceA55 + difference 3 1) (sourceB55 + difference 1 3) sourceC55) = raw3732 := by
      apply Matrix.ext; unfold tripleCharges sourceA55 sourceB55 sourceC55 difference raw3732; decide +kernel
    rw [ha]
    exact (canonical3732 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA55 + difference 3 2) (sourceB55 + difference 2 3) sourceC55) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2042) := by
    have ha : (tripleCharges (sourceA55 + difference 3 2) (sourceB55 + difference 2 3) sourceC55) = raw3735 := by
      apply Matrix.ext; unfold tripleCharges sourceA55 sourceB55 sourceC55 difference raw3735; decide +kernel
    rw [ha]
    exact (canonical3735 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA55 + difference 3 3) (sourceB55 + difference 3 3) sourceC55) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2284) := by
    have ha : (tripleCharges (sourceA55 + difference 3 3) (sourceB55 + difference 3 3) sourceC55) = raw3715 := by
      apply Matrix.ext; unfold tripleCharges sourceA55 sourceB55 sourceC55 difference raw3715; decide +kernel
    rw [ha]
    exact (canonical3715 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA55 + difference 3 4) (sourceB55 + difference 4 3) sourceC55) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2284) := by
    have ha : (tripleCharges (sourceA55 + difference 3 4) (sourceB55 + difference 4 3) sourceC55) = raw3736 := by
      apply Matrix.ext; unfold tripleCharges sourceA55 sourceB55 sourceC55 difference raw3736; decide +kernel
    rw [ha]
    exact (canonical3736 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA55 + difference 3 5) (sourceB55 + difference 5 3) sourceC55) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1068) := by
    have ha : (tripleCharges (sourceA55 + difference 3 5) (sourceB55 + difference 5 3) sourceC55) = raw3737 := by
      apply Matrix.ext; unfold tripleCharges sourceA55 sourceB55 sourceC55 difference raw3737; decide +kernel
    rw [ha]
    exact (canonical3737 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA55 + sourceB55) sourceC55) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA55 + sourceB55) sourceC55) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA55 sourceB55 sourceC55 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA55 sourceB55 sourceC55
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm55, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq59 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm59 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA59 + difference 0 0) (sourceB59 + difference 0 0) sourceC59) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA59 + difference 0 0) (sourceB59 + difference 0 0) sourceC59) = raw3828 := by
      apply Matrix.ext; unfold tripleCharges sourceA59 sourceB59 sourceC59 difference raw3828; decide +kernel
    rw [ha]
    exact (canonical3828 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA59 + difference 0 1) (sourceB59 + difference 1 0) sourceC59) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3155) := by
    have ha : (tripleCharges (sourceA59 + difference 0 1) (sourceB59 + difference 1 0) sourceC59) = raw3829 := by
      apply Matrix.ext; unfold tripleCharges sourceA59 sourceB59 sourceC59 difference raw3829; decide +kernel
    rw [ha]
    exact (canonical3829 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA59 + difference 0 2) (sourceB59 + difference 2 0) sourceC59) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3158) := by
    have ha : (tripleCharges (sourceA59 + difference 0 2) (sourceB59 + difference 2 0) sourceC59) = raw3830 := by
      apply Matrix.ext; unfold tripleCharges sourceA59 sourceB59 sourceC59 difference raw3830; decide +kernel
    rw [ha]
    exact (canonical3830 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA59 + difference 0 3) (sourceB59 + difference 3 0) sourceC59) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3158) := by
    have ha : (tripleCharges (sourceA59 + difference 0 3) (sourceB59 + difference 3 0) sourceC59) = raw3831 := by
      apply Matrix.ext; unfold tripleCharges sourceA59 sourceB59 sourceC59 difference raw3831; decide +kernel
    rw [ha]
    exact (canonical3831 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA59 + difference 0 4) (sourceB59 + difference 4 0) sourceC59) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3158) := by
    have ha : (tripleCharges (sourceA59 + difference 0 4) (sourceB59 + difference 4 0) sourceC59) = raw3832 := by
      apply Matrix.ext; unfold tripleCharges sourceA59 sourceB59 sourceC59 difference raw3832; decide +kernel
    rw [ha]
    exact (canonical3832 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA59 + difference 0 5) (sourceB59 + difference 5 0) sourceC59) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3619) := by
    have ha : (tripleCharges (sourceA59 + difference 0 5) (sourceB59 + difference 5 0) sourceC59) = raw3833 := by
      apply Matrix.ext; unfold tripleCharges sourceA59 sourceB59 sourceC59 difference raw3833; decide +kernel
    rw [ha]
    exact (canonical3833 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA59 + sourceB59) sourceC59) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA59 + sourceB59) sourceC59) = raw3834 := by
      apply Matrix.ext; unfold doubleCharges sourceA59 sourceB59 sourceC59 raw3834; decide +kernel
    rw [ha]
    exact (canonical3834 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA59 sourceB59 sourceC59
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm59, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq60 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm60 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA60 + difference 0 0) (sourceB60 + difference 0 0) sourceC60) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA60 + difference 0 0) (sourceB60 + difference 0 0) sourceC60) = raw3828 := by
      apply Matrix.ext; unfold tripleCharges sourceA60 sourceB60 sourceC60 difference raw3828; decide +kernel
    rw [ha]
    exact (canonical3828 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA60 + difference 1 0) (sourceB60 + difference 0 1) sourceC60) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1014) := by
    have ha : (tripleCharges (sourceA60 + difference 1 0) (sourceB60 + difference 0 1) sourceC60) = raw3835 := by
      apply Matrix.ext; unfold tripleCharges sourceA60 sourceB60 sourceC60 difference raw3835; decide +kernel
    rw [ha]
    exact (canonical3835 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA60 + difference 2 0) (sourceB60 + difference 0 2) sourceC60) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1024) := by
    have ha : (tripleCharges (sourceA60 + difference 2 0) (sourceB60 + difference 0 2) sourceC60) = raw3836 := by
      apply Matrix.ext; unfold tripleCharges sourceA60 sourceB60 sourceC60 difference raw3836; decide +kernel
    rw [ha]
    exact (canonical3836 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA60 + difference 3 0) (sourceB60 + difference 0 3) sourceC60) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1024) := by
    have ha : (tripleCharges (sourceA60 + difference 3 0) (sourceB60 + difference 0 3) sourceC60) = raw3837 := by
      apply Matrix.ext; unfold tripleCharges sourceA60 sourceB60 sourceC60 difference raw3837; decide +kernel
    rw [ha]
    exact (canonical3837 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA60 + difference 4 0) (sourceB60 + difference 0 4) sourceC60) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1024) := by
    have ha : (tripleCharges (sourceA60 + difference 4 0) (sourceB60 + difference 0 4) sourceC60) = raw3838 := by
      apply Matrix.ext; unfold tripleCharges sourceA60 sourceB60 sourceC60 difference raw3838; decide +kernel
    rw [ha]
    exact (canonical3838 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA60 + difference 5 0) (sourceB60 + difference 0 5) sourceC60) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1016) := by
    have ha : (tripleCharges (sourceA60 + difference 5 0) (sourceB60 + difference 0 5) sourceC60) = raw3839 := by
      apply Matrix.ext; unfold tripleCharges sourceA60 sourceB60 sourceC60 difference raw3839; decide +kernel
    rw [ha]
    exact (canonical3839 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA60 + sourceB60) sourceC60) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA60 + sourceB60) sourceC60) = raw3834 := by
      apply Matrix.ext; unfold doubleCharges sourceA60 sourceB60 sourceC60 raw3834; decide +kernel
    rw [ha]
    exact (canonical3834 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA60 sourceB60 sourceC60
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm60, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq61 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm61 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA61 + difference 1 0) (sourceB61 + difference 0 1) sourceC61) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1014) := by
    have ha : (tripleCharges (sourceA61 + difference 1 0) (sourceB61 + difference 0 1) sourceC61) = raw3835 := by
      apply Matrix.ext; unfold tripleCharges sourceA61 sourceB61 sourceC61 difference raw3835; decide +kernel
    rw [ha]
    exact (canonical3835 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA61 + difference 1 1) (sourceB61 + difference 1 1) sourceC61) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA61 + difference 1 1) (sourceB61 + difference 1 1) sourceC61) = raw3828 := by
      apply Matrix.ext; unfold tripleCharges sourceA61 sourceB61 sourceC61 difference raw3828; decide +kernel
    rw [ha]
    exact (canonical3828 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA61 + difference 1 2) (sourceB61 + difference 2 1) sourceC61) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2083) := by
    have ha : (tripleCharges (sourceA61 + difference 1 2) (sourceB61 + difference 2 1) sourceC61) = raw3840 := by
      apply Matrix.ext; unfold tripleCharges sourceA61 sourceB61 sourceC61 difference raw3840; decide +kernel
    rw [ha]
    exact (canonical3840 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA61 + difference 1 3) (sourceB61 + difference 3 1) sourceC61) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2083) := by
    have ha : (tripleCharges (sourceA61 + difference 1 3) (sourceB61 + difference 3 1) sourceC61) = raw3841 := by
      apply Matrix.ext; unfold tripleCharges sourceA61 sourceB61 sourceC61 difference raw3841; decide +kernel
    rw [ha]
    exact (canonical3841 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA61 + difference 1 4) (sourceB61 + difference 4 1) sourceC61) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2083) := by
    have ha : (tripleCharges (sourceA61 + difference 1 4) (sourceB61 + difference 4 1) sourceC61) = raw3842 := by
      apply Matrix.ext; unfold tripleCharges sourceA61 sourceB61 sourceC61 difference raw3842; decide +kernel
    rw [ha]
    exact (canonical3842 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA61 + difference 1 5) (sourceB61 + difference 5 1) sourceC61) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2233) := by
    have ha : (tripleCharges (sourceA61 + difference 1 5) (sourceB61 + difference 5 1) sourceC61) = raw3843 := by
      apply Matrix.ext; unfold tripleCharges sourceA61 sourceB61 sourceC61 difference raw3843; decide +kernel
    rw [ha]
    exact (canonical3843 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA61 + sourceB61) sourceC61) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA61 + sourceB61) sourceC61) = raw3834 := by
      apply Matrix.ext; unfold doubleCharges sourceA61 sourceB61 sourceC61 raw3834; decide +kernel
    rw [ha]
    exact (canonical3834 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA61 sourceB61 sourceC61
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm61, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq62 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm62 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA62 + difference 0 1) (sourceB62 + difference 1 0) sourceC62) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3155) := by
    have ha : (tripleCharges (sourceA62 + difference 0 1) (sourceB62 + difference 1 0) sourceC62) = raw3829 := by
      apply Matrix.ext; unfold tripleCharges sourceA62 sourceB62 sourceC62 difference raw3829; decide +kernel
    rw [ha]
    exact (canonical3829 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA62 + difference 1 1) (sourceB62 + difference 1 1) sourceC62) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA62 + difference 1 1) (sourceB62 + difference 1 1) sourceC62) = raw3828 := by
      apply Matrix.ext; unfold tripleCharges sourceA62 sourceB62 sourceC62 difference raw3828; decide +kernel
    rw [ha]
    exact (canonical3828 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA62 + difference 2 1) (sourceB62 + difference 1 2) sourceC62) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2010) := by
    have ha : (tripleCharges (sourceA62 + difference 2 1) (sourceB62 + difference 1 2) sourceC62) = raw3844 := by
      apply Matrix.ext; unfold tripleCharges sourceA62 sourceB62 sourceC62 difference raw3844; decide +kernel
    rw [ha]
    exact (canonical3844 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA62 + difference 3 1) (sourceB62 + difference 1 3) sourceC62) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2010) := by
    have ha : (tripleCharges (sourceA62 + difference 3 1) (sourceB62 + difference 1 3) sourceC62) = raw3845 := by
      apply Matrix.ext; unfold tripleCharges sourceA62 sourceB62 sourceC62 difference raw3845; decide +kernel
    rw [ha]
    exact (canonical3845 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA62 + difference 4 1) (sourceB62 + difference 1 4) sourceC62) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2010) := by
    have ha : (tripleCharges (sourceA62 + difference 4 1) (sourceB62 + difference 1 4) sourceC62) = raw3846 := by
      apply Matrix.ext; unfold tripleCharges sourceA62 sourceB62 sourceC62 difference raw3846; decide +kernel
    rw [ha]
    exact (canonical3846 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA62 + difference 5 1) (sourceB62 + difference 1 5) sourceC62) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1457) := by
    have ha : (tripleCharges (sourceA62 + difference 5 1) (sourceB62 + difference 1 5) sourceC62) = raw3847 := by
      apply Matrix.ext; unfold tripleCharges sourceA62 sourceB62 sourceC62 difference raw3847; decide +kernel
    rw [ha]
    exact (canonical3847 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA62 + sourceB62) sourceC62) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA62 + sourceB62) sourceC62) = raw3834 := by
      apply Matrix.ext; unfold doubleCharges sourceA62 sourceB62 sourceC62 raw3834; decide +kernel
    rw [ha]
    exact (canonical3834 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA62 sourceB62 sourceC62
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm62, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq63 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm63 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA63 + difference 2 0) (sourceB63 + difference 0 2) sourceC63) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1024) := by
    have ha : (tripleCharges (sourceA63 + difference 2 0) (sourceB63 + difference 0 2) sourceC63) = raw3836 := by
      apply Matrix.ext; unfold tripleCharges sourceA63 sourceB63 sourceC63 difference raw3836; decide +kernel
    rw [ha]
    exact (canonical3836 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA63 + difference 2 1) (sourceB63 + difference 1 2) sourceC63) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2010) := by
    have ha : (tripleCharges (sourceA63 + difference 2 1) (sourceB63 + difference 1 2) sourceC63) = raw3844 := by
      apply Matrix.ext; unfold tripleCharges sourceA63 sourceB63 sourceC63 difference raw3844; decide +kernel
    rw [ha]
    exact (canonical3844 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA63 + difference 2 2) (sourceB63 + difference 2 2) sourceC63) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA63 + difference 2 2) (sourceB63 + difference 2 2) sourceC63) = raw3828 := by
      apply Matrix.ext; unfold tripleCharges sourceA63 sourceB63 sourceC63 difference raw3828; decide +kernel
    rw [ha]
    exact (canonical3828 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA63 + difference 2 3) (sourceB63 + difference 3 2) sourceC63) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA63 + difference 2 3) (sourceB63 + difference 3 2) sourceC63) = raw3848 := by
      apply Matrix.ext; unfold tripleCharges sourceA63 sourceB63 sourceC63 difference raw3848; decide +kernel
    rw [ha]
    exact (canonical3848 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA63 + difference 2 4) (sourceB63 + difference 4 2) sourceC63) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA63 + difference 2 4) (sourceB63 + difference 4 2) sourceC63) = raw3849 := by
      apply Matrix.ext; unfold tripleCharges sourceA63 sourceB63 sourceC63 difference raw3849; decide +kernel
    rw [ha]
    exact (canonical3849 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA63 + difference 2 5) (sourceB63 + difference 5 2) sourceC63) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA63 + difference 2 5) (sourceB63 + difference 5 2) sourceC63) = raw3850 := by
      apply Matrix.ext; unfold tripleCharges sourceA63 sourceB63 sourceC63 difference raw3850; decide +kernel
    rw [ha]
    exact (canonical3850 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA63 + sourceB63) sourceC63) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA63 + sourceB63) sourceC63) = raw3834 := by
      apply Matrix.ext; unfold doubleCharges sourceA63 sourceB63 sourceC63 raw3834; decide +kernel
    rw [ha]
    exact (canonical3834 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA63 sourceB63 sourceC63
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm63, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources2
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq64 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm64 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA64 + difference 0 2) (sourceB64 + difference 2 0) sourceC64) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3158) := by
    have ha : (tripleCharges (sourceA64 + difference 0 2) (sourceB64 + difference 2 0) sourceC64) = raw3830 := by
      apply Matrix.ext; unfold tripleCharges sourceA64 sourceB64 sourceC64 difference raw3830; decide +kernel
    rw [ha]
    exact (canonical3830 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA64 + difference 1 2) (sourceB64 + difference 2 1) sourceC64) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2083) := by
    have ha : (tripleCharges (sourceA64 + difference 1 2) (sourceB64 + difference 2 1) sourceC64) = raw3840 := by
      apply Matrix.ext; unfold tripleCharges sourceA64 sourceB64 sourceC64 difference raw3840; decide +kernel
    rw [ha]
    exact (canonical3840 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA64 + difference 2 2) (sourceB64 + difference 2 2) sourceC64) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA64 + difference 2 2) (sourceB64 + difference 2 2) sourceC64) = raw3828 := by
      apply Matrix.ext; unfold tripleCharges sourceA64 sourceB64 sourceC64 difference raw3828; decide +kernel
    rw [ha]
    exact (canonical3828 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA64 + difference 3 2) (sourceB64 + difference 2 3) sourceC64) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA64 + difference 3 2) (sourceB64 + difference 2 3) sourceC64) = raw3851 := by
      apply Matrix.ext; unfold tripleCharges sourceA64 sourceB64 sourceC64 difference raw3851; decide +kernel
    rw [ha]
    exact (canonical3851 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA64 + difference 4 2) (sourceB64 + difference 2 4) sourceC64) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA64 + difference 4 2) (sourceB64 + difference 2 4) sourceC64) = raw3852 := by
      apply Matrix.ext; unfold tripleCharges sourceA64 sourceB64 sourceC64 difference raw3852; decide +kernel
    rw [ha]
    exact (canonical3852 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA64 + difference 5 2) (sourceB64 + difference 2 5) sourceC64) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1460) := by
    have ha : (tripleCharges (sourceA64 + difference 5 2) (sourceB64 + difference 2 5) sourceC64) = raw3853 := by
      apply Matrix.ext; unfold tripleCharges sourceA64 sourceB64 sourceC64 difference raw3853; decide +kernel
    rw [ha]
    exact (canonical3853 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA64 + sourceB64) sourceC64) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA64 + sourceB64) sourceC64) = raw3834 := by
      apply Matrix.ext; unfold doubleCharges sourceA64 sourceB64 sourceC64 raw3834; decide +kernel
    rw [ha]
    exact (canonical3834 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA64 sourceB64 sourceC64
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm64, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq65 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm65 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA65 + difference 5 0) (sourceB65 + difference 0 5) sourceC65) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1016) := by
    have ha : (tripleCharges (sourceA65 + difference 5 0) (sourceB65 + difference 0 5) sourceC65) = raw3839 := by
      apply Matrix.ext; unfold tripleCharges sourceA65 sourceB65 sourceC65 difference raw3839; decide +kernel
    rw [ha]
    exact (canonical3839 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA65 + difference 5 1) (sourceB65 + difference 1 5) sourceC65) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1457) := by
    have ha : (tripleCharges (sourceA65 + difference 5 1) (sourceB65 + difference 1 5) sourceC65) = raw3847 := by
      apply Matrix.ext; unfold tripleCharges sourceA65 sourceB65 sourceC65 difference raw3847; decide +kernel
    rw [ha]
    exact (canonical3847 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA65 + difference 5 2) (sourceB65 + difference 2 5) sourceC65) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1460) := by
    have ha : (tripleCharges (sourceA65 + difference 5 2) (sourceB65 + difference 2 5) sourceC65) = raw3853 := by
      apply Matrix.ext; unfold tripleCharges sourceA65 sourceB65 sourceC65 difference raw3853; decide +kernel
    rw [ha]
    exact (canonical3853 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA65 + difference 5 3) (sourceB65 + difference 3 5) sourceC65) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1460) := by
    have ha : (tripleCharges (sourceA65 + difference 5 3) (sourceB65 + difference 3 5) sourceC65) = raw3854 := by
      apply Matrix.ext; unfold tripleCharges sourceA65 sourceB65 sourceC65 difference raw3854; decide +kernel
    rw [ha]
    exact (canonical3854 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA65 + difference 5 4) (sourceB65 + difference 4 5) sourceC65) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1460) := by
    have ha : (tripleCharges (sourceA65 + difference 5 4) (sourceB65 + difference 4 5) sourceC65) = raw3855 := by
      apply Matrix.ext; unfold tripleCharges sourceA65 sourceB65 sourceC65 difference raw3855; decide +kernel
    rw [ha]
    exact (canonical3855 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA65 + difference 5 5) (sourceB65 + difference 5 5) sourceC65) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA65 + difference 5 5) (sourceB65 + difference 5 5) sourceC65) = raw3828 := by
      apply Matrix.ext; unfold tripleCharges sourceA65 sourceB65 sourceC65 difference raw3828; decide +kernel
    rw [ha]
    exact (canonical3828 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA65 + sourceB65) sourceC65) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA65 + sourceB65) sourceC65) = raw3834 := by
      apply Matrix.ext; unfold doubleCharges sourceA65 sourceB65 sourceC65 raw3834; decide +kernel
    rw [ha]
    exact (canonical3834 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA65 sourceB65 sourceC65
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm65, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq68 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm68 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA68 + difference 0 0) (sourceB68 + difference 0 0) sourceC68) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2283) := by
    have ha : (tripleCharges (sourceA68 + difference 0 0) (sourceB68 + difference 0 0) sourceC68) = raw3900 := by
      apply Matrix.ext; unfold tripleCharges sourceA68 sourceB68 sourceC68 difference raw3900; decide +kernel
    rw [ha]
    exact (canonical3900 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA68 + difference 0 1) (sourceB68 + difference 1 0) sourceC68) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2050) := by
    have ha : (tripleCharges (sourceA68 + difference 0 1) (sourceB68 + difference 1 0) sourceC68) = raw3901 := by
      apply Matrix.ext; unfold tripleCharges sourceA68 sourceB68 sourceC68 difference raw3901; decide +kernel
    rw [ha]
    exact (canonical3901 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA68 + difference 0 2) (sourceB68 + difference 2 0) sourceC68) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA68 + difference 0 2) (sourceB68 + difference 2 0) sourceC68) = raw3719 := by
      apply Matrix.ext; unfold tripleCharges sourceA68 sourceB68 sourceC68 difference raw3719; decide +kernel
    rw [ha]
    exact (canonical3719 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA68 + difference 0 3) (sourceB68 + difference 3 0) sourceC68) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA68 + difference 0 3) (sourceB68 + difference 3 0) sourceC68) = raw3902 := by
      apply Matrix.ext; unfold tripleCharges sourceA68 sourceB68 sourceC68 difference raw3902; decide +kernel
    rw [ha]
    exact (canonical3902 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA68 + difference 0 4) (sourceB68 + difference 4 0) sourceC68) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA68 + difference 0 4) (sourceB68 + difference 4 0) sourceC68) = raw3903 := by
      apply Matrix.ext; unfold tripleCharges sourceA68 sourceB68 sourceC68 difference raw3903; decide +kernel
    rw [ha]
    exact (canonical3903 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA68 + difference 0 5) (sourceB68 + difference 5 0) sourceC68) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1078) := by
    have ha : (tripleCharges (sourceA68 + difference 0 5) (sourceB68 + difference 5 0) sourceC68) = raw3904 := by
      apply Matrix.ext; unfold tripleCharges sourceA68 sourceB68 sourceC68 difference raw3904; decide +kernel
    rw [ha]
    exact (canonical3904 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA68 + sourceB68) sourceC68) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA68 + sourceB68) sourceC68) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA68 sourceB68 sourceC68 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA68 sourceB68 sourceC68
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm68, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq73 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm73 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA73 + difference 0 1) (sourceB73 + difference 1 0) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3626) := by
    have ha : (tripleCharges (sourceA73 + difference 0 1) (sourceB73 + difference 1 0) sourceC73) = raw3972 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3972; decide +kernel
    rw [ha]
    exact (canonical3972 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA73 + difference 0 2) (sourceB73 + difference 2 0) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA73 + difference 0 2) (sourceB73 + difference 2 0) sourceC73) = raw3973 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3973; decide +kernel
    rw [ha]
    exact (canonical3973 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA73 + difference 0 3) (sourceB73 + difference 3 0) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA73 + difference 0 3) (sourceB73 + difference 3 0) sourceC73) = raw3974 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3974; decide +kernel
    rw [ha]
    exact (canonical3974 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA73 + difference 0 4) (sourceB73 + difference 4 0) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA73 + difference 0 4) (sourceB73 + difference 4 0) sourceC73) = raw3975 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3975; decide +kernel
    rw [ha]
    exact (canonical3975 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA73 + difference 0 5) (sourceB73 + difference 5 0) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA73 + difference 0 5) (sourceB73 + difference 5 0) sourceC73) = raw3976 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3976; decide +kernel
    rw [ha]
    exact (canonical3976 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA73 + difference 1 0) (sourceB73 + difference 0 1) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3247) := by
    have ha : (tripleCharges (sourceA73 + difference 1 0) (sourceB73 + difference 0 1) sourceC73) = raw3977 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3977; decide +kernel
    rw [ha]
    exact (canonical3977 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA73 + difference 1 2) (sourceB73 + difference 2 1) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3358) := by
    have ha : (tripleCharges (sourceA73 + difference 1 2) (sourceB73 + difference 2 1) sourceC73) = raw3978 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3978; decide +kernel
    rw [ha]
    exact (canonical3978 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA73 + difference 1 3) (sourceB73 + difference 3 1) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3358) := by
    have ha : (tripleCharges (sourceA73 + difference 1 3) (sourceB73 + difference 3 1) sourceC73) = raw3979 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3979; decide +kernel
    rw [ha]
    exact (canonical3979 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA73 + difference 1 4) (sourceB73 + difference 4 1) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2842) := by
    have ha : (tripleCharges (sourceA73 + difference 1 4) (sourceB73 + difference 4 1) sourceC73) = raw3980 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3980; decide +kernel
    rw [ha]
    exact (canonical3980 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA73 + difference 1 5) (sourceB73 + difference 5 1) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA73 + difference 1 5) (sourceB73 + difference 5 1) sourceC73) = raw3981 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3981; decide +kernel
    rw [ha]
    exact (canonical3981 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA73 + difference 2 0) (sourceB73 + difference 0 2) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3242) := by
    have ha : (tripleCharges (sourceA73 + difference 2 0) (sourceB73 + difference 0 2) sourceC73) = raw3982 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3982; decide +kernel
    rw [ha]
    exact (canonical3982 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA73 + difference 2 1) (sourceB73 + difference 1 2) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3472) := by
    have ha : (tripleCharges (sourceA73 + difference 2 1) (sourceB73 + difference 1 2) sourceC73) = raw3983 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3983; decide +kernel
    rw [ha]
    exact (canonical3983 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA73 + difference 2 3) (sourceB73 + difference 3 2) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3437) := by
    have ha : (tripleCharges (sourceA73 + difference 2 3) (sourceB73 + difference 3 2) sourceC73) = raw3984 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3984; decide +kernel
    rw [ha]
    exact (canonical3984 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA73 + difference 2 4) (sourceB73 + difference 4 2) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2837) := by
    have ha : (tripleCharges (sourceA73 + difference 2 4) (sourceB73 + difference 4 2) sourceC73) = raw3985 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3985; decide +kernel
    rw [ha]
    exact (canonical3985 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA73 + difference 2 5) (sourceB73 + difference 5 2) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA73 + difference 2 5) (sourceB73 + difference 5 2) sourceC73) = raw3986 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3986; decide +kernel
    rw [ha]
    exact (canonical3986 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA73 + difference 3 0) (sourceB73 + difference 0 3) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3242) := by
    have ha : (tripleCharges (sourceA73 + difference 3 0) (sourceB73 + difference 0 3) sourceC73) = raw3987 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3987; decide +kernel
    rw [ha]
    exact (canonical3987 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA73 + difference 3 1) (sourceB73 + difference 1 3) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3472) := by
    have ha : (tripleCharges (sourceA73 + difference 3 1) (sourceB73 + difference 1 3) sourceC73) = raw3988 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3988; decide +kernel
    rw [ha]
    exact (canonical3988 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA73 + difference 3 2) (sourceB73 + difference 2 3) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3437) := by
    have ha : (tripleCharges (sourceA73 + difference 3 2) (sourceB73 + difference 2 3) sourceC73) = raw3989 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3989; decide +kernel
    rw [ha]
    exact (canonical3989 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA73 + difference 3 4) (sourceB73 + difference 4 3) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2837) := by
    have ha : (tripleCharges (sourceA73 + difference 3 4) (sourceB73 + difference 4 3) sourceC73) = raw3990 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3990; decide +kernel
    rw [ha]
    exact (canonical3990 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA73 + difference 3 5) (sourceB73 + difference 5 3) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA73 + difference 3 5) (sourceB73 + difference 5 3) sourceC73) = raw3991 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3991; decide +kernel
    rw [ha]
    exact (canonical3991 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA73 + difference 4 0) (sourceB73 + difference 0 4) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA73 + difference 4 0) (sourceB73 + difference 0 4) sourceC73) = raw3992 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3992; decide +kernel
    rw [ha]
    exact (canonical3992 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA73 + difference 4 1) (sourceB73 + difference 1 4) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3486) := by
    have ha : (tripleCharges (sourceA73 + difference 4 1) (sourceB73 + difference 1 4) sourceC73) = raw3993 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3993; decide +kernel
    rw [ha]
    exact (canonical3993 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA73 + difference 4 2) (sourceB73 + difference 2 4) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA73 + difference 4 2) (sourceB73 + difference 2 4) sourceC73) = raw3994 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3994; decide +kernel
    rw [ha]
    exact (canonical3994 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA73 + difference 4 3) (sourceB73 + difference 3 4) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA73 + difference 4 3) (sourceB73 + difference 3 4) sourceC73) = raw3995 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3995; decide +kernel
    rw [ha]
    exact (canonical3995 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA73 + difference 4 5) (sourceB73 + difference 5 4) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA73 + difference 4 5) (sourceB73 + difference 5 4) sourceC73) = raw3996 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3996; decide +kernel
    rw [ha]
    exact (canonical3996 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA73 + difference 5 0) (sourceB73 + difference 0 5) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1629) := by
    have ha : (tripleCharges (sourceA73 + difference 5 0) (sourceB73 + difference 0 5) sourceC73) = raw3997 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3997; decide +kernel
    rw [ha]
    exact (canonical3997 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA73 + difference 5 1) (sourceB73 + difference 1 5) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA73 + difference 5 1) (sourceB73 + difference 1 5) sourceC73) = raw3998 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3998; decide +kernel
    rw [ha]
    exact (canonical3998 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA73 + difference 5 2) (sourceB73 + difference 2 5) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1624) := by
    have ha : (tripleCharges (sourceA73 + difference 5 2) (sourceB73 + difference 2 5) sourceC73) = raw3999 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3999; decide +kernel
    rw [ha]
    exact (canonical3999 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA73 + difference 5 3) (sourceB73 + difference 3 5) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1624) := by
    have ha : (tripleCharges (sourceA73 + difference 5 3) (sourceB73 + difference 3 5) sourceC73) = raw4000 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw4000; decide +kernel
    rw [ha]
    exact (canonical4000 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA73 + difference 5 4) (sourceB73 + difference 4 5) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1628) := by
    have ha : (tripleCharges (sourceA73 + difference 5 4) (sourceB73 + difference 4 5) sourceC73) = raw4001 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw4001; decide +kernel
    rw [ha]
    exact (canonical4001 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA73 sourceB73 sourceC73
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm73, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq74 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm74 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA74 + difference 0 0) (sourceB74 + difference 0 0) sourceC74) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA74 + difference 0 0) (sourceB74 + difference 0 0) sourceC74) = raw4002 := by
      apply Matrix.ext; unfold tripleCharges sourceA74 sourceB74 sourceC74 difference raw4002; decide +kernel
    rw [ha]
    exact (canonical4002 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA74 + difference 0 1) (sourceB74 + difference 1 0) sourceC74) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA74 + difference 0 1) (sourceB74 + difference 1 0) sourceC74) = raw4003 := by
      apply Matrix.ext; unfold tripleCharges sourceA74 sourceB74 sourceC74 difference raw4003; decide +kernel
    rw [ha]
    exact (canonical4003 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA74 + difference 0 2) (sourceB74 + difference 2 0) sourceC74) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA74 + difference 0 2) (sourceB74 + difference 2 0) sourceC74) = raw4004 := by
      apply Matrix.ext; unfold tripleCharges sourceA74 sourceB74 sourceC74 difference raw4004; decide +kernel
    rw [ha]
    exact (canonical4004 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA74 + difference 0 3) (sourceB74 + difference 3 0) sourceC74) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA74 + difference 0 3) (sourceB74 + difference 3 0) sourceC74) = raw4005 := by
      apply Matrix.ext; unfold tripleCharges sourceA74 sourceB74 sourceC74 difference raw4005; decide +kernel
    rw [ha]
    exact (canonical4005 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA74 + difference 0 4) (sourceB74 + difference 4 0) sourceC74) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA74 + difference 0 4) (sourceB74 + difference 4 0) sourceC74) = raw4006 := by
      apply Matrix.ext; unfold tripleCharges sourceA74 sourceB74 sourceC74 difference raw4006; decide +kernel
    rw [ha]
    exact (canonical4006 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA74 + difference 0 5) (sourceB74 + difference 5 0) sourceC74) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3907) := by
    have ha : (tripleCharges (sourceA74 + difference 0 5) (sourceB74 + difference 5 0) sourceC74) = raw4007 := by
      apply Matrix.ext; unfold tripleCharges sourceA74 sourceB74 sourceC74 difference raw4007; decide +kernel
    rw [ha]
    exact (canonical4007 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA74 + sourceB74) sourceC74) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA74 + sourceB74) sourceC74) = raw4008 := by
      apply Matrix.ext; unfold doubleCharges sourceA74 sourceB74 sourceC74 raw4008; decide +kernel
    rw [ha]
    exact (canonical4008 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA74 sourceB74 sourceC74
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm74, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq75 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm75 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA75 + difference 0 0) (sourceB75 + difference 0 0) sourceC75) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA75 + difference 0 0) (sourceB75 + difference 0 0) sourceC75) = raw4002 := by
      apply Matrix.ext; unfold tripleCharges sourceA75 sourceB75 sourceC75 difference raw4002; decide +kernel
    rw [ha]
    exact (canonical4002 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA75 + difference 1 0) (sourceB75 + difference 0 1) sourceC75) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1279) := by
    have ha : (tripleCharges (sourceA75 + difference 1 0) (sourceB75 + difference 0 1) sourceC75) = raw4009 := by
      apply Matrix.ext; unfold tripleCharges sourceA75 sourceB75 sourceC75 difference raw4009; decide +kernel
    rw [ha]
    exact (canonical4009 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA75 + difference 2 0) (sourceB75 + difference 0 2) sourceC75) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1224) := by
    have ha : (tripleCharges (sourceA75 + difference 2 0) (sourceB75 + difference 0 2) sourceC75) = raw4010 := by
      apply Matrix.ext; unfold tripleCharges sourceA75 sourceB75 sourceC75 difference raw4010; decide +kernel
    rw [ha]
    exact (canonical4010 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA75 + difference 3 0) (sourceB75 + difference 0 3) sourceC75) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1224) := by
    have ha : (tripleCharges (sourceA75 + difference 3 0) (sourceB75 + difference 0 3) sourceC75) = raw4011 := by
      apply Matrix.ext; unfold tripleCharges sourceA75 sourceB75 sourceC75 difference raw4011; decide +kernel
    rw [ha]
    exact (canonical4011 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA75 + difference 4 0) (sourceB75 + difference 0 4) sourceC75) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA75 + difference 4 0) (sourceB75 + difference 0 4) sourceC75) = raw4012 := by
      apply Matrix.ext; unfold tripleCharges sourceA75 sourceB75 sourceC75 difference raw4012; decide +kernel
    rw [ha]
    exact (canonical4012 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA75 + difference 5 0) (sourceB75 + difference 0 5) sourceC75) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1227) := by
    have ha : (tripleCharges (sourceA75 + difference 5 0) (sourceB75 + difference 0 5) sourceC75) = raw4013 := by
      apply Matrix.ext; unfold tripleCharges sourceA75 sourceB75 sourceC75 difference raw4013; decide +kernel
    rw [ha]
    exact (canonical4013 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA75 + sourceB75) sourceC75) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA75 + sourceB75) sourceC75) = raw4008 := by
      apply Matrix.ext; unfold doubleCharges sourceA75 sourceB75 sourceC75 raw4008; decide +kernel
    rw [ha]
    exact (canonical4008 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA75 sourceB75 sourceC75
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm75, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq76 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm76 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA76 + difference 1 0) (sourceB76 + difference 0 1) sourceC76) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1279) := by
    have ha : (tripleCharges (sourceA76 + difference 1 0) (sourceB76 + difference 0 1) sourceC76) = raw4009 := by
      apply Matrix.ext; unfold tripleCharges sourceA76 sourceB76 sourceC76 difference raw4009; decide +kernel
    rw [ha]
    exact (canonical4009 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA76 + difference 1 1) (sourceB76 + difference 1 1) sourceC76) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA76 + difference 1 1) (sourceB76 + difference 1 1) sourceC76) = raw4002 := by
      apply Matrix.ext; unfold tripleCharges sourceA76 sourceB76 sourceC76 difference raw4002; decide +kernel
    rw [ha]
    exact (canonical4002 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA76 + difference 1 2) (sourceB76 + difference 2 1) sourceC76) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2579) := by
    have ha : (tripleCharges (sourceA76 + difference 1 2) (sourceB76 + difference 2 1) sourceC76) = raw4014 := by
      apply Matrix.ext; unfold tripleCharges sourceA76 sourceB76 sourceC76 difference raw4014; decide +kernel
    rw [ha]
    exact (canonical4014 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA76 + difference 1 3) (sourceB76 + difference 3 1) sourceC76) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2579) := by
    have ha : (tripleCharges (sourceA76 + difference 1 3) (sourceB76 + difference 3 1) sourceC76) = raw4015 := by
      apply Matrix.ext; unfold tripleCharges sourceA76 sourceB76 sourceC76 difference raw4015; decide +kernel
    rw [ha]
    exact (canonical4015 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA76 + difference 1 4) (sourceB76 + difference 4 1) sourceC76) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2651) := by
    have ha : (tripleCharges (sourceA76 + difference 1 4) (sourceB76 + difference 4 1) sourceC76) = raw4016 := by
      apply Matrix.ext; unfold tripleCharges sourceA76 sourceB76 sourceC76 difference raw4016; decide +kernel
    rw [ha]
    exact (canonical4016 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA76 + difference 1 5) (sourceB76 + difference 5 1) sourceC76) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA76 + difference 1 5) (sourceB76 + difference 5 1) sourceC76) = raw4017 := by
      apply Matrix.ext; unfold tripleCharges sourceA76 sourceB76 sourceC76 difference raw4017; decide +kernel
    rw [ha]
    exact (canonical4017 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA76 + sourceB76) sourceC76) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA76 + sourceB76) sourceC76) = raw4008 := by
      apply Matrix.ext; unfold doubleCharges sourceA76 sourceB76 sourceC76 raw4008; decide +kernel
    rw [ha]
    exact (canonical4008 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA76 sourceB76 sourceC76
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm76, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq77 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm77 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA77 + difference 0 1) (sourceB77 + difference 1 0) sourceC77) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA77 + difference 0 1) (sourceB77 + difference 1 0) sourceC77) = raw4003 := by
      apply Matrix.ext; unfold tripleCharges sourceA77 sourceB77 sourceC77 difference raw4003; decide +kernel
    rw [ha]
    exact (canonical4003 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA77 + difference 1 1) (sourceB77 + difference 1 1) sourceC77) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA77 + difference 1 1) (sourceB77 + difference 1 1) sourceC77) = raw4002 := by
      apply Matrix.ext; unfold tripleCharges sourceA77 sourceB77 sourceC77 difference raw4002; decide +kernel
    rw [ha]
    exact (canonical4002 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA77 + difference 2 1) (sourceB77 + difference 1 2) sourceC77) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2495) := by
    have ha : (tripleCharges (sourceA77 + difference 2 1) (sourceB77 + difference 1 2) sourceC77) = raw4018 := by
      apply Matrix.ext; unfold tripleCharges sourceA77 sourceB77 sourceC77 difference raw4018; decide +kernel
    rw [ha]
    exact (canonical4018 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA77 + difference 3 1) (sourceB77 + difference 1 3) sourceC77) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2495) := by
    have ha : (tripleCharges (sourceA77 + difference 3 1) (sourceB77 + difference 1 3) sourceC77) = raw4019 := by
      apply Matrix.ext; unfold tripleCharges sourceA77 sourceB77 sourceC77 difference raw4019; decide +kernel
    rw [ha]
    exact (canonical4019 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA77 + difference 4 1) (sourceB77 + difference 1 4) sourceC77) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA77 + difference 4 1) (sourceB77 + difference 1 4) sourceC77) = raw4020 := by
      apply Matrix.ext; unfold tripleCharges sourceA77 sourceB77 sourceC77 difference raw4020; decide +kernel
    rw [ha]
    exact (canonical4020 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA77 + difference 5 1) (sourceB77 + difference 1 5) sourceC77) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1372) := by
    have ha : (tripleCharges (sourceA77 + difference 5 1) (sourceB77 + difference 1 5) sourceC77) = raw4021 := by
      apply Matrix.ext; unfold tripleCharges sourceA77 sourceB77 sourceC77 difference raw4021; decide +kernel
    rw [ha]
    exact (canonical4021 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA77 + sourceB77) sourceC77) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA77 + sourceB77) sourceC77) = raw4008 := by
      apply Matrix.ext; unfold doubleCharges sourceA77 sourceB77 sourceC77 raw4008; decide +kernel
    rw [ha]
    exact (canonical4008 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA77 sourceB77 sourceC77
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm77, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck48 : Integer.Sparse.reindex keyMap MixedData.row48 = numericRow48 := by decide +kernel

theorem numericCheck48 (x : Master → ℝ) : Integer.Sparse.eval numericRow48 x =
    (1 : ℝ) * reducedSource48 x := by
  norm_num [numericRow48, reducedSource48, Integer.Sparse.eval, Sparse.eval, nodeValue2040, nodeValue2041, nodeValue2042, nodeValue2055, nodeValue2284, nodeValue4085]

theorem reindexCheck49 : Integer.Sparse.reindex keyMap MixedData.row49 = numericRow49 := by decide +kernel

theorem numericCheck49 (x : Master → ℝ) : Integer.Sparse.eval numericRow49 x =
    (1 : ℝ) * reducedSource49 x := by
  norm_num [numericRow49, reducedSource49, Integer.Sparse.eval, Sparse.eval, nodeValue1068, nodeValue2042, nodeValue2284, nodeValue4085]

theorem reindexCheck50 : Integer.Sparse.reindex keyMap MixedData.row50 = numericRow50 := by decide +kernel

theorem numericCheck50 (x : Master → ℝ) : Integer.Sparse.eval numericRow50 x =
    (1 : ℝ) * reducedSource50 x := by
  norm_num [numericRow50, reducedSource50, Integer.Sparse.eval, Sparse.eval, nodeValue2235, nodeValue3155, nodeValue3158, nodeValue3619, nodeValue4083]

theorem reindexCheck51 : Integer.Sparse.reindex keyMap MixedData.row51 = numericRow51 := by decide +kernel

theorem numericCheck51 (x : Master → ℝ) : Integer.Sparse.eval numericRow51 x =
    (1 : ℝ) * reducedSource51 x := by
  norm_num [numericRow51, reducedSource51, Integer.Sparse.eval, Sparse.eval, nodeValue1014, nodeValue1016, nodeValue1024, nodeValue2235, nodeValue4083]

theorem reindexCheck52 : Integer.Sparse.reindex keyMap MixedData.row52 = numericRow52 := by decide +kernel

theorem numericCheck52 (x : Master → ℝ) : Integer.Sparse.eval numericRow52 x =
    (1 : ℝ) * reducedSource52 x := by
  norm_num [numericRow52, reducedSource52, Integer.Sparse.eval, Sparse.eval, nodeValue1014, nodeValue2083, nodeValue2233, nodeValue2235, nodeValue4083]

theorem reindexCheck53 : Integer.Sparse.reindex keyMap MixedData.row53 = numericRow53 := by decide +kernel

theorem numericCheck53 (x : Master → ℝ) : Integer.Sparse.eval numericRow53 x =
    (1 : ℝ) * reducedSource53 x := by
  norm_num [numericRow53, reducedSource53, Integer.Sparse.eval, Sparse.eval, nodeValue1457, nodeValue2010, nodeValue2235, nodeValue3155, nodeValue4083]

theorem reindexCheck54 : Integer.Sparse.reindex keyMap MixedData.row54 = numericRow54 := by decide +kernel

theorem numericCheck54 (x : Master → ℝ) : Integer.Sparse.eval numericRow54 x =
    (1 : ℝ) * reducedSource54 x := by
  norm_num [numericRow54, reducedSource54, Integer.Sparse.eval, Sparse.eval, nodeValue1024, nodeValue2010, nodeValue2092, nodeValue2235, nodeValue2245, nodeValue4083]

theorem reindexCheck55 : Integer.Sparse.reindex keyMap MixedData.row55 = numericRow55 := by decide +kernel

theorem numericCheck55 (x : Master → ℝ) : Integer.Sparse.eval numericRow55 x =
    (1 : ℝ) * reducedSource55 x := by
  norm_num [numericRow55, reducedSource55, Integer.Sparse.eval, Sparse.eval, nodeValue1460, nodeValue2083, nodeValue2092, nodeValue2235, nodeValue3158, nodeValue4083]

theorem reindexCheck56 : Integer.Sparse.reindex keyMap MixedData.row56 = numericRow56 := by decide +kernel

theorem numericCheck56 (x : Master → ℝ) : Integer.Sparse.eval numericRow56 x =
    (1 : ℝ) * reducedSource56 x := by
  norm_num [numericRow56, reducedSource56, Integer.Sparse.eval, Sparse.eval, nodeValue1016, nodeValue1457, nodeValue1460, nodeValue2235, nodeValue4083]

theorem reindexCheck57 : Integer.Sparse.reindex keyMap MixedData.row57 = numericRow57 := by decide +kernel

theorem numericCheck57 (x : Master → ℝ) : Integer.Sparse.eval numericRow57 x =
    (1 : ℝ) * reducedSource57 x := by
  norm_num [numericRow57, reducedSource57, Integer.Sparse.eval, Sparse.eval, nodeValue1078, nodeValue2050, nodeValue2283, nodeValue2290, nodeValue4085]

theorem reindexCheck59 : Integer.Sparse.reindex keyMap MixedData.row59 = numericRow59 := by decide +kernel

theorem numericCheck59 (x : Master → ℝ) : Integer.Sparse.eval numericRow59 x =
    (2160 : ℝ) * reducedSource59 x := by
  norm_num [numericRow59, reducedSource59, Integer.Sparse.eval, Sparse.eval, nodeValue1624, nodeValue1628, nodeValue1629, nodeValue1729, nodeValue2837, nodeValue2842, nodeValue3052, nodeValue3242, nodeValue3247, nodeValue3302, nodeValue3358, nodeValue3437, nodeValue3472, nodeValue3486, nodeValue3523, nodeValue3535, nodeValue3541, nodeValue3548, nodeValue3584, nodeValue3626, nodeValue3862]
  ring

theorem reindexCheck60 : Integer.Sparse.reindex keyMap MixedData.row60 = numericRow60 := by decide +kernel

theorem numericCheck60 (x : Master → ℝ) : Integer.Sparse.eval numericRow60 x =
    (1 : ℝ) * reducedSource60 x := by
  norm_num [numericRow60, reducedSource60, Integer.Sparse.eval, Sparse.eval, nodeValue2734, nodeValue2777, nodeValue3038, nodeValue3054, nodeValue3907, nodeValue4092]

theorem reindexCheck61 : Integer.Sparse.reindex keyMap MixedData.row61 = numericRow61 := by decide +kernel

theorem numericCheck61 (x : Master → ℝ) : Integer.Sparse.eval numericRow61 x =
    (1 : ℝ) * reducedSource61 x := by
  norm_num [numericRow61, reducedSource61, Integer.Sparse.eval, Sparse.eval, nodeValue1224, nodeValue1227, nodeValue1243, nodeValue1279, nodeValue2734, nodeValue4092]

theorem reindexCheck62 : Integer.Sparse.reindex keyMap MixedData.row62 = numericRow62 := by decide +kernel

theorem numericCheck62 (x : Master → ℝ) : Integer.Sparse.eval numericRow62 x =
    (1 : ℝ) * reducedSource62 x := by
  norm_num [numericRow62, reducedSource62, Integer.Sparse.eval, Sparse.eval, nodeValue1279, nodeValue2579, nodeValue2651, nodeValue2734, nodeValue2774, nodeValue4092]

theorem reindexCheck63 : Integer.Sparse.reindex keyMap MixedData.row63 = numericRow63 := by decide +kernel

theorem numericCheck63 (x : Master → ℝ) : Integer.Sparse.eval numericRow63 x =
    (1 : ℝ) * reducedSource63 x := by
  norm_num [numericRow63, reducedSource63, Integer.Sparse.eval, Sparse.eval, nodeValue1372, nodeValue2495, nodeValue2519, nodeValue2734, nodeValue3054, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero48 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource48 (mixedVector B) = 0 := by
  have h2040 : mixedVector B (Sum.inr 2040) = Sparse.eval nodeValue2040 (mixedVector B) := by
    change mixedMoment B node2040 node2040Labels = _
    exact sound2040 B hB hF
  have h2041 : mixedVector B (Sum.inr 2041) = Sparse.eval nodeValue2041 (mixedVector B) := by
    change mixedMoment B node2041 node2041Labels = _
    exact sound2041 B hB hF
  have h2042 : mixedVector B (Sum.inr 2042) = Sparse.eval nodeValue2042 (mixedVector B) := by
    change mixedMoment B node2042 node2042Labels = _
    exact sound2042 B hB hF
  have h2055 : mixedVector B (Sum.inr 2055) = Sparse.eval nodeValue2055 (mixedVector B) := by
    change mixedMoment B node2055 node2055Labels = _
    exact sound2055 B hB hF
  have h2284 : mixedVector B (Sum.inr 2284) = Sparse.eval nodeValue2284 (mixedVector B) := by
    change mixedMoment B node2284 node2284Labels = _
    exact sound2284 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm54, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2040, h2041, h2042, h2055, h2284, h4085, reducedSource48] using sourceEq54 B hB

theorem rowSound48 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row48 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck48, numericCheck48, reducedZero48 B hB hF, mul_zero]

theorem reducedZero49 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource49 (mixedVector B) = 0 := by
  have h1068 : mixedVector B (Sum.inr 1068) = Sparse.eval nodeValue1068 (mixedVector B) := by
    change mixedMoment B node1068 node1068Labels = _
    exact sound1068 B hB hF
  have h2042 : mixedVector B (Sum.inr 2042) = Sparse.eval nodeValue2042 (mixedVector B) := by
    change mixedMoment B node2042 node2042Labels = _
    exact sound2042 B hB hF
  have h2284 : mixedVector B (Sum.inr 2284) = Sparse.eval nodeValue2284 (mixedVector B) := by
    change mixedMoment B node2284 node2284Labels = _
    exact sound2284 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm55, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1068, h2042, h2284, h4085, reducedSource49] using sourceEq55 B hB

theorem rowSound49 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row49 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck49, numericCheck49, reducedZero49 B hB hF, mul_zero]

theorem reducedZero50 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource50 (mixedVector B) = 0 := by
  have h2235 : mixedVector B (Sum.inr 2235) = Sparse.eval nodeValue2235 (mixedVector B) := by
    change mixedMoment B node2235 node2235Labels = _
    exact sound2235 B hB hF
  have h3155 : mixedVector B (Sum.inr 3155) = Sparse.eval nodeValue3155 (mixedVector B) := by
    change mixedMoment B node3155 node3155Labels = _
    exact sound3155 B hB hF
  have h3158 : mixedVector B (Sum.inr 3158) = Sparse.eval nodeValue3158 (mixedVector B) := by
    change mixedMoment B node3158 node3158Labels = _
    exact sound3158 B hB hF
  have h3619 : mixedVector B (Sum.inr 3619) = Sparse.eval nodeValue3619 (mixedVector B) := by
    change mixedMoment B node3619 node3619Labels = _
    exact sound3619 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm59, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2235, h3155, h3158, h3619, h4083, reducedSource50] using sourceEq59 B hB

theorem rowSound50 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row50 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck50, numericCheck50, reducedZero50 B hB hF, mul_zero]

theorem reducedZero51 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource51 (mixedVector B) = 0 := by
  have h1014 : mixedVector B (Sum.inr 1014) = Sparse.eval nodeValue1014 (mixedVector B) := by
    change mixedMoment B node1014 node1014Labels = _
    exact sound1014 B hB hF
  have h1016 : mixedVector B (Sum.inr 1016) = Sparse.eval nodeValue1016 (mixedVector B) := by
    change mixedMoment B node1016 node1016Labels = _
    exact sound1016 B hB hF
  have h1024 : mixedVector B (Sum.inr 1024) = Sparse.eval nodeValue1024 (mixedVector B) := by
    change mixedMoment B node1024 node1024Labels = _
    exact sound1024 B hB hF
  have h2235 : mixedVector B (Sum.inr 2235) = Sparse.eval nodeValue2235 (mixedVector B) := by
    change mixedMoment B node2235 node2235Labels = _
    exact sound2235 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm60, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1014, h1016, h1024, h2235, h4083, reducedSource51] using sourceEq60 B hB

theorem rowSound51 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row51 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck51, numericCheck51, reducedZero51 B hB hF, mul_zero]

theorem reducedZero52 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource52 (mixedVector B) = 0 := by
  have h1014 : mixedVector B (Sum.inr 1014) = Sparse.eval nodeValue1014 (mixedVector B) := by
    change mixedMoment B node1014 node1014Labels = _
    exact sound1014 B hB hF
  have h2083 : mixedVector B (Sum.inr 2083) = Sparse.eval nodeValue2083 (mixedVector B) := by
    change mixedMoment B node2083 node2083Labels = _
    exact sound2083 B hB hF
  have h2233 : mixedVector B (Sum.inr 2233) = Sparse.eval nodeValue2233 (mixedVector B) := by
    change mixedMoment B node2233 node2233Labels = _
    exact sound2233 B hB hF
  have h2235 : mixedVector B (Sum.inr 2235) = Sparse.eval nodeValue2235 (mixedVector B) := by
    change mixedMoment B node2235 node2235Labels = _
    exact sound2235 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm61, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1014, h2083, h2233, h2235, h4083, reducedSource52] using sourceEq61 B hB

theorem rowSound52 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row52 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck52, numericCheck52, reducedZero52 B hB hF, mul_zero]

theorem reducedZero53 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource53 (mixedVector B) = 0 := by
  have h1457 : mixedVector B (Sum.inr 1457) = Sparse.eval nodeValue1457 (mixedVector B) := by
    change mixedMoment B node1457 node1457Labels = _
    exact sound1457 B hB hF
  have h2010 : mixedVector B (Sum.inr 2010) = Sparse.eval nodeValue2010 (mixedVector B) := by
    change mixedMoment B node2010 node2010Labels = _
    exact sound2010 B hB hF
  have h2235 : mixedVector B (Sum.inr 2235) = Sparse.eval nodeValue2235 (mixedVector B) := by
    change mixedMoment B node2235 node2235Labels = _
    exact sound2235 B hB hF
  have h3155 : mixedVector B (Sum.inr 3155) = Sparse.eval nodeValue3155 (mixedVector B) := by
    change mixedMoment B node3155 node3155Labels = _
    exact sound3155 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm62, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1457, h2010, h2235, h3155, h4083, reducedSource53] using sourceEq62 B hB

theorem rowSound53 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row53 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck53, numericCheck53, reducedZero53 B hB hF, mul_zero]

theorem reducedZero54 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource54 (mixedVector B) = 0 := by
  have h1024 : mixedVector B (Sum.inr 1024) = Sparse.eval nodeValue1024 (mixedVector B) := by
    change mixedMoment B node1024 node1024Labels = _
    exact sound1024 B hB hF
  have h2010 : mixedVector B (Sum.inr 2010) = Sparse.eval nodeValue2010 (mixedVector B) := by
    change mixedMoment B node2010 node2010Labels = _
    exact sound2010 B hB hF
  have h2092 : mixedVector B (Sum.inr 2092) = Sparse.eval nodeValue2092 (mixedVector B) := by
    change mixedMoment B node2092 node2092Labels = _
    exact sound2092 B hB hF
  have h2235 : mixedVector B (Sum.inr 2235) = Sparse.eval nodeValue2235 (mixedVector B) := by
    change mixedMoment B node2235 node2235Labels = _
    exact sound2235 B hB hF
  have h2245 : mixedVector B (Sum.inr 2245) = Sparse.eval nodeValue2245 (mixedVector B) := by
    change mixedMoment B node2245 node2245Labels = _
    exact sound2245 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm63, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1024, h2010, h2092, h2235, h2245, h4083, reducedSource54] using sourceEq63 B hB

theorem rowSound54 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row54 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck54, numericCheck54, reducedZero54 B hB hF, mul_zero]

theorem reducedZero55 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource55 (mixedVector B) = 0 := by
  have h1460 : mixedVector B (Sum.inr 1460) = Sparse.eval nodeValue1460 (mixedVector B) := by
    change mixedMoment B node1460 node1460Labels = _
    exact sound1460 B hB hF
  have h2083 : mixedVector B (Sum.inr 2083) = Sparse.eval nodeValue2083 (mixedVector B) := by
    change mixedMoment B node2083 node2083Labels = _
    exact sound2083 B hB hF
  have h2092 : mixedVector B (Sum.inr 2092) = Sparse.eval nodeValue2092 (mixedVector B) := by
    change mixedMoment B node2092 node2092Labels = _
    exact sound2092 B hB hF
  have h2235 : mixedVector B (Sum.inr 2235) = Sparse.eval nodeValue2235 (mixedVector B) := by
    change mixedMoment B node2235 node2235Labels = _
    exact sound2235 B hB hF
  have h3158 : mixedVector B (Sum.inr 3158) = Sparse.eval nodeValue3158 (mixedVector B) := by
    change mixedMoment B node3158 node3158Labels = _
    exact sound3158 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm64, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1460, h2083, h2092, h2235, h3158, h4083, reducedSource55] using sourceEq64 B hB

theorem rowSound55 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row55 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck55, numericCheck55, reducedZero55 B hB hF, mul_zero]

theorem reducedZero56 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource56 (mixedVector B) = 0 := by
  have h1016 : mixedVector B (Sum.inr 1016) = Sparse.eval nodeValue1016 (mixedVector B) := by
    change mixedMoment B node1016 node1016Labels = _
    exact sound1016 B hB hF
  have h1457 : mixedVector B (Sum.inr 1457) = Sparse.eval nodeValue1457 (mixedVector B) := by
    change mixedMoment B node1457 node1457Labels = _
    exact sound1457 B hB hF
  have h1460 : mixedVector B (Sum.inr 1460) = Sparse.eval nodeValue1460 (mixedVector B) := by
    change mixedMoment B node1460 node1460Labels = _
    exact sound1460 B hB hF
  have h2235 : mixedVector B (Sum.inr 2235) = Sparse.eval nodeValue2235 (mixedVector B) := by
    change mixedMoment B node2235 node2235Labels = _
    exact sound2235 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm65, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1016, h1457, h1460, h2235, h4083, reducedSource56] using sourceEq65 B hB

theorem rowSound56 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row56 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck56, numericCheck56, reducedZero56 B hB hF, mul_zero]

theorem reducedZero57 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource57 (mixedVector B) = 0 := by
  have h1078 : mixedVector B (Sum.inr 1078) = Sparse.eval nodeValue1078 (mixedVector B) := by
    change mixedMoment B node1078 node1078Labels = _
    exact sound1078 B hB hF
  have h2050 : mixedVector B (Sum.inr 2050) = Sparse.eval nodeValue2050 (mixedVector B) := by
    change mixedMoment B node2050 node2050Labels = _
    exact sound2050 B hB hF
  have h2283 : mixedVector B (Sum.inr 2283) = Sparse.eval nodeValue2283 (mixedVector B) := by
    change mixedMoment B node2283 node2283Labels = _
    exact sound2283 B hB hF
  have h2290 : mixedVector B (Sum.inr 2290) = Sparse.eval nodeValue2290 (mixedVector B) := by
    change mixedMoment B node2290 node2290Labels = _
    exact sound2290 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm68, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1078, h2050, h2283, h2290, h4085, reducedSource57] using sourceEq68 B hB

theorem rowSound57 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row57 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck57, numericCheck57, reducedZero57 B hB hF, mul_zero]

theorem reducedZero59 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource59 (mixedVector B) = 0 := by
  have h1624 : mixedVector B (Sum.inr 1624) = Sparse.eval nodeValue1624 (mixedVector B) := by
    change mixedMoment B node1624 node1624Labels = _
    exact sound1624 B hB hF
  have h1628 : mixedVector B (Sum.inr 1628) = Sparse.eval nodeValue1628 (mixedVector B) := by
    change mixedMoment B node1628 node1628Labels = _
    exact sound1628 B hB hF
  have h1629 : mixedVector B (Sum.inr 1629) = Sparse.eval nodeValue1629 (mixedVector B) := by
    change mixedMoment B node1629 node1629Labels = _
    exact sound1629 B hB hF
  have h1729 : mixedVector B (Sum.inr 1729) = Sparse.eval nodeValue1729 (mixedVector B) := by
    change mixedMoment B node1729 node1729Labels = _
    exact sound1729 B hB hF
  have h2837 : mixedVector B (Sum.inr 2837) = Sparse.eval nodeValue2837 (mixedVector B) := by
    change mixedMoment B node2837 node2837Labels = _
    exact sound2837 B hB hF
  have h2842 : mixedVector B (Sum.inr 2842) = Sparse.eval nodeValue2842 (mixedVector B) := by
    change mixedMoment B node2842 node2842Labels = _
    exact sound2842 B hB hF
  have h3052 : mixedVector B (Sum.inr 3052) = Sparse.eval nodeValue3052 (mixedVector B) := by
    change mixedMoment B node3052 node3052Labels = _
    exact sound3052 B hB hF
  have h3242 : mixedVector B (Sum.inr 3242) = Sparse.eval nodeValue3242 (mixedVector B) := by
    change mixedMoment B node3242 node3242Labels = _
    exact sound3242 B hB hF
  have h3247 : mixedVector B (Sum.inr 3247) = Sparse.eval nodeValue3247 (mixedVector B) := by
    change mixedMoment B node3247 node3247Labels = _
    exact sound3247 B hB hF
  have h3302 : mixedVector B (Sum.inr 3302) = Sparse.eval nodeValue3302 (mixedVector B) := by
    change mixedMoment B node3302 node3302Labels = _
    exact sound3302 B hB hF
  have h3358 : mixedVector B (Sum.inr 3358) = Sparse.eval nodeValue3358 (mixedVector B) := by
    change mixedMoment B node3358 node3358Labels = _
    exact sound3358 B hB hF
  have h3437 : mixedVector B (Sum.inr 3437) = Sparse.eval nodeValue3437 (mixedVector B) := by
    change mixedMoment B node3437 node3437Labels = _
    exact sound3437 B hB hF
  have h3472 : mixedVector B (Sum.inr 3472) = Sparse.eval nodeValue3472 (mixedVector B) := by
    change mixedMoment B node3472 node3472Labels = _
    exact sound3472 B hB hF
  have h3486 : mixedVector B (Sum.inr 3486) = Sparse.eval nodeValue3486 (mixedVector B) := by
    change mixedMoment B node3486 node3486Labels = _
    exact sound3486 B hB hF
  have h3523 : mixedVector B (Sum.inr 3523) = Sparse.eval nodeValue3523 (mixedVector B) := by
    change mixedMoment B node3523 node3523Labels = _
    exact sound3523 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h3548 : mixedVector B (Sum.inr 3548) = Sparse.eval nodeValue3548 (mixedVector B) := by
    change mixedMoment B node3548 node3548Labels = _
    exact sound3548 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h3626 : mixedVector B (Sum.inr 3626) = Sparse.eval nodeValue3626 (mixedVector B) := by
    change mixedMoment B node3626 node3626Labels = _
    exact sound3626 B hB hF
  have h3862 : mixedVector B (Sum.inr 3862) = Sparse.eval nodeValue3862 (mixedVector B) := by
    change mixedMoment B node3862 node3862Labels = _
    exact sound3862 B hB hF
  simpa only [sourceForm73, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1624, h1628, h1629, h1729, h2837, h2842, h3052, h3242, h3247, h3302, h3358, h3437, h3472, h3486, h3523, h3535, h3541, h3548, h3584, h3626, h3862, reducedSource59] using sourceEq73 B hB

theorem rowSound59 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row59 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck59, numericCheck59, reducedZero59 B hB hF, mul_zero]

theorem reducedZero60 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource60 (mixedVector B) = 0 := by
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h3907 : mixedVector B (Sum.inr 3907) = Sparse.eval nodeValue3907 (mixedVector B) := by
    change mixedMoment B node3907 node3907Labels = _
    exact sound3907 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm74, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2734, h2777, h3038, h3054, h3907, h4092, reducedSource60] using sourceEq74 B hB

theorem rowSound60 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row60 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck60, numericCheck60, reducedZero60 B hB hF, mul_zero]

theorem reducedZero61 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource61 (mixedVector B) = 0 := by
  have h1224 : mixedVector B (Sum.inr 1224) = Sparse.eval nodeValue1224 (mixedVector B) := by
    change mixedMoment B node1224 node1224Labels = _
    exact sound1224 B hB hF
  have h1227 : mixedVector B (Sum.inr 1227) = Sparse.eval nodeValue1227 (mixedVector B) := by
    change mixedMoment B node1227 node1227Labels = _
    exact sound1227 B hB hF
  have h1243 : mixedVector B (Sum.inr 1243) = Sparse.eval nodeValue1243 (mixedVector B) := by
    change mixedMoment B node1243 node1243Labels = _
    exact sound1243 B hB hF
  have h1279 : mixedVector B (Sum.inr 1279) = Sparse.eval nodeValue1279 (mixedVector B) := by
    change mixedMoment B node1279 node1279Labels = _
    exact sound1279 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm75, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1224, h1227, h1243, h1279, h2734, h4092, reducedSource61] using sourceEq75 B hB

theorem rowSound61 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row61 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck61, numericCheck61, reducedZero61 B hB hF, mul_zero]

theorem reducedZero62 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource62 (mixedVector B) = 0 := by
  have h1279 : mixedVector B (Sum.inr 1279) = Sparse.eval nodeValue1279 (mixedVector B) := by
    change mixedMoment B node1279 node1279Labels = _
    exact sound1279 B hB hF
  have h2579 : mixedVector B (Sum.inr 2579) = Sparse.eval nodeValue2579 (mixedVector B) := by
    change mixedMoment B node2579 node2579Labels = _
    exact sound2579 B hB hF
  have h2651 : mixedVector B (Sum.inr 2651) = Sparse.eval nodeValue2651 (mixedVector B) := by
    change mixedMoment B node2651 node2651Labels = _
    exact sound2651 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h2774 : mixedVector B (Sum.inr 2774) = Sparse.eval nodeValue2774 (mixedVector B) := by
    change mixedMoment B node2774 node2774Labels = _
    exact sound2774 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm76, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1279, h2579, h2651, h2734, h2774, h4092, reducedSource62] using sourceEq76 B hB

theorem rowSound62 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row62 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck62, numericCheck62, reducedZero62 B hB hF, mul_zero]

theorem reducedZero63 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource63 (mixedVector B) = 0 := by
  have h1372 : mixedVector B (Sum.inr 1372) = Sparse.eval nodeValue1372 (mixedVector B) := by
    change mixedMoment B node1372 node1372Labels = _
    exact sound1372 B hB hF
  have h2495 : mixedVector B (Sum.inr 2495) = Sparse.eval nodeValue2495 (mixedVector B) := by
    change mixedMoment B node2495 node2495Labels = _
    exact sound2495 B hB hF
  have h2519 : mixedVector B (Sum.inr 2519) = Sparse.eval nodeValue2519 (mixedVector B) := by
    change mixedMoment B node2519 node2519Labels = _
    exact sound2519 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm77, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1372, h2495, h2519, h2734, h3054, h4092, reducedSource63] using sourceEq77 B hB

theorem rowSound63 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row63 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck63, numericCheck63, reducedZero63 B hB hF, mul_zero]

theorem sourceRowsAt48 : MixedData.sourceRows (48 : Fin 2425) =
    MixedData.row48 := by decide +kernel

theorem sourceRowsAt49 : MixedData.sourceRows (49 : Fin 2425) =
    MixedData.row49 := by decide +kernel

theorem sourceRowsAt50 : MixedData.sourceRows (50 : Fin 2425) =
    MixedData.row50 := by decide +kernel

theorem sourceRowsAt51 : MixedData.sourceRows (51 : Fin 2425) =
    MixedData.row51 := by decide +kernel

theorem sourceRowsAt52 : MixedData.sourceRows (52 : Fin 2425) =
    MixedData.row52 := by decide +kernel

theorem sourceRowsAt53 : MixedData.sourceRows (53 : Fin 2425) =
    MixedData.row53 := by decide +kernel

theorem sourceRowsAt54 : MixedData.sourceRows (54 : Fin 2425) =
    MixedData.row54 := by decide +kernel

theorem sourceRowsAt55 : MixedData.sourceRows (55 : Fin 2425) =
    MixedData.row55 := by decide +kernel

theorem sourceRowsAt56 : MixedData.sourceRows (56 : Fin 2425) =
    MixedData.row56 := by decide +kernel

theorem sourceRowsAt57 : MixedData.sourceRows (57 : Fin 2425) =
    MixedData.row57 := by decide +kernel

theorem sourceRowsAt58 : MixedData.sourceRows (58 : Fin 2425) =
    MixedData.row58 := by decide +kernel

theorem sourceRowsAt59 : MixedData.sourceRows (59 : Fin 2425) =
    MixedData.row59 := by decide +kernel

theorem sourceRowsAt60 : MixedData.sourceRows (60 : Fin 2425) =
    MixedData.row60 := by decide +kernel

theorem sourceRowsAt61 : MixedData.sourceRows (61 : Fin 2425) =
    MixedData.row61 := by decide +kernel

theorem sourceRowsAt62 : MixedData.sourceRows (62 : Fin 2425) =
    MixedData.row62 := by decide +kernel

theorem sourceRowsAt63 : MixedData.sourceRows (63 : Fin 2425) =
    MixedData.row63 := by decide +kernel

theorem chunkSound3_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 3) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 48 ∨ k.val = 49 ∨ k.val = 50 ∨ k.val = 51 ∨ k.val = 52 ∨ k.val = 53 ∨ k.val = 54 ∨ k.val = 55 ∨ k.val = 56 ∨ k.val = 57 ∨ k.val = 58 ∨ k.val = 59 ∨ k.val = 60 ∨ k.val = 61 ∨ k.val = 62 ∨ k.val = 63 := by omega
  rcases heq with h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63
  · have he : k = (48 : Fin 2425) := Fin.ext h48
    subst k
    rw [sourceRowsAt48]
    exact rowSound48 B hB hF
  · have he : k = (49 : Fin 2425) := Fin.ext h49
    subst k
    rw [sourceRowsAt49]
    exact rowSound49 B hB hF
  · have he : k = (50 : Fin 2425) := Fin.ext h50
    subst k
    rw [sourceRowsAt50]
    exact rowSound50 B hB hF
  · have he : k = (51 : Fin 2425) := Fin.ext h51
    subst k
    rw [sourceRowsAt51]
    exact rowSound51 B hB hF
  · have he : k = (52 : Fin 2425) := Fin.ext h52
    subst k
    rw [sourceRowsAt52]
    exact rowSound52 B hB hF
  · have he : k = (53 : Fin 2425) := Fin.ext h53
    subst k
    rw [sourceRowsAt53]
    exact rowSound53 B hB hF
  · have he : k = (54 : Fin 2425) := Fin.ext h54
    subst k
    rw [sourceRowsAt54]
    exact rowSound54 B hB hF
  · have he : k = (55 : Fin 2425) := Fin.ext h55
    subst k
    rw [sourceRowsAt55]
    exact rowSound55 B hB hF
  · have he : k = (56 : Fin 2425) := Fin.ext h56
    subst k
    rw [sourceRowsAt56]
    exact rowSound56 B hB hF
  · have he : k = (57 : Fin 2425) := Fin.ext h57
    subst k
    rw [sourceRowsAt57]
    exact rowSound57 B hB hF
  · have he : k = (58 : Fin 2425) := Fin.ext h58
    subst k
    rw [sourceRowsAt58]
    exact rowSound58_e B hB hF
  · have he : k = (59 : Fin 2425) := Fin.ext h59
    subst k
    rw [sourceRowsAt59]
    exact rowSound59 B hB hF
  · have he : k = (60 : Fin 2425) := Fin.ext h60
    subst k
    rw [sourceRowsAt60]
    exact rowSound60 B hB hF
  · have he : k = (61 : Fin 2425) := Fin.ext h61
    subst k
    rw [sourceRowsAt61]
    exact rowSound61 B hB hF
  · have he : k = (62 : Fin 2425) := Fin.ext h62
    subst k
    rw [sourceRowsAt62]
    exact rowSound62 B hB hF
  · have he : k = (63 : Fin 2425) := Fin.ext h63
    subst k
    rw [sourceRowsAt63]
    exact rowSound63 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound3_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound3_e_oai
