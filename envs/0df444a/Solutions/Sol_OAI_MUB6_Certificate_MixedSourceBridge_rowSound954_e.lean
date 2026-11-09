-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound954_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:14:24.815592+00:00
-- url     : https://prove2.me/submissions/f41920ff-7071-43bd-8b33-e8af1a2dfb7b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E128
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5439_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12939 raw12939Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw12939 raw12939Labels = mixedMoment B raw12939step0 raw12939step0Labels := by
      have hz : ∀ j, raw12939 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12939step0 = (fun i j => raw12939 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12939step0 raw12939; decide +kernel
      have hl : raw12939step0Labels = raw12939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12939 raw12939Labels permutation265 hz
    mixedMoment B raw12939step0 raw12939step0Labels = mixedMoment B raw12939step1 raw12939step1Labels := by
      have ha : raw12939step1 = (fun i j => raw12939step0 (permutation56 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12939step1 raw12939step0; decide +kernel
      have hl : raw12939step1Labels = raw12939step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12939step0 raw12939step0Labels permutation56 permutation4
    mixedMoment B raw12939step1 raw12939step1Labels = mixedMoment B raw12939step2 raw12939step2Labels := by
      have ha : raw12939step2 = -raw12939step1 := by apply Matrix.ext; change ∀ i j, raw12939step2 i j = -(raw12939step1 i j); unfold raw12939step2 raw12939step1; decide +kernel
      have hl : raw12939step2Labels = raw12939step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12939step2 raw12939step2Labels = mixedMoment B raw12939step3 raw12939step3Labels := by
      have ha : raw12939step3 = raw12939step2 := by apply Matrix.ext; unfold raw12939step3 raw12939step2; decide +kernel
      have hl : raw12939step2Labels = labelEmbedding7 ∘ raw12939step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12939step2 raw12939step2Labels raw12939step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

theorem canonical12940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12940 raw12940Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw12940 raw12940Labels = mixedMoment B raw12940step0 raw12940step0Labels := by
      have hz : ∀ j, raw12940 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12940step0 = (fun i j => raw12940 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12940step0 raw12940; decide +kernel
      have hl : raw12940step0Labels = raw12940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12940 raw12940Labels permutation434 hz
    mixedMoment B raw12940step0 raw12940step0Labels = mixedMoment B raw12940step1 raw12940step1Labels := by
      have hz : ∀ j, raw12940step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12940step1 = (fun i j => raw12940step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12940step1 raw12940step0; decide +kernel
      have hl : raw12940step1Labels = raw12940step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12940step0 raw12940step0Labels permutation56 hz
    mixedMoment B raw12940step1 raw12940step1Labels = mixedMoment B raw12940step2 raw12940step2Labels := by
      have ha : raw12940step2 = (fun i j => raw12940step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12940step2 raw12940step1; decide +kernel
      have hl : raw12940step2Labels = raw12940step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12940step1 raw12940step1Labels permutation17 permutation6
    mixedMoment B raw12940step2 raw12940step2Labels = mixedMoment B raw12940step3 raw12940step3Labels := by
      have ha : raw12940step3 = raw12940step2 := by apply Matrix.ext; unfold raw12940step3 raw12940step2; decide +kernel
      have hl : raw12940step2Labels = labelEmbedding9 ∘ raw12940step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12940step2 raw12940step2Labels raw12940step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5453 node5453Labels := by rfl

theorem canonical12941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12941 raw12941Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw12941 raw12941Labels = mixedMoment B raw12941step0 raw12941step0Labels := by
      have hz : ∀ j, raw12941 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12941step0 = (fun i j => raw12941 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12941step0 raw12941; decide +kernel
      have hl : raw12941step0Labels = raw12941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12941 raw12941Labels permutation520 hz
    mixedMoment B raw12941step0 raw12941step0Labels = mixedMoment B raw12941step1 raw12941step1Labels := by
      have hz : ∀ j, raw12941step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12941step1 = (fun i j => raw12941step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12941step1 raw12941step0; decide +kernel
      have hl : raw12941step1Labels = raw12941step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12941step0 raw12941step0Labels permutation56 hz
    mixedMoment B raw12941step1 raw12941step1Labels = mixedMoment B raw12941step2 raw12941step2Labels := by
      have ha : raw12941step2 = (fun i j => raw12941step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12941step2 raw12941step1; decide +kernel
      have hl : raw12941step2Labels = raw12941step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12941step1 raw12941step1Labels permutation17 permutation6
    mixedMoment B raw12941step2 raw12941step2Labels = mixedMoment B raw12941step3 raw12941step3Labels := by
      have ha : raw12941step3 = raw12941step2 := by apply Matrix.ext; unfold raw12941step3 raw12941step2; decide +kernel
      have hl : raw12941step2Labels = labelEmbedding9 ∘ raw12941step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12941step2 raw12941step2Labels raw12941step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5453 node5453Labels := by rfl

theorem canonical12942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12942 raw12942Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw12942 raw12942Labels = mixedMoment B raw12942step0 raw12942step0Labels := by
      have hz : ∀ j, raw12942 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12942step0 = (fun i j => raw12942 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12942step0 raw12942; decide +kernel
      have hl : raw12942step0Labels = raw12942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12942 raw12942Labels permutation590 hz
    mixedMoment B raw12942step0 raw12942step0Labels = mixedMoment B raw12942step1 raw12942step1Labels := by
      have hz : ∀ j, raw12942step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12942step1 = (fun i j => raw12942step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12942step1 raw12942step0; decide +kernel
      have hl : raw12942step1Labels = raw12942step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12942step0 raw12942step0Labels permutation56 hz
    mixedMoment B raw12942step1 raw12942step1Labels = mixedMoment B raw12942step2 raw12942step2Labels := by
      have ha : raw12942step2 = (fun i j => raw12942step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12942step2 raw12942step1; decide +kernel
      have hl : raw12942step2Labels = raw12942step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12942step1 raw12942step1Labels permutation17 permutation6
    mixedMoment B raw12942step2 raw12942step2Labels = mixedMoment B raw12942step3 raw12942step3Labels := by
      have ha : raw12942step3 = raw12942step2 := by apply Matrix.ext; unfold raw12942step3 raw12942step2; decide +kernel
      have hl : raw12942step2Labels = labelEmbedding9 ∘ raw12942step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12942step2 raw12942step2Labels raw12942step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5453 node5453Labels := by rfl

theorem canonical12949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12949 raw12949Labels = mixedMoment B node5166 node5166Labels := by
  calc
    mixedMoment B raw12949 raw12949Labels = mixedMoment B raw12949step0 raw12949step0Labels := by
      have ha : raw12949step0 = (fun i j => raw12949 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12949step0 raw12949; decide +kernel
      have hl : raw12949step0Labels = raw12949Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12949 raw12949Labels permutation161 permutation2
    _ = mixedMoment B node5166 node5166Labels := by rfl

theorem canonical12954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12954 raw12954Labels = mixedMoment B node5155 node5155Labels := by
  calc
    mixedMoment B raw12954 raw12954Labels = mixedMoment B raw12954step0 raw12954step0Labels := by
      have ha : raw12954step0 = (fun i j => raw12954 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12954step0 raw12954; decide +kernel
      have hl : raw12954step0Labels = raw12954Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12954 raw12954Labels permutation155 permutation2
    _ = mixedMoment B node5155 node5155Labels := by rfl

theorem canonical12959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12959 raw12959Labels = mixedMoment B node5155 node5155Labels := by
  calc
    mixedMoment B raw12959 raw12959Labels = mixedMoment B raw12959step0 raw12959step0Labels := by
      have ha : raw12959step0 = (fun i j => raw12959 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12959step0 raw12959; decide +kernel
      have hl : raw12959step0Labels = raw12959Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12959 raw12959Labels permutation153 permutation2
    _ = mixedMoment B node5155 node5155Labels := by rfl

theorem canonical12964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12964 raw12964Labels = mixedMoment B node5155 node5155Labels := by
  calc
    _ = mixedMoment B node5155 node5155Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical144
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18433 raw18433Labels = mixedMoment B node5383 node5383Labels := by
  calc
    mixedMoment B raw18433 raw18433Labels = mixedMoment B raw18433step0 raw18433step0Labels := by
      have ha : raw18433step0 = (fun i j => raw18433 (permutation289 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18433step0 raw18433; decide +kernel
      have hl : raw18433step0Labels = raw18433Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18433 raw18433Labels permutation289 permutation5
    mixedMoment B raw18433step0 raw18433step0Labels = mixedMoment B raw18433step1 raw18433step1Labels := by
      have ha : raw18433step1 = -raw18433step0 := by apply Matrix.ext; change ∀ i j, raw18433step1 i j = -(raw18433step0 i j); unfold raw18433step1 raw18433step0; decide +kernel
      have hl : raw18433step1Labels = raw18433step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18433step1 raw18433step1Labels = mixedMoment B raw18433step2 raw18433step2Labels := by
      have ha : raw18433step2 = raw18433step1 := by apply Matrix.ext; unfold raw18433step2 raw18433step1; decide +kernel
      have hl : raw18433step1Labels = labelEmbedding8 ∘ raw18433step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18433step1 raw18433step1Labels raw18433step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5383 node5383Labels := by rfl

theorem canonical18434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18434 raw18434Labels = mixedMoment B node5166 node5166Labels := by
  calc
    mixedMoment B raw18434 raw18434Labels = mixedMoment B raw18434step0 raw18434step0Labels := by
      have ha : raw18434step0 = (fun i j => raw18434 (permutation373 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18434step0 raw18434; decide +kernel
      have hl : raw18434step0Labels = raw18434Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18434 raw18434Labels permutation373 permutation4
    mixedMoment B raw18434step0 raw18434step0Labels = mixedMoment B raw18434step1 raw18434step1Labels := by
      have ha : raw18434step1 = -raw18434step0 := by apply Matrix.ext; change ∀ i j, raw18434step1 i j = -(raw18434step0 i j); unfold raw18434step1 raw18434step0; decide +kernel
      have hl : raw18434step1Labels = raw18434step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18434step1 raw18434step1Labels = mixedMoment B raw18434step2 raw18434step2Labels := by
      have ha : raw18434step2 = raw18434step1 := by apply Matrix.ext; unfold raw18434step2 raw18434step1; decide +kernel
      have hl : raw18434step1Labels = labelEmbedding7 ∘ raw18434step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18434step1 raw18434step1Labels raw18434step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5166 node5166Labels := by rfl

theorem canonical18435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18435 raw18435Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18435 raw18435Labels = mixedMoment B raw18435step0 raw18435step0Labels := by
      have hz : ∀ j, raw18435 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18435step0 = (fun i j => raw18435 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18435step0 raw18435; decide +kernel
      have hl : raw18435step0Labels = raw18435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18435 raw18435Labels permutation434 hz
    mixedMoment B raw18435step0 raw18435step0Labels = mixedMoment B raw18435step1 raw18435step1Labels := by
      have ha : raw18435step1 = (fun i j => raw18435step0 (permutation89 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18435step1 raw18435step0; decide +kernel
      have hl : raw18435step1Labels = raw18435step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18435step0 raw18435step0Labels permutation89 permutation4
    mixedMoment B raw18435step1 raw18435step1Labels = mixedMoment B raw18435step2 raw18435step2Labels := by
      have ha : raw18435step2 = -raw18435step1 := by apply Matrix.ext; change ∀ i j, raw18435step2 i j = -(raw18435step1 i j); unfold raw18435step2 raw18435step1; decide +kernel
      have hl : raw18435step2Labels = raw18435step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18435step2 raw18435step2Labels = mixedMoment B raw18435step3 raw18435step3Labels := by
      have ha : raw18435step3 = raw18435step2 := by apply Matrix.ext; unfold raw18435step3 raw18435step2; decide +kernel
      have hl : raw18435step2Labels = labelEmbedding7 ∘ raw18435step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18435step2 raw18435step2Labels raw18435step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

theorem canonical18436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18436 raw18436Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18436 raw18436Labels = mixedMoment B raw18436step0 raw18436step0Labels := by
      have hz : ∀ j, raw18436 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18436step0 = (fun i j => raw18436 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18436step0 raw18436; decide +kernel
      have hl : raw18436step0Labels = raw18436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18436 raw18436Labels permutation520 hz
    mixedMoment B raw18436step0 raw18436step0Labels = mixedMoment B raw18436step1 raw18436step1Labels := by
      have ha : raw18436step1 = (fun i j => raw18436step0 (permutation89 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18436step1 raw18436step0; decide +kernel
      have hl : raw18436step1Labels = raw18436step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18436step0 raw18436step0Labels permutation89 permutation4
    mixedMoment B raw18436step1 raw18436step1Labels = mixedMoment B raw18436step2 raw18436step2Labels := by
      have ha : raw18436step2 = -raw18436step1 := by apply Matrix.ext; change ∀ i j, raw18436step2 i j = -(raw18436step1 i j); unfold raw18436step2 raw18436step1; decide +kernel
      have hl : raw18436step2Labels = raw18436step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18436step2 raw18436step2Labels = mixedMoment B raw18436step3 raw18436step3Labels := by
      have ha : raw18436step3 = raw18436step2 := by apply Matrix.ext; unfold raw18436step3 raw18436step2; decide +kernel
      have hl : raw18436step2Labels = labelEmbedding7 ∘ raw18436step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18436step2 raw18436step2Labels raw18436step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

theorem canonical18437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18437 raw18437Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18437 raw18437Labels = mixedMoment B raw18437step0 raw18437step0Labels := by
      have hz : ∀ j, raw18437 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18437step0 = (fun i j => raw18437 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18437step0 raw18437; decide +kernel
      have hl : raw18437step0Labels = raw18437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18437 raw18437Labels permutation590 hz
    mixedMoment B raw18437step0 raw18437step0Labels = mixedMoment B raw18437step1 raw18437step1Labels := by
      have ha : raw18437step1 = (fun i j => raw18437step0 (permutation89 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18437step1 raw18437step0; decide +kernel
      have hl : raw18437step1Labels = raw18437step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18437step0 raw18437step0Labels permutation89 permutation4
    mixedMoment B raw18437step1 raw18437step1Labels = mixedMoment B raw18437step2 raw18437step2Labels := by
      have ha : raw18437step2 = -raw18437step1 := by apply Matrix.ext; change ∀ i j, raw18437step2 i j = -(raw18437step1 i j); unfold raw18437step2 raw18437step1; decide +kernel
      have hl : raw18437step2Labels = raw18437step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18437step2 raw18437step2Labels = mixedMoment B raw18437step3 raw18437step3Labels := by
      have ha : raw18437step3 = raw18437step2 := by apply Matrix.ext; unfold raw18437step3 raw18437step2; decide +kernel
      have hl : raw18437step2Labels = labelEmbedding7 ∘ raw18437step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18437step2 raw18437step2Labels raw18437step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

theorem canonical18438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18438 raw18438Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw18438 raw18438Labels = mixedMoment B raw18438step0 raw18438step0Labels := by
      have hz : ∀ j, raw18438 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw18438step0 = (fun i j => raw18438 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw18438step0 raw18438; decide +kernel
      have hl : raw18438step0Labels = raw18438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18438 raw18438Labels permutation265 hz
    _ = mixedMoment B node5301 node5301Labels := by rfl

theorem canonical18439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18439 raw18439Labels = mixedMoment B node5383 node5383Labels := by
  calc
    mixedMoment B raw18439 raw18439Labels = mixedMoment B raw18439step0 raw18439step0Labels := by
      have ha : raw18439step0 = (fun i j => raw18439 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18439step0 raw18439; decide +kernel
      have hl : raw18439step0Labels = raw18439Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18439 raw18439Labels permutation265 permutation3
    mixedMoment B raw18439step0 raw18439step0Labels = mixedMoment B raw18439step1 raw18439step1Labels := by
      have ha : raw18439step1 = raw18439step0 := by apply Matrix.ext; unfold raw18439step1 raw18439step0; decide +kernel
      have hl : raw18439step0Labels = labelEmbedding6 ∘ raw18439step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18439step0 raw18439step0Labels raw18439step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5383 node5383Labels := by rfl

theorem canonical18440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18440 raw18440Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18440 raw18440Labels = mixedMoment B raw18440step0 raw18440step0Labels := by
      have hz : ∀ j, raw18440 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18440step0 = (fun i j => raw18440 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18440step0 raw18440; decide +kernel
      have hl : raw18440step0Labels = raw18440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18440 raw18440Labels permutation434 hz
    mixedMoment B raw18440step0 raw18440step0Labels = mixedMoment B raw18440step1 raw18440step1Labels := by
      have ha : raw18440step1 = (fun i j => raw18440step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18440step1 raw18440step0; decide +kernel
      have hl : raw18440step1Labels = raw18440step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18440step0 raw18440step0Labels permutation35 permutation2
    _ = mixedMoment B node5439 node5439Labels := by rfl

theorem canonical18441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18441 raw18441Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18441 raw18441Labels = mixedMoment B raw18441step0 raw18441step0Labels := by
      have hz : ∀ j, raw18441 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18441step0 = (fun i j => raw18441 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18441step0 raw18441; decide +kernel
      have hl : raw18441step0Labels = raw18441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18441 raw18441Labels permutation520 hz
    mixedMoment B raw18441step0 raw18441step0Labels = mixedMoment B raw18441step1 raw18441step1Labels := by
      have ha : raw18441step1 = (fun i j => raw18441step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18441step1 raw18441step0; decide +kernel
      have hl : raw18441step1Labels = raw18441step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18441step0 raw18441step0Labels permutation35 permutation2
    _ = mixedMoment B node5439 node5439Labels := by rfl

theorem canonical18442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18442 raw18442Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18442 raw18442Labels = mixedMoment B raw18442step0 raw18442step0Labels := by
      have hz : ∀ j, raw18442 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18442step0 = (fun i j => raw18442 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18442step0 raw18442; decide +kernel
      have hl : raw18442step0Labels = raw18442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18442 raw18442Labels permutation590 hz
    mixedMoment B raw18442step0 raw18442step0Labels = mixedMoment B raw18442step1 raw18442step1Labels := by
      have ha : raw18442step1 = (fun i j => raw18442step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18442step1 raw18442step0; decide +kernel
      have hl : raw18442step1Labels = raw18442step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18442step0 raw18442step0Labels permutation35 permutation2
    _ = mixedMoment B node5439 node5439Labels := by rfl

theorem canonical18443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18443 raw18443Labels = mixedMoment B node5374 node5374Labels := by
  calc
    mixedMoment B raw18443 raw18443Labels = mixedMoment B raw18443step0 raw18443step0Labels := by
      have ha : raw18443step0 = (fun i j => raw18443 (permutation268 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18443step0 raw18443; decide +kernel
      have hl : raw18443step0Labels = raw18443Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18443 raw18443Labels permutation268 permutation3
    mixedMoment B raw18443step0 raw18443step0Labels = mixedMoment B raw18443step1 raw18443step1Labels := by
      have ha : raw18443step1 = raw18443step0 := by apply Matrix.ext; unfold raw18443step1 raw18443step0; decide +kernel
      have hl : raw18443step0Labels = labelEmbedding6 ∘ raw18443step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18443step0 raw18443step0Labels raw18443step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5374 node5374Labels := by rfl

theorem canonical18444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18444 raw18444Labels = mixedMoment B node5155 node5155Labels := by
  calc
    mixedMoment B raw18444 raw18444Labels = mixedMoment B raw18444step0 raw18444step0Labels := by
      have ha : raw18444step0 = (fun i j => raw18444 (permutation369 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18444step0 raw18444; decide +kernel
      have hl : raw18444step0Labels = raw18444Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18444 raw18444Labels permutation369 permutation4
    mixedMoment B raw18444step0 raw18444step0Labels = mixedMoment B raw18444step1 raw18444step1Labels := by
      have ha : raw18444step1 = -raw18444step0 := by apply Matrix.ext; change ∀ i j, raw18444step1 i j = -(raw18444step0 i j); unfold raw18444step1 raw18444step0; decide +kernel
      have hl : raw18444step1Labels = raw18444step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18444step1 raw18444step1Labels = mixedMoment B raw18444step2 raw18444step2Labels := by
      have ha : raw18444step2 = raw18444step1 := by apply Matrix.ext; unfold raw18444step2 raw18444step1; decide +kernel
      have hl : raw18444step1Labels = labelEmbedding7 ∘ raw18444step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18444step1 raw18444step1Labels raw18444step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5155 node5155Labels := by rfl

theorem canonical18445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18445 raw18445Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw18445 raw18445Labels = mixedMoment B raw18445step0 raw18445step0Labels := by
      have hz : ∀ j, raw18445 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18445step0 = (fun i j => raw18445 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18445step0 raw18445; decide +kernel
      have hl : raw18445step0Labels = raw18445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18445 raw18445Labels permutation520 hz
    mixedMoment B raw18445step0 raw18445step0Labels = mixedMoment B raw18445step1 raw18445step1Labels := by
      have ha : raw18445step1 = (fun i j => raw18445step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18445step1 raw18445step0; decide +kernel
      have hl : raw18445step1Labels = raw18445step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18445step0 raw18445step0Labels permutation127 permutation3
    mixedMoment B raw18445step1 raw18445step1Labels = mixedMoment B raw18445step2 raw18445step2Labels := by
      have ha : raw18445step2 = -raw18445step1 := by apply Matrix.ext; change ∀ i j, raw18445step2 i j = -(raw18445step1 i j); unfold raw18445step2 raw18445step1; decide +kernel
      have hl : raw18445step2Labels = raw18445step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18445step2 raw18445step2Labels = mixedMoment B raw18445step3 raw18445step3Labels := by
      have ha : raw18445step3 = raw18445step2 := by apply Matrix.ext; unfold raw18445step3 raw18445step2; decide +kernel
      have hl : raw18445step2Labels = labelEmbedding6 ∘ raw18445step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18445step2 raw18445step2Labels raw18445step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

theorem canonical18446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18446 raw18446Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw18446 raw18446Labels = mixedMoment B raw18446step0 raw18446step0Labels := by
      have hz : ∀ j, raw18446 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18446step0 = (fun i j => raw18446 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18446step0 raw18446; decide +kernel
      have hl : raw18446step0Labels = raw18446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18446 raw18446Labels permutation590 hz
    mixedMoment B raw18446step0 raw18446step0Labels = mixedMoment B raw18446step1 raw18446step1Labels := by
      have ha : raw18446step1 = (fun i j => raw18446step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18446step1 raw18446step0; decide +kernel
      have hl : raw18446step1Labels = raw18446step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18446step0 raw18446step0Labels permutation127 permutation3
    mixedMoment B raw18446step1 raw18446step1Labels = mixedMoment B raw18446step2 raw18446step2Labels := by
      have ha : raw18446step2 = -raw18446step1 := by apply Matrix.ext; change ∀ i j, raw18446step2 i j = -(raw18446step1 i j); unfold raw18446step2 raw18446step1; decide +kernel
      have hl : raw18446step2Labels = raw18446step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18446step2 raw18446step2Labels = mixedMoment B raw18446step3 raw18446step3Labels := by
      have ha : raw18446step3 = raw18446step2 := by apply Matrix.ext; unfold raw18446step3 raw18446step2; decide +kernel
      have hl : raw18446step2Labels = labelEmbedding6 ∘ raw18446step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18446step2 raw18446step2Labels raw18446step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

theorem canonical18447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18447 raw18447Labels = mixedMoment B node5374 node5374Labels := by
  calc
    mixedMoment B raw18447 raw18447Labels = mixedMoment B raw18447step0 raw18447step0Labels := by
      have ha : raw18447step0 = (fun i j => raw18447 (permutation266 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18447step0 raw18447; decide +kernel
      have hl : raw18447step0Labels = raw18447Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18447 raw18447Labels permutation266 permutation3
    mixedMoment B raw18447step0 raw18447step0Labels = mixedMoment B raw18447step1 raw18447step1Labels := by
      have ha : raw18447step1 = raw18447step0 := by apply Matrix.ext; unfold raw18447step1 raw18447step0; decide +kernel
      have hl : raw18447step0Labels = labelEmbedding6 ∘ raw18447step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18447step0 raw18447step0Labels raw18447step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5374 node5374Labels := by rfl

theorem canonical18448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18448 raw18448Labels = mixedMoment B node5155 node5155Labels := by
  calc
    mixedMoment B raw18448 raw18448Labels = mixedMoment B raw18448step0 raw18448step0Labels := by
      have ha : raw18448step0 = (fun i j => raw18448 (permutation368 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18448step0 raw18448; decide +kernel
      have hl : raw18448step0Labels = raw18448Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18448 raw18448Labels permutation368 permutation4
    mixedMoment B raw18448step0 raw18448step0Labels = mixedMoment B raw18448step1 raw18448step1Labels := by
      have ha : raw18448step1 = -raw18448step0 := by apply Matrix.ext; change ∀ i j, raw18448step1 i j = -(raw18448step0 i j); unfold raw18448step1 raw18448step0; decide +kernel
      have hl : raw18448step1Labels = raw18448step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18448step1 raw18448step1Labels = mixedMoment B raw18448step2 raw18448step2Labels := by
      have ha : raw18448step2 = raw18448step1 := by apply Matrix.ext; unfold raw18448step2 raw18448step1; decide +kernel
      have hl : raw18448step1Labels = labelEmbedding7 ∘ raw18448step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18448step1 raw18448step1Labels raw18448step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5155 node5155Labels := by rfl

theorem canonical18449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18449 raw18449Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw18449 raw18449Labels = mixedMoment B raw18449step0 raw18449step0Labels := by
      have hz : ∀ j, raw18449 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18449step0 = (fun i j => raw18449 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18449step0 raw18449; decide +kernel
      have hl : raw18449step0Labels = raw18449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18449 raw18449Labels permutation434 hz
    mixedMoment B raw18449step0 raw18449step0Labels = mixedMoment B raw18449step1 raw18449step1Labels := by
      have ha : raw18449step1 = (fun i j => raw18449step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18449step1 raw18449step0; decide +kernel
      have hl : raw18449step1Labels = raw18449step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18449step0 raw18449step0Labels permutation127 permutation3
    mixedMoment B raw18449step1 raw18449step1Labels = mixedMoment B raw18449step2 raw18449step2Labels := by
      have ha : raw18449step2 = -raw18449step1 := by apply Matrix.ext; change ∀ i j, raw18449step2 i j = -(raw18449step1 i j); unfold raw18449step2 raw18449step1; decide +kernel
      have hl : raw18449step2Labels = raw18449step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18449step2 raw18449step2Labels = mixedMoment B raw18449step3 raw18449step3Labels := by
      have ha : raw18449step3 = raw18449step2 := by apply Matrix.ext; unfold raw18449step3 raw18449step2; decide +kernel
      have hl : raw18449step2Labels = labelEmbedding6 ∘ raw18449step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18449step2 raw18449step2Labels raw18449step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

theorem canonical18450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18450 raw18450Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw18450 raw18450Labels = mixedMoment B raw18450step0 raw18450step0Labels := by
      have hz : ∀ j, raw18450 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18450step0 = (fun i j => raw18450 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18450step0 raw18450; decide +kernel
      have hl : raw18450step0Labels = raw18450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18450 raw18450Labels permutation590 hz
    mixedMoment B raw18450step0 raw18450step0Labels = mixedMoment B raw18450step1 raw18450step1Labels := by
      have ha : raw18450step1 = (fun i j => raw18450step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18450step1 raw18450step0; decide +kernel
      have hl : raw18450step1Labels = raw18450step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18450step0 raw18450step0Labels permutation151 permutation3
    mixedMoment B raw18450step1 raw18450step1Labels = mixedMoment B raw18450step2 raw18450step2Labels := by
      have ha : raw18450step2 = -raw18450step1 := by apply Matrix.ext; change ∀ i j, raw18450step2 i j = -(raw18450step1 i j); unfold raw18450step2 raw18450step1; decide +kernel
      have hl : raw18450step2Labels = raw18450step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18450step2 raw18450step2Labels = mixedMoment B raw18450step3 raw18450step3Labels := by
      have ha : raw18450step3 = raw18450step2 := by apply Matrix.ext; unfold raw18450step3 raw18450step2; decide +kernel
      have hl : raw18450step2Labels = labelEmbedding6 ∘ raw18450step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18450step2 raw18450step2Labels raw18450step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

theorem canonical18451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18451 raw18451Labels = mixedMoment B node5374 node5374Labels := by
  calc
    mixedMoment B raw18451 raw18451Labels = mixedMoment B raw18451step0 raw18451step0Labels := by
      have ha : raw18451step0 = (fun i j => raw18451 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18451step0 raw18451; decide +kernel
      have hl : raw18451step0Labels = raw18451Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18451 raw18451Labels permutation265 permutation3
    mixedMoment B raw18451step0 raw18451step0Labels = mixedMoment B raw18451step1 raw18451step1Labels := by
      have ha : raw18451step1 = raw18451step0 := by apply Matrix.ext; unfold raw18451step1 raw18451step0; decide +kernel
      have hl : raw18451step0Labels = labelEmbedding6 ∘ raw18451step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18451step0 raw18451step0Labels raw18451step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5374 node5374Labels := by rfl

theorem canonical18452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18452 raw18452Labels = mixedMoment B node5155 node5155Labels := by
  calc
    mixedMoment B raw18452 raw18452Labels = mixedMoment B raw18452step0 raw18452step0Labels := by
      have ha : raw18452step0 = (fun i j => raw18452 (permutation367 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18452step0 raw18452; decide +kernel
      have hl : raw18452step0Labels = raw18452Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18452 raw18452Labels permutation367 permutation4
    mixedMoment B raw18452step0 raw18452step0Labels = mixedMoment B raw18452step1 raw18452step1Labels := by
      have ha : raw18452step1 = -raw18452step0 := by apply Matrix.ext; change ∀ i j, raw18452step1 i j = -(raw18452step0 i j); unfold raw18452step1 raw18452step0; decide +kernel
      have hl : raw18452step1Labels = raw18452step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18452step1 raw18452step1Labels = mixedMoment B raw18452step2 raw18452step2Labels := by
      have ha : raw18452step2 = raw18452step1 := by apply Matrix.ext; unfold raw18452step2 raw18452step1; decide +kernel
      have hl : raw18452step1Labels = labelEmbedding7 ∘ raw18452step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18452step1 raw18452step1Labels raw18452step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5155 node5155Labels := by rfl

theorem canonical18453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18453 raw18453Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw18453 raw18453Labels = mixedMoment B raw18453step0 raw18453step0Labels := by
      have hz : ∀ j, raw18453 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18453step0 = (fun i j => raw18453 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18453step0 raw18453; decide +kernel
      have hl : raw18453step0Labels = raw18453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18453 raw18453Labels permutation434 hz
    mixedMoment B raw18453step0 raw18453step0Labels = mixedMoment B raw18453step1 raw18453step1Labels := by
      have ha : raw18453step1 = (fun i j => raw18453step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18453step1 raw18453step0; decide +kernel
      have hl : raw18453step1Labels = raw18453step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18453step0 raw18453step0Labels permutation151 permutation3
    mixedMoment B raw18453step1 raw18453step1Labels = mixedMoment B raw18453step2 raw18453step2Labels := by
      have ha : raw18453step2 = -raw18453step1 := by apply Matrix.ext; change ∀ i j, raw18453step2 i j = -(raw18453step1 i j); unfold raw18453step2 raw18453step1; decide +kernel
      have hl : raw18453step2Labels = raw18453step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18453step2 raw18453step2Labels = mixedMoment B raw18453step3 raw18453step3Labels := by
      have ha : raw18453step3 = raw18453step2 := by apply Matrix.ext; unfold raw18453step3 raw18453step2; decide +kernel
      have hl : raw18453step2Labels = labelEmbedding6 ∘ raw18453step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18453step2 raw18453step2Labels raw18453step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

theorem canonical18454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18454 raw18454Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw18454 raw18454Labels = mixedMoment B raw18454step0 raw18454step0Labels := by
      have hz : ∀ j, raw18454 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18454step0 = (fun i j => raw18454 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18454step0 raw18454; decide +kernel
      have hl : raw18454step0Labels = raw18454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18454 raw18454Labels permutation520 hz
    mixedMoment B raw18454step0 raw18454step0Labels = mixedMoment B raw18454step1 raw18454step1Labels := by
      have ha : raw18454step1 = (fun i j => raw18454step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18454step1 raw18454step0; decide +kernel
      have hl : raw18454step1Labels = raw18454step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18454step0 raw18454step0Labels permutation151 permutation3
    mixedMoment B raw18454step1 raw18454step1Labels = mixedMoment B raw18454step2 raw18454step2Labels := by
      have ha : raw18454step2 = -raw18454step1 := by apply Matrix.ext; change ∀ i j, raw18454step2 i j = -(raw18454step1 i j); unfold raw18454step2 raw18454step1; decide +kernel
      have hl : raw18454step2Labels = raw18454step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18454step2 raw18454step2Labels = mixedMoment B raw18454step3 raw18454step3Labels := by
      have ha : raw18454step3 = raw18454step2 := by apply Matrix.ext; unfold raw18454step3 raw18454step2; decide +kernel
      have hl : raw18454step2Labels = labelEmbedding6 ∘ raw18454step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18454step2 raw18454step2Labels raw18454step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

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

theorem canonical2181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2181 raw2181Labels = mixedMoment B node5155 node5155Labels := by
  calc
    mixedMoment B raw2181 raw2181Labels = mixedMoment B raw2181step0 raw2181step0Labels := by
      have ha : raw2181step0 = (fun i j => raw2181 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2181step0 raw2181; decide +kernel
      have hl : raw2181step0Labels = raw2181Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2181 raw2181Labels permutation152 permutation5
    mixedMoment B raw2181step0 raw2181step0Labels = mixedMoment B raw2181step1 raw2181step1Labels := by
      have ha : raw2181step1 = raw2181step0 := by apply Matrix.ext; unfold raw2181step1 raw2181step0; decide +kernel
      have hl : raw2181step0Labels = labelEmbedding8 ∘ raw2181step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2181step0 raw2181step0Labels raw2181step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5155 node5155Labels := by rfl

theorem canonical2182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2182 raw2182Labels = mixedMoment B node2908 node2908Labels := by
  calc
    mixedMoment B raw2182 raw2182Labels = mixedMoment B raw2182step0 raw2182step0Labels := by
      have ha : raw2182step0 = (fun i j => raw2182 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2182step0 raw2182; decide +kernel
      have hl : raw2182step0Labels = raw2182Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2182 raw2182Labels permutation152 permutation4
    _ = mixedMoment B node2908 node2908Labels := by rfl

theorem canonical2183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2183 raw2183Labels = mixedMoment B node3600 node3600Labels := by
  calc
    mixedMoment B raw2183 raw2183Labels = mixedMoment B raw2183step0 raw2183step0Labels := by
      have ha : raw2183step0 = (fun i j => raw2183 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2183step0 raw2183; decide +kernel
      have hl : raw2183step0Labels = raw2183Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2183 raw2183Labels permutation161 permutation3
    mixedMoment B raw2183step0 raw2183step0Labels = mixedMoment B raw2183step1 raw2183step1Labels := by
      have ha : raw2183step1 = -raw2183step0 := by apply Matrix.ext; change ∀ i j, raw2183step1 i j = -(raw2183step0 i j); unfold raw2183step1 raw2183step0; decide +kernel
      have hl : raw2183step1Labels = raw2183step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2183step1 raw2183step1Labels = mixedMoment B raw2183step2 raw2183step2Labels := by
      have ha : raw2183step2 = raw2183step1 := by apply Matrix.ext; unfold raw2183step2 raw2183step1; decide +kernel
      have hl : raw2183step1Labels = labelEmbedding1 ∘ raw2183step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2183step1 raw2183step1Labels raw2183step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3600 node3600Labels := by rfl

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

theorem canonical2310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2310 raw2310Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw2310 raw2310Labels = mixedMoment B raw2310step0 raw2310step0Labels := by
      have ha : raw2310step0 = (fun i j => raw2310 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2310step0 raw2310; decide +kernel
      have hl : raw2310step0Labels = raw2310Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2310 raw2310Labels permutation32 permutation5
    mixedMoment B raw2310step0 raw2310step0Labels = mixedMoment B raw2310step1 raw2310step1Labels := by
      have ha : raw2310step1 = raw2310step0 := by apply Matrix.ext; unfold raw2310step1 raw2310step0; decide +kernel
      have hl : raw2310step0Labels = labelEmbedding8 ∘ raw2310step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2310step0 raw2310step0Labels raw2310step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

theorem canonical2311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2311 raw2311Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw2311 raw2311Labels = mixedMoment B raw2311step0 raw2311step0Labels := by
      have ha : raw2311step0 = (fun i j => raw2311 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2311step0 raw2311; decide +kernel
      have hl : raw2311step0Labels = raw2311Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2311 raw2311Labels permutation32 permutation4
    _ = mixedMoment B node3053 node3053Labels := by rfl

theorem canonical2312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2312 raw2312Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw2312 raw2312Labels = mixedMoment B raw2312step0 raw2312step0Labels := by
      have ha : raw2312step0 = (fun i j => raw2312 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2312step0 raw2312; decide +kernel
      have hl : raw2312step0Labels = raw2312Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2312 raw2312Labels permutation41 permutation3
    mixedMoment B raw2312step0 raw2312step0Labels = mixedMoment B raw2312step1 raw2312step1Labels := by
      have ha : raw2312step1 = -raw2312step0 := by apply Matrix.ext; change ∀ i j, raw2312step1 i j = -(raw2312step0 i j); unfold raw2312step1 raw2312step0; decide +kernel
      have hl : raw2312step1Labels = raw2312step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2312step1 raw2312step1Labels = mixedMoment B raw2312step2 raw2312step2Labels := by
      have ha : raw2312step2 = raw2312step1 := by apply Matrix.ext; unfold raw2312step2 raw2312step1; decide +kernel
      have hl : raw2312step1Labels = labelEmbedding1 ∘ raw2312step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2312step1 raw2312step1Labels raw2312step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3619 node3619Labels := by rfl

theorem canonical2427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2427 raw2427Labels = mixedMoment B node5374 node5374Labels := by
  calc
    mixedMoment B raw2427 raw2427Labels = mixedMoment B raw2427step0 raw2427step0Labels := by
      have ha : raw2427step0 = (fun i j => raw2427 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2427step0 raw2427; decide +kernel
      have hl : raw2427step0Labels = raw2427Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2427 raw2427Labels permutation152 permutation4
    mixedMoment B raw2427step0 raw2427step0Labels = mixedMoment B raw2427step1 raw2427step1Labels := by
      have ha : raw2427step1 = raw2427step0 := by apply Matrix.ext; unfold raw2427step1 raw2427step0; decide +kernel
      have hl : raw2427step0Labels = labelEmbedding7 ∘ raw2427step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2427step0 raw2427step0Labels raw2427step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5374 node5374Labels := by rfl

theorem canonical2428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2428 raw2428Labels = mixedMoment B node3713 node3713Labels := by
  calc
    mixedMoment B raw2428 raw2428Labels = mixedMoment B raw2428step0 raw2428step0Labels := by
      have ha : raw2428step0 = (fun i j => raw2428 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2428step0 raw2428; decide +kernel
      have hl : raw2428step0Labels = raw2428Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2428 raw2428Labels permutation152 permutation4
    _ = mixedMoment B node3713 node3713Labels := by rfl

theorem canonical2429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2429 raw2429Labels = mixedMoment B node3713 node3713Labels := by
  calc
    mixedMoment B raw2429 raw2429Labels = mixedMoment B raw2429step0 raw2429step0Labels := by
      have ha : raw2429step0 = (fun i j => raw2429 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2429step0 raw2429; decide +kernel
      have hl : raw2429step0Labels = raw2429Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2429 raw2429Labels permutation176 permutation6
    mixedMoment B raw2429step0 raw2429step0Labels = mixedMoment B raw2429step1 raw2429step1Labels := by
      have ha : raw2429step1 = -raw2429step0 := by apply Matrix.ext; change ∀ i j, raw2429step1 i j = -(raw2429step0 i j); unfold raw2429step1 raw2429step0; decide +kernel
      have hl : raw2429step1Labels = raw2429step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2429step1 raw2429step1Labels = mixedMoment B raw2429step2 raw2429step2Labels := by
      have ha : raw2429step2 = raw2429step1 := by apply Matrix.ext; unfold raw2429step2 raw2429step1; decide +kernel
      have hl : raw2429step1Labels = labelEmbedding1 ∘ raw2429step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2429step1 raw2429step1Labels raw2429step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3713 node3713Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical2436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2436 raw2436Labels = mixedMoment B node5383 node5383Labels := by
  calc
    mixedMoment B raw2436 raw2436Labels = mixedMoment B raw2436step0 raw2436step0Labels := by
      have ha : raw2436step0 = (fun i j => raw2436 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2436step0 raw2436; decide +kernel
      have hl : raw2436step0Labels = raw2436Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2436 raw2436Labels permutation152 permutation4
    mixedMoment B raw2436step0 raw2436step0Labels = mixedMoment B raw2436step1 raw2436step1Labels := by
      have ha : raw2436step1 = raw2436step0 := by apply Matrix.ext; unfold raw2436step1 raw2436step0; decide +kernel
      have hl : raw2436step0Labels = labelEmbedding7 ∘ raw2436step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2436step0 raw2436step0Labels raw2436step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5383 node5383Labels := by rfl

theorem canonical2437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2437 raw2437Labels = mixedMoment B node3731 node3731Labels := by
  calc
    mixedMoment B raw2437 raw2437Labels = mixedMoment B raw2437step0 raw2437step0Labels := by
      have ha : raw2437step0 = (fun i j => raw2437 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2437step0 raw2437; decide +kernel
      have hl : raw2437step0Labels = raw2437Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2437 raw2437Labels permutation152 permutation4
    _ = mixedMoment B node3731 node3731Labels := by rfl

theorem canonical2438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2438 raw2438Labels = mixedMoment B node3867 node3867Labels := by
  calc
    mixedMoment B raw2438 raw2438Labels = mixedMoment B raw2438step0 raw2438step0Labels := by
      have ha : raw2438step0 = (fun i j => raw2438 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2438step0 raw2438; decide +kernel
      have hl : raw2438step0Labels = raw2438Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2438 raw2438Labels permutation176 permutation6
    mixedMoment B raw2438step0 raw2438step0Labels = mixedMoment B raw2438step1 raw2438step1Labels := by
      have ha : raw2438step1 = -raw2438step0 := by apply Matrix.ext; change ∀ i j, raw2438step1 i j = -(raw2438step0 i j); unfold raw2438step1 raw2438step0; decide +kernel
      have hl : raw2438step1Labels = raw2438step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2438step1 raw2438step1Labels = mixedMoment B raw2438step2 raw2438step2Labels := by
      have ha : raw2438step2 = raw2438step1 := by apply Matrix.ext; unfold raw2438step2 raw2438step1; decide +kernel
      have hl : raw2438step1Labels = labelEmbedding1 ∘ raw2438step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2438step1 raw2438step1Labels raw2438step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3867 node3867Labels := by rfl

theorem canonical2493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2493 raw2493Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw2493 raw2493Labels = mixedMoment B raw2493step0 raw2493step0Labels := by
      have ha : raw2493step0 = (fun i j => raw2493 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2493step0 raw2493; decide +kernel
      have hl : raw2493step0Labels = raw2493Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2493 raw2493Labels permutation32 permutation4
    mixedMoment B raw2493step0 raw2493step0Labels = mixedMoment B raw2493step1 raw2493step1Labels := by
      have ha : raw2493step1 = raw2493step0 := by apply Matrix.ext; unfold raw2493step1 raw2493step0; decide +kernel
      have hl : raw2493step0Labels = labelEmbedding7 ∘ raw2493step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2493step0 raw2493step0Labels raw2493step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

theorem canonical2494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2494 raw2494Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw2494 raw2494Labels = mixedMoment B raw2494step0 raw2494step0Labels := by
      have ha : raw2494step0 = (fun i j => raw2494 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2494step0 raw2494; decide +kernel
      have hl : raw2494step0Labels = raw2494Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2494 raw2494Labels permutation32 permutation4
    _ = mixedMoment B node3814 node3814Labels := by rfl

theorem canonical2495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2495 raw2495Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw2495 raw2495Labels = mixedMoment B raw2495step0 raw2495step0Labels := by
      have ha : raw2495step0 = (fun i j => raw2495 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2495step0 raw2495; decide +kernel
      have hl : raw2495step0Labels = raw2495Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2495 raw2495Labels permutation37 permutation6
    mixedMoment B raw2495step0 raw2495step0Labels = mixedMoment B raw2495step1 raw2495step1Labels := by
      have ha : raw2495step1 = -raw2495step0 := by apply Matrix.ext; change ∀ i j, raw2495step1 i j = -(raw2495step0 i j); unfold raw2495step1 raw2495step0; decide +kernel
      have hl : raw2495step1Labels = raw2495step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2495step1 raw2495step1Labels = mixedMoment B raw2495step2 raw2495step2Labels := by
      have ha : raw2495step2 = raw2495step1 := by apply Matrix.ext; unfold raw2495step2 raw2495step1; decide +kernel
      have hl : raw2495step1Labels = labelEmbedding1 ∘ raw2495step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2495step1 raw2495step1Labels raw2495step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3814 node3814Labels := by rfl

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

theorem canonical2565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2565 raw2565Labels = mixedMoment B node5453 node5453Labels := by
  calc
    _ = mixedMoment B node5453 node5453Labels := by rfl

theorem canonical2566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2566 raw2566Labels = mixedMoment B node3912 node3912Labels := by
  calc
    _ = mixedMoment B node3912 node3912Labels := by rfl

theorem canonical2567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2567 raw2567Labels = mixedMoment B node3912 node3912Labels := by
  calc
    mixedMoment B raw2567 raw2567Labels = mixedMoment B raw2567step0 raw2567step0Labels := by
      have ha : raw2567step0 = (fun i j => raw2567 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2567step0 raw2567; decide +kernel
      have hl : raw2567step0Labels = raw2567Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2567 raw2567Labels permutation29 permutation3
    mixedMoment B raw2567step0 raw2567step0Labels = mixedMoment B raw2567step1 raw2567step1Labels := by
      have ha : raw2567step1 = -raw2567step0 := by apply Matrix.ext; change ∀ i j, raw2567step1 i j = -(raw2567step0 i j); unfold raw2567step1 raw2567step0; decide +kernel
      have hl : raw2567step1Labels = raw2567step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2567step1 raw2567step1Labels = mixedMoment B raw2567step2 raw2567step2Labels := by
      have ha : raw2567step2 = raw2567step1 := by apply Matrix.ext; unfold raw2567step2 raw2567step1; decide +kernel
      have hl : raw2567step1Labels = labelEmbedding1 ∘ raw2567step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2567step1 raw2567step1Labels raw2567step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3912 node3912Labels := by rfl

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

theorem canonical550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw550 raw550Labels = mixedMoment B node3912 node3912Labels := by
  calc
    mixedMoment B raw550 raw550Labels = mixedMoment B raw550step0 raw550step0Labels := by
      have ha : raw550step0 = (fun i j => raw550 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw550step0 raw550; decide +kernel
      have hl : raw550step0Labels = raw550Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw550 raw550Labels permutation8 permutation5
    mixedMoment B raw550step0 raw550step0Labels = mixedMoment B raw550step1 raw550step1Labels := by
      have ha : raw550step1 = raw550step0 := by apply Matrix.ext; unfold raw550step1 raw550step0; decide +kernel
      have hl : raw550step0Labels = labelEmbedding1 ∘ raw550step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw550step0 raw550step0Labels raw550step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3912 node3912Labels := by rfl

theorem canonical551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw551 raw551Labels = mixedMoment B node505 node505Labels := by
  calc
    mixedMoment B raw551 raw551Labels = mixedMoment B raw551step0 raw551step0Labels := by
      have ha : raw551step0 = (fun i j => raw551 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw551step0 raw551; decide +kernel
      have hl : raw551step0Labels = raw551Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw551 raw551Labels permutation29 permutation4
    mixedMoment B raw551step0 raw551step0Labels = mixedMoment B raw551step1 raw551step1Labels := by
      have ha : raw551step1 = -raw551step0 := by apply Matrix.ext; change ∀ i j, raw551step1 i j = -(raw551step0 i j); unfold raw551step1 raw551step0; decide +kernel
      have hl : raw551step1Labels = raw551step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node505 node505Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4117 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4117 = injectiveMoment H node207 := by
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

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SinglePriority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair505 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node505 node505Labels = Sparse.eval singlePairValue505 (familyPairVector B) := by
  have hp := single_label_three B hB node505
  have hl : node505Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node505 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node505 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node505 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node505 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node505 (EqualityPatterns.family3.label 1) = PairSemantics.raw5204 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node505 PairSemantics.raw5204; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5204 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node505 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node505 (EqualityPatterns.family3.label 2) = PairSemantics.raw9013 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node505 PairSemantics.raw9013; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9013 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node505 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node505 (EqualityPatterns.family3.label 3) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node505 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm4 : familyPairMoment B (groupedColumns node505 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value207 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node505 (EqualityPatterns.family3.label 4) = PairSemantics.raw4117 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node505 PairSemantics.raw4117; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4117 hH).trans (PairSemantics.sound207 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue505, PairSemantics.value0, PairSemantics.value4, PairSemantics.value11, PairSemantics.value207, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3912 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3912 node3912Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node505 node505Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw550 singletonSmall3912
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3912) = raw550Labels := by decide +kernel
  rw [hl, canonical550 B hB] at h
  have hc0 : mixedMoment B raw550 (Fin.cases (0 : Fin 1) singletonSmall3912) =
      mixedMoment B node505 node505Labels := by
    have ha : raw550 = raw551 := by apply Matrix.ext; unfold raw550 raw551; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3912 = raw551Labels := by decide +kernel
    rw [ha, hj, canonical551 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
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

theorem singleton5155 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5155 node5155Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2908 node2908Labels + mixedMoment B node3600 node3600Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2181 singletonSmall5155
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5155) = raw2181Labels := by decide +kernel
  rw [hl, canonical2181 B hB] at h
  have hc0 : mixedMoment B raw2181 (Fin.cases (0 : Fin 2) singletonSmall5155) =
      mixedMoment B node2908 node2908Labels := by
    have ha : raw2181 = raw2182 := by apply Matrix.ext; unfold raw2181 raw2182; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5155 = raw2182Labels := by decide +kernel
    rw [ha, hj, canonical2182 B hB]
  have hc1 : mixedMoment B raw2181 (Fin.cases (1 : Fin 2) singletonSmall5155) =
      mixedMoment B node3600 node3600Labels := by
    have ha : raw2181 = raw2183 := by apply Matrix.ext; unfold raw2181 raw2183; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5155 = raw2183Labels := by decide +kernel
    rw [ha, hj, canonical2183 B hB]
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

theorem singleton5301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5301 node5301Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3053 node3053Labels + mixedMoment B node3619 node3619Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2310 singletonSmall5301
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5301) = raw2310Labels := by decide +kernel
  rw [hl, canonical2310 B hB] at h
  have hc0 : mixedMoment B raw2310 (Fin.cases (0 : Fin 2) singletonSmall5301) =
      mixedMoment B node3053 node3053Labels := by
    have ha : raw2310 = raw2311 := by apply Matrix.ext; unfold raw2310 raw2311; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5301 = raw2311Labels := by decide +kernel
    rw [ha, hj, canonical2311 B hB]
  have hc1 : mixedMoment B raw2310 (Fin.cases (1 : Fin 2) singletonSmall5301) =
      mixedMoment B node3619 node3619Labels := by
    have ha : raw2310 = raw2312 := by apply Matrix.ext; unfold raw2310 raw2312; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5301 = raw2312Labels := by decide +kernel
    rw [ha, hj, canonical2312 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5374 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5374 node5374Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3713 node3713Labels + mixedMoment B node3713 node3713Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2427 singletonSmall5374
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5374) = raw2427Labels := by decide +kernel
  rw [hl, canonical2427 B hB] at h
  have hc0 : mixedMoment B raw2427 (Fin.cases (0 : Fin 2) singletonSmall5374) =
      mixedMoment B node3713 node3713Labels := by
    have ha : raw2427 = raw2428 := by apply Matrix.ext; unfold raw2427 raw2428; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5374 = raw2428Labels := by decide +kernel
    rw [ha, hj, canonical2428 B hB]
  have hc1 : mixedMoment B raw2427 (Fin.cases (1 : Fin 2) singletonSmall5374) =
      mixedMoment B node3713 node3713Labels := by
    have ha : raw2427 = raw2429 := by apply Matrix.ext; unfold raw2427 raw2429; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5374 = raw2429Labels := by decide +kernel
    rw [ha, hj, canonical2429 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
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

theorem singleton5383 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5383 node5383Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3731 node3731Labels + mixedMoment B node3867 node3867Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2436 singletonSmall5383
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5383) = raw2436Labels := by decide +kernel
  rw [hl, canonical2436 B hB] at h
  have hc0 : mixedMoment B raw2436 (Fin.cases (0 : Fin 2) singletonSmall5383) =
      mixedMoment B node3731 node3731Labels := by
    have ha : raw2436 = raw2437 := by apply Matrix.ext; unfold raw2436 raw2437; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5383 = raw2437Labels := by decide +kernel
    rw [ha, hj, canonical2437 B hB]
  have hc1 : mixedMoment B raw2436 (Fin.cases (1 : Fin 2) singletonSmall5383) =
      mixedMoment B node3867 node3867Labels := by
    have ha : raw2436 = raw2438 := by apply Matrix.ext; unfold raw2436 raw2438; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5383 = raw2438Labels := by decide +kernel
    rw [ha, hj, canonical2438 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5412 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5412 node5412Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3814 node3814Labels + mixedMoment B node3814 node3814Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2493 singletonSmall5412
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5412) = raw2493Labels := by decide +kernel
  rw [hl, canonical2493 B hB] at h
  have hc0 : mixedMoment B raw2493 (Fin.cases (0 : Fin 2) singletonSmall5412) =
      mixedMoment B node3814 node3814Labels := by
    have ha : raw2493 = raw2494 := by apply Matrix.ext; unfold raw2493 raw2494; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5412 = raw2494Labels := by decide +kernel
    rw [ha, hj, canonical2494 B hB]
  have hc1 : mixedMoment B raw2493 (Fin.cases (1 : Fin 2) singletonSmall5412) =
      mixedMoment B node3814 node3814Labels := by
    have ha : raw2493 = raw2495 := by apply Matrix.ext; unfold raw2493 raw2495; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5412 = raw2495Labels := by decide +kernel
    rw [ha, hj, canonical2495 B hB]
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

theorem singleton5453 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5453 node5453Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3912 node3912Labels + mixedMoment B node3912 node3912Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2565 singletonSmall5453
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5453) = raw2565Labels := by decide +kernel
  rw [hl, canonical2565 B hB] at h
  have hc0 : mixedMoment B raw2565 (Fin.cases (0 : Fin 2) singletonSmall5453) =
      mixedMoment B node3912 node3912Labels := by
    have ha : raw2565 = raw2566 := by apply Matrix.ext; unfold raw2565 raw2566; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5453 = raw2566Labels := by decide +kernel
    rw [ha, hj, canonical2566 B hB]
  have hc1 : mixedMoment B raw2565 (Fin.cases (1 : Fin 2) singletonSmall5453) =
      mixedMoment B node3912 node3912Labels := by
    have ha : raw2565 = raw2567 := by apply Matrix.ext; unfold raw2565 raw2567; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5453 = raw2567Labels := by decide +kernel
    rw [ha, hj, canonical2567 B hB]
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

theorem sound505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node505 node505Labels = Sparse.eval nodeValue505 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue505 (familyPairVector B) := singlePair505 B _hB
    _ = _ := by norm_num [singlePairValue505, nodeValue505, Sparse.eval, mixedVector] <;> ring

theorem sound3814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3814 node3814Labels = Sparse.eval nodeValue3814 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3814) = mixedMoment B node3814 node3814Labels := rfl
  simpa [nodeValue3814, Sparse.eval] using hc.symm

theorem sound3912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3912 node3912Labels = Sparse.eval nodeValue3912 (mixedVector B) := by
  have h := singleton3912 B _hB
  rw [sound505 B _hB _hF] at h
  norm_num [nodeValue3912, nodeValue505, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5412 node5412Labels = Sparse.eval nodeValue5412 (mixedVector B) := by
  have h := singleton5412 B _hB
  rw [sound3814 B _hB _hF] at h
  norm_num [nodeValue5412, nodeValue3814, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5453 node5453Labels = Sparse.eval nodeValue5453 (mixedVector B) := by
  have h := singleton5453 B _hB
  rw [sound3912 B _hB _hF] at h
  norm_num [nodeValue5453, nodeValue3912, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2908 node2908Labels = Sparse.eval nodeValue2908 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2908) = mixedMoment B node2908 node2908Labels := rfl
  simpa [nodeValue2908, Sparse.eval] using hc.symm

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

theorem sound3053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3053 node3053Labels = Sparse.eval nodeValue3053 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3053) = mixedMoment B node3053 node3053Labels := rfl
  simpa [nodeValue3053, Sparse.eval] using hc.symm

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

theorem sound3600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3600 node3600Labels = Sparse.eval nodeValue3600 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3600) = mixedMoment B node3600 node3600Labels := rfl
  simpa [nodeValue3600, Sparse.eval] using hc.symm

theorem sound3619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3619 node3619Labels = Sparse.eval nodeValue3619 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3619) = mixedMoment B node3619 node3619Labels := rfl
  simpa [nodeValue3619, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3713 node3713Labels = Sparse.eval nodeValue3713 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3713) = mixedMoment B node3713 node3713Labels := rfl
  simpa [nodeValue3713, Sparse.eval] using hc.symm

theorem sound3731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3731 node3731Labels = Sparse.eval nodeValue3731 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3731) = mixedMoment B node3731 node3731Labels := rfl
  simpa [nodeValue3731, Sparse.eval] using hc.symm

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

theorem sound3867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3867 node3867Labels = Sparse.eval nodeValue3867 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3867) = mixedMoment B node3867 node3867Labels := rfl
  simpa [nodeValue3867, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5166 node5166Labels = 0 := by
  exact mixedMoment_alpha B hF node5166 node5166Labels 1 permutation161
    (by decide +kernel)

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

theorem sound5155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5155 node5155Labels = Sparse.eval nodeValue5155 (mixedVector B) := by
  have h := singleton5155 B _hB
  rw [sound2908 B _hB _hF, sound3600 B _hB _hF] at h
  norm_num [nodeValue5155, nodeValue2908, nodeValue3600, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5166 node5166Labels = Sparse.eval nodeValue5166 (mixedVector B) := by
  simpa only [nodeValue5166, Sparse.eval_nil] using zero5166 B _hB _hF

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

theorem sound5301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5301 node5301Labels = Sparse.eval nodeValue5301 (mixedVector B) := by
  have h := singleton5301 B _hB
  rw [sound3053 B _hB _hF, sound3619 B _hB _hF] at h
  norm_num [nodeValue5301, nodeValue3053, nodeValue3619, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5374 node5374Labels = Sparse.eval nodeValue5374 (mixedVector B) := by
  have h := singleton5374 B _hB
  rw [sound3713 B _hB _hF] at h
  norm_num [nodeValue5374, nodeValue3713, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5383 node5383Labels = Sparse.eval nodeValue5383 (mixedVector B) := by
  have h := singleton5383 B _hB
  rw [sound3731 B _hB _hF, sound3867 B _hB _hF] at h
  norm_num [nodeValue5383, nodeValue3731, nodeValue3867, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources34
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1101 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1101 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1101 + difference 0 1) (sourceB1101 + difference 1 0) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5383) := by
    have ha : (tripleCharges (sourceA1101 + difference 0 1) (sourceB1101 + difference 1 0) sourceC1101) = raw18433 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18433; decide +kernel
    rw [ha]
    exact (canonical18433 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1101 + difference 0 2) (sourceB1101 + difference 2 0) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5166) := by
    have ha : (tripleCharges (sourceA1101 + difference 0 2) (sourceB1101 + difference 2 0) sourceC1101) = raw18434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18434; decide +kernel
    rw [ha]
    exact (canonical18434 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1101 + difference 0 3) (sourceB1101 + difference 3 0) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1101 + difference 0 3) (sourceB1101 + difference 3 0) sourceC1101) = raw18435 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18435; decide +kernel
    rw [ha]
    exact (canonical18435 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1101 + difference 0 4) (sourceB1101 + difference 4 0) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1101 + difference 0 4) (sourceB1101 + difference 4 0) sourceC1101) = raw18436 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18436; decide +kernel
    rw [ha]
    exact (canonical18436 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1101 + difference 0 5) (sourceB1101 + difference 5 0) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1101 + difference 0 5) (sourceB1101 + difference 5 0) sourceC1101) = raw18437 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18437; decide +kernel
    rw [ha]
    exact (canonical18437 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1101 + difference 1 0) (sourceB1101 + difference 0 1) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA1101 + difference 1 0) (sourceB1101 + difference 0 1) sourceC1101) = raw18438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18438; decide +kernel
    rw [ha]
    exact (canonical18438 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1101 + difference 1 2) (sourceB1101 + difference 2 1) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA1101 + difference 1 2) (sourceB1101 + difference 2 1) sourceC1101) = raw12939 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw12939; decide +kernel
    rw [ha]
    exact (canonical12939 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1101 + difference 1 3) (sourceB1101 + difference 3 1) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA1101 + difference 1 3) (sourceB1101 + difference 3 1) sourceC1101) = raw12940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw12940; decide +kernel
    rw [ha]
    exact (canonical12940 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1101 + difference 1 4) (sourceB1101 + difference 4 1) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA1101 + difference 1 4) (sourceB1101 + difference 4 1) sourceC1101) = raw12941 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw12941; decide +kernel
    rw [ha]
    exact (canonical12941 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1101 + difference 1 5) (sourceB1101 + difference 5 1) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA1101 + difference 1 5) (sourceB1101 + difference 5 1) sourceC1101) = raw12942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw12942; decide +kernel
    rw [ha]
    exact (canonical12942 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1101 + difference 2 0) (sourceB1101 + difference 0 2) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5166) := by
    have ha : (tripleCharges (sourceA1101 + difference 2 0) (sourceB1101 + difference 0 2) sourceC1101) = raw12949 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw12949; decide +kernel
    rw [ha]
    exact (canonical12949 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1101 + difference 2 1) (sourceB1101 + difference 1 2) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5383) := by
    have ha : (tripleCharges (sourceA1101 + difference 2 1) (sourceB1101 + difference 1 2) sourceC1101) = raw18439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18439; decide +kernel
    rw [ha]
    exact (canonical18439 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1101 + difference 2 3) (sourceB1101 + difference 3 2) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1101 + difference 2 3) (sourceB1101 + difference 3 2) sourceC1101) = raw18440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18440; decide +kernel
    rw [ha]
    exact (canonical18440 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1101 + difference 2 4) (sourceB1101 + difference 4 2) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1101 + difference 2 4) (sourceB1101 + difference 4 2) sourceC1101) = raw18441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18441; decide +kernel
    rw [ha]
    exact (canonical18441 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1101 + difference 2 5) (sourceB1101 + difference 5 2) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1101 + difference 2 5) (sourceB1101 + difference 5 2) sourceC1101) = raw18442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18442; decide +kernel
    rw [ha]
    exact (canonical18442 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1101 + difference 3 0) (sourceB1101 + difference 0 3) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5155) := by
    have ha : (tripleCharges (sourceA1101 + difference 3 0) (sourceB1101 + difference 0 3) sourceC1101) = raw12954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw12954; decide +kernel
    rw [ha]
    exact (canonical12954 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1101 + difference 3 1) (sourceB1101 + difference 1 3) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5374) := by
    have ha : (tripleCharges (sourceA1101 + difference 3 1) (sourceB1101 + difference 1 3) sourceC1101) = raw18443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18443; decide +kernel
    rw [ha]
    exact (canonical18443 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1101 + difference 3 2) (sourceB1101 + difference 2 3) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5155) := by
    have ha : (tripleCharges (sourceA1101 + difference 3 2) (sourceB1101 + difference 2 3) sourceC1101) = raw18444 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18444; decide +kernel
    rw [ha]
    exact (canonical18444 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1101 + difference 3 4) (sourceB1101 + difference 4 3) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA1101 + difference 3 4) (sourceB1101 + difference 4 3) sourceC1101) = raw18445 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18445; decide +kernel
    rw [ha]
    exact (canonical18445 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1101 + difference 3 5) (sourceB1101 + difference 5 3) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA1101 + difference 3 5) (sourceB1101 + difference 5 3) sourceC1101) = raw18446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18446; decide +kernel
    rw [ha]
    exact (canonical18446 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1101 + difference 4 0) (sourceB1101 + difference 0 4) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5155) := by
    have ha : (tripleCharges (sourceA1101 + difference 4 0) (sourceB1101 + difference 0 4) sourceC1101) = raw12959 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw12959; decide +kernel
    rw [ha]
    exact (canonical12959 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1101 + difference 4 1) (sourceB1101 + difference 1 4) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5374) := by
    have ha : (tripleCharges (sourceA1101 + difference 4 1) (sourceB1101 + difference 1 4) sourceC1101) = raw18447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18447; decide +kernel
    rw [ha]
    exact (canonical18447 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1101 + difference 4 2) (sourceB1101 + difference 2 4) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5155) := by
    have ha : (tripleCharges (sourceA1101 + difference 4 2) (sourceB1101 + difference 2 4) sourceC1101) = raw18448 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18448; decide +kernel
    rw [ha]
    exact (canonical18448 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1101 + difference 4 3) (sourceB1101 + difference 3 4) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA1101 + difference 4 3) (sourceB1101 + difference 3 4) sourceC1101) = raw18449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18449; decide +kernel
    rw [ha]
    exact (canonical18449 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1101 + difference 4 5) (sourceB1101 + difference 5 4) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA1101 + difference 4 5) (sourceB1101 + difference 5 4) sourceC1101) = raw18450 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18450; decide +kernel
    rw [ha]
    exact (canonical18450 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1101 + difference 5 0) (sourceB1101 + difference 0 5) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5155) := by
    have ha : (tripleCharges (sourceA1101 + difference 5 0) (sourceB1101 + difference 0 5) sourceC1101) = raw12964 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw12964; decide +kernel
    rw [ha]
    exact (canonical12964 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1101 + difference 5 1) (sourceB1101 + difference 1 5) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5374) := by
    have ha : (tripleCharges (sourceA1101 + difference 5 1) (sourceB1101 + difference 1 5) sourceC1101) = raw18451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18451; decide +kernel
    rw [ha]
    exact (canonical18451 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1101 + difference 5 2) (sourceB1101 + difference 2 5) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5155) := by
    have ha : (tripleCharges (sourceA1101 + difference 5 2) (sourceB1101 + difference 2 5) sourceC1101) = raw18452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18452; decide +kernel
    rw [ha]
    exact (canonical18452 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1101 + difference 5 3) (sourceB1101 + difference 3 5) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA1101 + difference 5 3) (sourceB1101 + difference 3 5) sourceC1101) = raw18453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18453; decide +kernel
    rw [ha]
    exact (canonical18453 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1101 + difference 5 4) (sourceB1101 + difference 4 5) sourceC1101) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA1101 + difference 5 4) (sourceB1101 + difference 4 5) sourceC1101) = raw18454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1101 sourceB1101 sourceC1101 difference raw18454; decide +kernel
    rw [ha]
    exact (canonical18454 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1101 sourceB1101 sourceC1101
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1101, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck954 : Integer.Sparse.reindex keyMap MixedData.row954 = numericRow954 := by decide +kernel

theorem numericCheck954 (x : Master → ℝ) : Integer.Sparse.eval numericRow954 x =
    (2880 : ℝ) * reducedSource954 x := by
  norm_num [numericRow954, reducedSource954, Integer.Sparse.eval, Sparse.eval, nodeValue5155, nodeValue5166, nodeValue5301, nodeValue5374, nodeValue5383, nodeValue5412, nodeValue5439, nodeValue5453] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero954 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource954 (mixedVector B) = 0 := by
  have h5155 : mixedVector B (Sum.inr 5155) = Sparse.eval nodeValue5155 (mixedVector B) := by
    change mixedMoment B node5155 node5155Labels = _
    exact sound5155 B hB hF
  have h5166 : mixedVector B (Sum.inr 5166) = Sparse.eval nodeValue5166 (mixedVector B) := by
    change mixedMoment B node5166 node5166Labels = _
    exact sound5166 B hB hF
  have h5301 : mixedVector B (Sum.inr 5301) = Sparse.eval nodeValue5301 (mixedVector B) := by
    change mixedMoment B node5301 node5301Labels = _
    exact sound5301 B hB hF
  have h5374 : mixedVector B (Sum.inr 5374) = Sparse.eval nodeValue5374 (mixedVector B) := by
    change mixedMoment B node5374 node5374Labels = _
    exact sound5374 B hB hF
  have h5383 : mixedVector B (Sum.inr 5383) = Sparse.eval nodeValue5383 (mixedVector B) := by
    change mixedMoment B node5383 node5383Labels = _
    exact sound5383 B hB hF
  have h5412 : mixedVector B (Sum.inr 5412) = Sparse.eval nodeValue5412 (mixedVector B) := by
    change mixedMoment B node5412 node5412Labels = _
    exact sound5412 B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439_e B hB hF
  have h5453 : mixedVector B (Sum.inr 5453) = Sparse.eval nodeValue5453 (mixedVector B) := by
    change mixedMoment B node5453 node5453Labels = _
    exact sound5453 B hB hF
  simpa only [sourceForm1101, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5155, h5166, h5301, h5374, h5383, h5412, h5439, h5453, reducedSource954] using sourceEq1101 B hB

theorem rowSound954_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row954 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck954, numericCheck954, reducedZero954 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound954_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound954_e_oai
