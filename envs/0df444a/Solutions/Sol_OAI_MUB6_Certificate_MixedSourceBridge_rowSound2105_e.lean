-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2105_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T23:25:36.911554+00:00
-- url     : https://prove2.me/submissions/c8d614fc-bd15-4aed-88b3-50e31acf8a95

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E108
import Definitions.Def_OAIQ106E109
import Definitions.Def_OAIQ106E110
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5167_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5418_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5465_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5482_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical138
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17668 raw17668Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw17668 raw17668Labels = mixedMoment B raw17668step0 raw17668step0Labels := by
      have hz : ∀ j, raw17668 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17668step0 = (fun i j => raw17668 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17668step0 raw17668; decide +kernel
      have hl : raw17668step0Labels = raw17668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17668 raw17668Labels permutation434 hz
    _ = mixedMoment B node5465 node5465Labels := by rfl

theorem canonical17670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17670 raw17670Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw17670 raw17670Labels = mixedMoment B raw17670step0 raw17670step0Labels := by
      have hz : ∀ j, raw17670 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17670step0 = (fun i j => raw17670 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17670step0 raw17670; decide +kernel
      have hl : raw17670step0Labels = raw17670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17670 raw17670Labels permutation434 hz
    _ = mixedMoment B node5486 node5486Labels := by rfl

theorem canonical17672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17672 raw17672Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw17672 raw17672Labels = mixedMoment B raw17672step0 raw17672step0Labels := by
      have hz : ∀ j, raw17672 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17672step0 = (fun i j => raw17672 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17672step0 raw17672; decide +kernel
      have hl : raw17672step0Labels = raw17672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17672 raw17672Labels permutation346 hz
    _ = mixedMoment B node5465 node5465Labels := by rfl

theorem canonical17674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17674 raw17674Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw17674 raw17674Labels = mixedMoment B raw17674step0 raw17674step0Labels := by
      have hz : ∀ j, raw17674 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17674step0 = (fun i j => raw17674 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17674step0 raw17674; decide +kernel
      have hl : raw17674step0Labels = raw17674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17674 raw17674Labels permutation346 hz
    _ = mixedMoment B node5486 node5486Labels := by rfl

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

theorem canonical1902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1902 raw1902Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw1902 raw1902Labels = mixedMoment B raw1902step0 raw1902step0Labels := by
      have ha : raw1902step0 = (fun i j => raw1902 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1902step0 raw1902; decide +kernel
      have hl : raw1902step0Labels = raw1902Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1902 raw1902Labels permutation152 permutation4
    mixedMoment B raw1902step0 raw1902step0Labels = mixedMoment B raw1902step1 raw1902step1Labels := by
      have ha : raw1902step1 = raw1902step0 := by apply Matrix.ext; unfold raw1902step1 raw1902step0; decide +kernel
      have hl : raw1902step0Labels = labelEmbedding7 ∘ raw1902step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1902step0 raw1902step0Labels raw1902step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4939 node4939Labels := by rfl

theorem canonical1903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1903 raw1903Labels = mixedMoment B node2330 node2330Labels := by
  calc
    mixedMoment B raw1903 raw1903Labels = mixedMoment B raw1903step0 raw1903step0Labels := by
      have ha : raw1903step0 = (fun i j => raw1903 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1903step0 raw1903; decide +kernel
      have hl : raw1903step0Labels = raw1903Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1903 raw1903Labels permutation152 permutation4
    _ = mixedMoment B node2330 node2330Labels := by rfl

theorem canonical1904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1904 raw1904Labels = mixedMoment B node3404 node3404Labels := by
  calc
    mixedMoment B raw1904 raw1904Labels = mixedMoment B raw1904step0 raw1904step0Labels := by
      have ha : raw1904step0 = (fun i j => raw1904 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1904step0 raw1904; decide +kernel
      have hl : raw1904step0Labels = raw1904Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1904 raw1904Labels permutation152 permutation6
    mixedMoment B raw1904step0 raw1904step0Labels = mixedMoment B raw1904step1 raw1904step1Labels := by
      have ha : raw1904step1 = -raw1904step0 := by apply Matrix.ext; change ∀ i j, raw1904step1 i j = -(raw1904step0 i j); unfold raw1904step1 raw1904step0; decide +kernel
      have hl : raw1904step1Labels = raw1904step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1904step1 raw1904step1Labels = mixedMoment B raw1904step2 raw1904step2Labels := by
      have ha : raw1904step2 = raw1904step1 := by apply Matrix.ext; unfold raw1904step2 raw1904step1; decide +kernel
      have hl : raw1904step1Labels = labelEmbedding1 ∘ raw1904step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1904step1 raw1904step1Labels raw1904step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3404 node3404Labels := by rfl

theorem canonical1905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1905 raw1905Labels = mixedMoment B node4941 node4941Labels := by
  calc
    mixedMoment B raw1905 raw1905Labels = mixedMoment B raw1905step0 raw1905step0Labels := by
      have ha : raw1905step0 = (fun i j => raw1905 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1905step0 raw1905; decide +kernel
      have hl : raw1905step0Labels = raw1905Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1905 raw1905Labels permutation152 permutation4
    mixedMoment B raw1905step0 raw1905step0Labels = mixedMoment B raw1905step1 raw1905step1Labels := by
      have ha : raw1905step1 = raw1905step0 := by apply Matrix.ext; unfold raw1905step1 raw1905step0; decide +kernel
      have hl : raw1905step0Labels = labelEmbedding7 ∘ raw1905step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1905step0 raw1905step0Labels raw1905step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4941 node4941Labels := by rfl

theorem canonical1906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1906 raw1906Labels = mixedMoment B node2332 node2332Labels := by
  calc
    mixedMoment B raw1906 raw1906Labels = mixedMoment B raw1906step0 raw1906step0Labels := by
      have ha : raw1906step0 = (fun i j => raw1906 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1906step0 raw1906; decide +kernel
      have hl : raw1906step0Labels = raw1906Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1906 raw1906Labels permutation152 permutation4
    _ = mixedMoment B node2332 node2332Labels := by rfl

theorem canonical1907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1907 raw1907Labels = mixedMoment B node3410 node3410Labels := by
  calc
    mixedMoment B raw1907 raw1907Labels = mixedMoment B raw1907step0 raw1907step0Labels := by
      have ha : raw1907step0 = (fun i j => raw1907 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1907step0 raw1907; decide +kernel
      have hl : raw1907step0Labels = raw1907Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1907 raw1907Labels permutation152 permutation6
    mixedMoment B raw1907step0 raw1907step0Labels = mixedMoment B raw1907step1 raw1907step1Labels := by
      have ha : raw1907step1 = -raw1907step0 := by apply Matrix.ext; change ∀ i j, raw1907step1 i j = -(raw1907step0 i j); unfold raw1907step1 raw1907step0; decide +kernel
      have hl : raw1907step1Labels = raw1907step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1907step1 raw1907step1Labels = mixedMoment B raw1907step2 raw1907step2Labels := by
      have ha : raw1907step2 = raw1907step1 := by apply Matrix.ext; unfold raw1907step2 raw1907step1; decide +kernel
      have hl : raw1907step1Labels = labelEmbedding1 ∘ raw1907step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1907step1 raw1907step1Labels raw1907step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3410 node3410Labels := by rfl

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

theorem canonical2460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2460 raw2460Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw2460 raw2460Labels = mixedMoment B raw2460step0 raw2460step0Labels := by
      have ha : raw2460step0 = (fun i j => raw2460 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2460step0 raw2460; decide +kernel
      have hl : raw2460step0Labels = raw2460Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2460 raw2460Labels permutation152 permutation4
    mixedMoment B raw2460step0 raw2460step0Labels = mixedMoment B raw2460step1 raw2460step1Labels := by
      have ha : raw2460step1 = raw2460step0 := by apply Matrix.ext; unfold raw2460step1 raw2460step0; decide +kernel
      have hl : raw2460step0Labels = labelEmbedding7 ∘ raw2460step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2460step0 raw2460step0Labels raw2460step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

theorem canonical2461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2461 raw2461Labels = mixedMoment B node3779 node3779Labels := by
  calc
    mixedMoment B raw2461 raw2461Labels = mixedMoment B raw2461step0 raw2461step0Labels := by
      have ha : raw2461step0 = (fun i j => raw2461 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2461step0 raw2461; decide +kernel
      have hl : raw2461step0Labels = raw2461Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2461 raw2461Labels permutation152 permutation4
    _ = mixedMoment B node3779 node3779Labels := by rfl

theorem canonical2462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2462 raw2462Labels = mixedMoment B node3797 node3797Labels := by
  calc
    mixedMoment B raw2462 raw2462Labels = mixedMoment B raw2462step0 raw2462step0Labels := by
      have ha : raw2462step0 = (fun i j => raw2462 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2462step0 raw2462; decide +kernel
      have hl : raw2462step0Labels = raw2462Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2462 raw2462Labels permutation152 permutation6
    mixedMoment B raw2462step0 raw2462step0Labels = mixedMoment B raw2462step1 raw2462step1Labels := by
      have ha : raw2462step1 = -raw2462step0 := by apply Matrix.ext; change ∀ i j, raw2462step1 i j = -(raw2462step0 i j); unfold raw2462step1 raw2462step0; decide +kernel
      have hl : raw2462step1Labels = raw2462step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2462step1 raw2462step1Labels = mixedMoment B raw2462step2 raw2462step2Labels := by
      have ha : raw2462step2 = raw2462step1 := by apply Matrix.ext; unfold raw2462step2 raw2462step1; decide +kernel
      have hl : raw2462step1Labels = labelEmbedding1 ∘ raw2462step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2462step1 raw2462step1Labels raw2462step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3797 node3797Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical210
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26972 raw26972Labels = mixedMoment B node5167 node5167Labels := by
  calc
    mixedMoment B raw26972 raw26972Labels = mixedMoment B raw26972step0 raw26972step0Labels := by
      have ha : raw26972step0 = (fun i j => raw26972 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26972step0 raw26972; decide +kernel
      have hl : raw26972step0Labels = raw26972Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26972 raw26972Labels permutation168 permutation3
    mixedMoment B raw26972step0 raw26972step0Labels = mixedMoment B raw26972step1 raw26972step1Labels := by
      have ha : raw26972step1 = raw26972step0 := by apply Matrix.ext; unfold raw26972step1 raw26972step0; decide +kernel
      have hl : raw26972step0Labels = labelEmbedding6 ∘ raw26972step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26972step0 raw26972step0Labels raw26972step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5167 node5167Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical275
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical35228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35228 raw35228Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw35228 raw35228Labels = mixedMoment B raw35228step0 raw35228step0Labels := by
      have hz : ∀ j, raw35228 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35228step0 = (fun i j => raw35228 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35228step0 raw35228; decide +kernel
      have hl : raw35228step0Labels = raw35228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35228 raw35228Labels permutation434 hz
    mixedMoment B raw35228step0 raw35228step0Labels = mixedMoment B raw35228step1 raw35228step1Labels := by
      have ha : raw35228step1 = (fun i j => raw35228step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35228step1 raw35228step0; decide +kernel
      have hl : raw35228step1Labels = raw35228step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35228step0 raw35228step0Labels permutation33 permutation2
    _ = mixedMoment B node5465 node5465Labels := by rfl

theorem canonical35231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35231 raw35231Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw35231 raw35231Labels = mixedMoment B raw35231step0 raw35231step0Labels := by
      have hz : ∀ j, raw35231 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35231step0 = (fun i j => raw35231 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35231step0 raw35231; decide +kernel
      have hl : raw35231step0Labels = raw35231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35231 raw35231Labels permutation346 hz
    mixedMoment B raw35231step0 raw35231step0Labels = mixedMoment B raw35231step1 raw35231step1Labels := by
      have ha : raw35231step1 = (fun i j => raw35231step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35231step1 raw35231step0; decide +kernel
      have hl : raw35231step1Labels = raw35231step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35231step0 raw35231step0Labels permutation33 permutation2
    _ = mixedMoment B node5465 node5465Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical282
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical36130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36130 raw36130Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw36130 raw36130Labels = mixedMoment B raw36130step0 raw36130step0Labels := by
      have hz : ∀ j, raw36130 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36130step0 = (fun i j => raw36130 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36130step0 raw36130; decide +kernel
      have hl : raw36130step0Labels = raw36130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36130 raw36130Labels permutation346 hz
    mixedMoment B raw36130step0 raw36130step0Labels = mixedMoment B raw36130step1 raw36130step1Labels := by
      have ha : raw36130step1 = (fun i j => raw36130step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36130step1 raw36130step0; decide +kernel
      have hl : raw36130step1Labels = raw36130step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36130step0 raw36130step0Labels permutation56 permutation2
    _ = mixedMoment B node5486 node5486Labels := by rfl

theorem canonical36131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36131 raw36131Labels = mixedMoment B node4941 node4941Labels := by
  calc
    mixedMoment B raw36131 raw36131Labels = mixedMoment B raw36131step0 raw36131step0Labels := by
      have ha : raw36131step0 = (fun i j => raw36131 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36131step0 raw36131; decide +kernel
      have hl : raw36131step0Labels = raw36131Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36131 raw36131Labels permutation164 permutation3
    mixedMoment B raw36131step0 raw36131step0Labels = mixedMoment B raw36131step1 raw36131step1Labels := by
      have ha : raw36131step1 = raw36131step0 := by apply Matrix.ext; unfold raw36131step1 raw36131step0; decide +kernel
      have hl : raw36131step0Labels = labelEmbedding6 ∘ raw36131step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36131step0 raw36131step0Labels raw36131step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4941 node4941Labels := by rfl

theorem canonical36132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36132 raw36132Labels = mixedMoment B node4941 node4941Labels := by
  calc
    mixedMoment B raw36132 raw36132Labels = mixedMoment B raw36132step0 raw36132step0Labels := by
      have ha : raw36132step0 = (fun i j => raw36132 (permutation277 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36132step0 raw36132; decide +kernel
      have hl : raw36132step0Labels = raw36132Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36132 raw36132Labels permutation277 permutation3
    mixedMoment B raw36132step0 raw36132step0Labels = mixedMoment B raw36132step1 raw36132step1Labels := by
      have ha : raw36132step1 = raw36132step0 := by apply Matrix.ext; unfold raw36132step1 raw36132step0; decide +kernel
      have hl : raw36132step0Labels = labelEmbedding6 ∘ raw36132step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36132step0 raw36132step0Labels raw36132step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4941 node4941Labels := by rfl

theorem canonical36133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36133 raw36133Labels = mixedMoment B node5460 node5460Labels := by
  calc
    mixedMoment B raw36133 raw36133Labels = mixedMoment B raw36133step0 raw36133step0Labels := by
      have ha : raw36133step0 = (fun i j => raw36133 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36133step0 raw36133; decide +kernel
      have hl : raw36133step0Labels = raw36133Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36133 raw36133Labels permutation164 permutation3
    mixedMoment B raw36133step0 raw36133step0Labels = mixedMoment B raw36133step1 raw36133step1Labels := by
      have ha : raw36133step1 = raw36133step0 := by apply Matrix.ext; unfold raw36133step1 raw36133step0; decide +kernel
      have hl : raw36133step0Labels = labelEmbedding6 ∘ raw36133step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36133step0 raw36133step0Labels raw36133step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5460 node5460Labels := by rfl

theorem canonical36139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36139 raw36139Labels = mixedMoment B node5418 node5418Labels := by
  calc
    mixedMoment B raw36139 raw36139Labels = mixedMoment B raw36139step0 raw36139step0Labels := by
      have hz : ∀ j, raw36139 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36139step0 = (fun i j => raw36139 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36139step0 raw36139; decide +kernel
      have hl : raw36139step0Labels = raw36139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36139 raw36139Labels permutation346 hz
    mixedMoment B raw36139step0 raw36139step0Labels = mixedMoment B raw36139step1 raw36139step1Labels := by
      have ha : raw36139step1 = (fun i j => raw36139step0 (permutation96 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36139step1 raw36139step0; decide +kernel
      have hl : raw36139step1Labels = raw36139step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36139step0 raw36139step0Labels permutation96 permutation3
    mixedMoment B raw36139step1 raw36139step1Labels = mixedMoment B raw36139step2 raw36139step2Labels := by
      have ha : raw36139step2 = -raw36139step1 := by apply Matrix.ext; change ∀ i j, raw36139step2 i j = -(raw36139step1 i j); unfold raw36139step2 raw36139step1; decide +kernel
      have hl : raw36139step2Labels = raw36139step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36139step2 raw36139step2Labels = mixedMoment B raw36139step3 raw36139step3Labels := by
      have ha : raw36139step3 = raw36139step2 := by apply Matrix.ext; unfold raw36139step3 raw36139step2; decide +kernel
      have hl : raw36139step2Labels = labelEmbedding6 ∘ raw36139step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36139step2 raw36139step2Labels raw36139step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5418 node5418Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical290
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical37200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37200 raw37200Labels = mixedMoment B node5167 node5167Labels := by
  calc
    mixedMoment B raw37200 raw37200Labels = mixedMoment B raw37200step0 raw37200step0Labels := by
      have ha : raw37200step0 = (fun i j => raw37200 (permutation281 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37200step0 raw37200; decide +kernel
      have hl : raw37200step0Labels = raw37200Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37200 raw37200Labels permutation281 permutation3
    mixedMoment B raw37200step0 raw37200step0Labels = mixedMoment B raw37200step1 raw37200step1Labels := by
      have ha : raw37200step1 = raw37200step0 := by apply Matrix.ext; unfold raw37200step1 raw37200step0; decide +kernel
      have hl : raw37200step0Labels = labelEmbedding6 ∘ raw37200step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37200step0 raw37200step0Labels raw37200step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5167 node5167Labels := by rfl

theorem canonical37201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37201 raw37201Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw37201 raw37201Labels = mixedMoment B raw37201step0 raw37201step0Labels := by
      have hz : ∀ j, raw37201 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37201step0 = (fun i j => raw37201 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37201step0 raw37201; decide +kernel
      have hl : raw37201step0Labels = raw37201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37201 raw37201Labels permutation434 hz
    mixedMoment B raw37201step0 raw37201step0Labels = mixedMoment B raw37201step1 raw37201step1Labels := by
      have ha : raw37201step1 = (fun i j => raw37201step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37201step1 raw37201step0; decide +kernel
      have hl : raw37201step1Labels = raw37201step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37201step0 raw37201step0Labels permutation56 permutation2
    _ = mixedMoment B node5486 node5486Labels := by rfl

theorem canonical37202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37202 raw37202Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw37202 raw37202Labels = mixedMoment B raw37202step0 raw37202step0Labels := by
      have ha : raw37202step0 = (fun i j => raw37202 (permutation277 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37202step0 raw37202; decide +kernel
      have hl : raw37202step0Labels = raw37202Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37202 raw37202Labels permutation277 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical37203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37203 raw37203Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw37203 raw37203Labels = mixedMoment B raw37203step0 raw37203step0Labels := by
      have ha : raw37203step0 = (fun i j => raw37203 (permutation283 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37203step0 raw37203; decide +kernel
      have hl : raw37203step0Labels = raw37203Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37203 raw37203Labels permutation283 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical37204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37204 raw37204Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw37204 raw37204Labels = mixedMoment B raw37204step0 raw37204step0Labels := by
      have ha : raw37204step0 = (fun i j => raw37204 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37204step0 raw37204; decide +kernel
      have hl : raw37204step0Labels = raw37204Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37204 raw37204Labels permutation164 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical37205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37205 raw37205Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw37205 raw37205Labels = mixedMoment B raw37205step0 raw37205step0Labels := by
      have ha : raw37205step0 = (fun i j => raw37205 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37205step0 raw37205; decide +kernel
      have hl : raw37205step0Labels = raw37205Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37205 raw37205Labels permutation170 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical37206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37206 raw37206Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw37206 raw37206Labels = mixedMoment B raw37206step0 raw37206step0Labels := by
      have ha : raw37206step0 = (fun i j => raw37206 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37206step0 raw37206; decide +kernel
      have hl : raw37206step0Labels = raw37206Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37206 raw37206Labels permutation169 permutation3
    mixedMoment B raw37206step0 raw37206step0Labels = mixedMoment B raw37206step1 raw37206step1Labels := by
      have ha : raw37206step1 = raw37206step0 := by apply Matrix.ext; unfold raw37206step1 raw37206step0; decide +kernel
      have hl : raw37206step0Labels = labelEmbedding6 ∘ raw37206step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37206step0 raw37206step0Labels raw37206step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4939 node4939Labels := by rfl

theorem canonical37207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37207 raw37207Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw37207 raw37207Labels = mixedMoment B raw37207step0 raw37207step0Labels := by
      have ha : raw37207step0 = (fun i j => raw37207 (permutation282 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37207step0 raw37207; decide +kernel
      have hl : raw37207step0Labels = raw37207Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37207 raw37207Labels permutation282 permutation3
    mixedMoment B raw37207step0 raw37207step0Labels = mixedMoment B raw37207step1 raw37207step1Labels := by
      have ha : raw37207step1 = raw37207step0 := by apply Matrix.ext; unfold raw37207step1 raw37207step0; decide +kernel
      have hl : raw37207step0Labels = labelEmbedding6 ∘ raw37207step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37207step0 raw37207step0Labels raw37207step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4939 node4939Labels := by rfl

theorem canonical37208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37208 raw37208Labels = mixedMoment B node5418 node5418Labels := by
  calc
    mixedMoment B raw37208 raw37208Labels = mixedMoment B raw37208step0 raw37208step0Labels := by
      have hz : ∀ j, raw37208 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37208step0 = (fun i j => raw37208 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37208step0 raw37208; decide +kernel
      have hl : raw37208step0Labels = raw37208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37208 raw37208Labels permutation434 hz
    mixedMoment B raw37208step0 raw37208step0Labels = mixedMoment B raw37208step1 raw37208step1Labels := by
      have ha : raw37208step1 = (fun i j => raw37208step0 (permutation96 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37208step1 raw37208step0; decide +kernel
      have hl : raw37208step1Labels = raw37208step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37208step0 raw37208step0Labels permutation96 permutation3
    mixedMoment B raw37208step1 raw37208step1Labels = mixedMoment B raw37208step2 raw37208step2Labels := by
      have ha : raw37208step2 = -raw37208step1 := by apply Matrix.ext; change ∀ i j, raw37208step2 i j = -(raw37208step1 i j); unfold raw37208step2 raw37208step1; decide +kernel
      have hl : raw37208step2Labels = raw37208step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37208step2 raw37208step2Labels = mixedMoment B raw37208step3 raw37208step3Labels := by
      have ha : raw37208step3 = raw37208step2 := by apply Matrix.ext; unfold raw37208step3 raw37208step2; decide +kernel
      have hl : raw37208step2Labels = labelEmbedding6 ∘ raw37208step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37208step2 raw37208step2Labels raw37208step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5418 node5418Labels := by rfl

theorem canonical37209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37209 raw37209Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw37209 raw37209Labels = mixedMoment B raw37209step0 raw37209step0Labels := by
      have ha : raw37209step0 = (fun i j => raw37209 (permutation398 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37209step0 raw37209; decide +kernel
      have hl : raw37209step0Labels = raw37209Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37209 raw37209Labels permutation398 permutation3
    mixedMoment B raw37209step0 raw37209step0Labels = mixedMoment B raw37209step1 raw37209step1Labels := by
      have ha : raw37209step1 = -raw37209step0 := by apply Matrix.ext; change ∀ i j, raw37209step1 i j = -(raw37209step0 i j); unfold raw37209step1 raw37209step0; decide +kernel
      have hl : raw37209step1Labels = raw37209step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37209step1 raw37209step1Labels = mixedMoment B raw37209step2 raw37209step2Labels := by
      have ha : raw37209step2 = raw37209step1 := by apply Matrix.ext; unfold raw37209step2 raw37209step1; decide +kernel
      have hl : raw37209step1Labels = labelEmbedding6 ∘ raw37209step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37209step1 raw37209step1Labels raw37209step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

theorem canonical37210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37210 raw37210Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw37210 raw37210Labels = mixedMoment B raw37210step0 raw37210step0Labels := by
      have ha : raw37210step0 = (fun i j => raw37210 (permutation393 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37210step0 raw37210; decide +kernel
      have hl : raw37210step0Labels = raw37210Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37210 raw37210Labels permutation393 permutation3
    mixedMoment B raw37210step0 raw37210step0Labels = mixedMoment B raw37210step1 raw37210step1Labels := by
      have ha : raw37210step1 = -raw37210step0 := by apply Matrix.ext; change ∀ i j, raw37210step1 i j = -(raw37210step0 i j); unfold raw37210step1 raw37210step0; decide +kernel
      have hl : raw37210step1Labels = raw37210step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37210step1 raw37210step1Labels = mixedMoment B raw37210step2 raw37210step2Labels := by
      have ha : raw37210step2 = raw37210step1 := by apply Matrix.ext; unfold raw37210step2 raw37210step1; decide +kernel
      have hl : raw37210step1Labels = labelEmbedding6 ∘ raw37210step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37210step1 raw37210step1Labels raw37210step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

theorem canonical37211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37211 raw37211Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw37211 raw37211Labels = mixedMoment B raw37211step0 raw37211step0Labels := by
      have ha : raw37211step0 = (fun i j => raw37211 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37211step0 raw37211; decide +kernel
      have hl : raw37211step0Labels = raw37211Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37211 raw37211Labels permutation168 permutation3
    mixedMoment B raw37211step0 raw37211step0Labels = mixedMoment B raw37211step1 raw37211step1Labels := by
      have ha : raw37211step1 = raw37211step0 := by apply Matrix.ext; unfold raw37211step1 raw37211step0; decide +kernel
      have hl : raw37211step0Labels = labelEmbedding6 ∘ raw37211step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37211step0 raw37211step0Labels raw37211step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4939 node4939Labels := by rfl

theorem canonical37212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37212 raw37212Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw37212 raw37212Labels = mixedMoment B raw37212step0 raw37212step0Labels := by
      have ha : raw37212step0 = (fun i j => raw37212 (permutation281 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37212step0 raw37212; decide +kernel
      have hl : raw37212step0Labels = raw37212Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37212 raw37212Labels permutation281 permutation3
    mixedMoment B raw37212step0 raw37212step0Labels = mixedMoment B raw37212step1 raw37212step1Labels := by
      have ha : raw37212step1 = raw37212step0 := by apply Matrix.ext; unfold raw37212step1 raw37212step0; decide +kernel
      have hl : raw37212step0Labels = labelEmbedding6 ∘ raw37212step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37212step0 raw37212step0Labels raw37212step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4939 node4939Labels := by rfl

theorem canonical37213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37213 raw37213Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw37213 raw37213Labels = mixedMoment B raw37213step0 raw37213step0Labels := by
      have ha : raw37213step0 = (fun i j => raw37213 (permutation483 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37213step0 raw37213; decide +kernel
      have hl : raw37213step0Labels = raw37213Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37213 raw37213Labels permutation483 permutation3
    mixedMoment B raw37213step0 raw37213step0Labels = mixedMoment B raw37213step1 raw37213step1Labels := by
      have ha : raw37213step1 = -raw37213step0 := by apply Matrix.ext; change ∀ i j, raw37213step1 i j = -(raw37213step0 i j); unfold raw37213step1 raw37213step0; decide +kernel
      have hl : raw37213step1Labels = raw37213step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37213step1 raw37213step1Labels = mixedMoment B raw37213step2 raw37213step2Labels := by
      have ha : raw37213step2 = raw37213step1 := by apply Matrix.ext; unfold raw37213step2 raw37213step1; decide +kernel
      have hl : raw37213step1Labels = labelEmbedding6 ∘ raw37213step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37213step1 raw37213step1Labels raw37213step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

theorem canonical37214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37214 raw37214Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw37214 raw37214Labels = mixedMoment B raw37214step0 raw37214step0Labels := by
      have ha : raw37214step0 = (fun i j => raw37214 (permutation479 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37214step0 raw37214; decide +kernel
      have hl : raw37214step0Labels = raw37214Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37214 raw37214Labels permutation479 permutation3
    mixedMoment B raw37214step0 raw37214step0Labels = mixedMoment B raw37214step1 raw37214step1Labels := by
      have ha : raw37214step1 = -raw37214step0 := by apply Matrix.ext; change ∀ i j, raw37214step1 i j = -(raw37214step0 i j); unfold raw37214step1 raw37214step0; decide +kernel
      have hl : raw37214step1Labels = raw37214step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37214step1 raw37214step1Labels = mixedMoment B raw37214step2 raw37214step2Labels := by
      have ha : raw37214step2 = raw37214step1 := by apply Matrix.ext; unfold raw37214step2 raw37214step1; decide +kernel
      have hl : raw37214step1Labels = labelEmbedding6 ∘ raw37214step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37214step1 raw37214step1Labels raw37214step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

theorem canonical37215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37215 raw37215Labels = mixedMoment B node4941 node4941Labels := by
  calc
    mixedMoment B raw37215 raw37215Labels = mixedMoment B raw37215step0 raw37215step0Labels := by
      have ha : raw37215step0 = (fun i j => raw37215 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37215step0 raw37215; decide +kernel
      have hl : raw37215step0Labels = raw37215Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37215 raw37215Labels permutation170 permutation3
    mixedMoment B raw37215step0 raw37215step0Labels = mixedMoment B raw37215step1 raw37215step1Labels := by
      have ha : raw37215step1 = raw37215step0 := by apply Matrix.ext; unfold raw37215step1 raw37215step0; decide +kernel
      have hl : raw37215step0Labels = labelEmbedding6 ∘ raw37215step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37215step0 raw37215step0Labels raw37215step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4941 node4941Labels := by rfl

theorem canonical37216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37216 raw37216Labels = mixedMoment B node4941 node4941Labels := by
  calc
    mixedMoment B raw37216 raw37216Labels = mixedMoment B raw37216step0 raw37216step0Labels := by
      have ha : raw37216step0 = (fun i j => raw37216 (permutation283 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37216step0 raw37216; decide +kernel
      have hl : raw37216step0Labels = raw37216Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37216 raw37216Labels permutation283 permutation3
    mixedMoment B raw37216step0 raw37216step0Labels = mixedMoment B raw37216step1 raw37216step1Labels := by
      have ha : raw37216step1 = raw37216step0 := by apply Matrix.ext; unfold raw37216step1 raw37216step0; decide +kernel
      have hl : raw37216step0Labels = labelEmbedding6 ∘ raw37216step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37216step0 raw37216step0Labels raw37216step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4941 node4941Labels := by rfl

theorem canonical37217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37217 raw37217Labels = mixedMoment B node5460 node5460Labels := by
  calc
    mixedMoment B raw37217 raw37217Labels = mixedMoment B raw37217step0 raw37217step0Labels := by
      have ha : raw37217step0 = (fun i j => raw37217 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37217step0 raw37217; decide +kernel
      have hl : raw37217step0Labels = raw37217Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37217 raw37217Labels permutation170 permutation3
    mixedMoment B raw37217step0 raw37217step0Labels = mixedMoment B raw37217step1 raw37217step1Labels := by
      have ha : raw37217step1 = raw37217step0 := by apply Matrix.ext; unfold raw37217step1 raw37217step0; decide +kernel
      have hl : raw37217step0Labels = labelEmbedding6 ∘ raw37217step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37217step0 raw37217step0Labels raw37217step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5460 node5460Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4939 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4939 node4939Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2330 node2330Labels + mixedMoment B node3404 node3404Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1902 singletonSmall4939
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4939) = raw1902Labels := by decide +kernel
  rw [hl, canonical1902 B hB] at h
  have hc0 : mixedMoment B raw1902 (Fin.cases (0 : Fin 2) singletonSmall4939) =
      mixedMoment B node2330 node2330Labels := by
    have ha : raw1902 = raw1903 := by apply Matrix.ext; unfold raw1902 raw1903; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4939 = raw1903Labels := by decide +kernel
    rw [ha, hj, canonical1903 B hB]
  have hc1 : mixedMoment B raw1902 (Fin.cases (1 : Fin 2) singletonSmall4939) =
      mixedMoment B node3404 node3404Labels := by
    have ha : raw1902 = raw1904 := by apply Matrix.ext; unfold raw1902 raw1904; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4939 = raw1904Labels := by decide +kernel
    rw [ha, hj, canonical1904 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4941 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4941 node4941Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2332 node2332Labels + mixedMoment B node3410 node3410Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1905 singletonSmall4941
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4941) = raw1905Labels := by decide +kernel
  rw [hl, canonical1905 B hB] at h
  have hc0 : mixedMoment B raw1905 (Fin.cases (0 : Fin 2) singletonSmall4941) =
      mixedMoment B node2332 node2332Labels := by
    have ha : raw1905 = raw1906 := by apply Matrix.ext; unfold raw1905 raw1906; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4941 = raw1906Labels := by decide +kernel
    rw [ha, hj, canonical1906 B hB]
  have hc1 : mixedMoment B raw1905 (Fin.cases (1 : Fin 2) singletonSmall4941) =
      mixedMoment B node3410 node3410Labels := by
    have ha : raw1905 = raw1907 := by apply Matrix.ext; unfold raw1905 raw1907; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4941 = raw1907Labels := by decide +kernel
    rw [ha, hj, canonical1907 B hB]
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

theorem singleton5393 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5393 node5393Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3779 node3779Labels + mixedMoment B node3797 node3797Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2460 singletonSmall5393
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5393) = raw2460Labels := by decide +kernel
  rw [hl, canonical2460 B hB] at h
  have hc0 : mixedMoment B raw2460 (Fin.cases (0 : Fin 2) singletonSmall5393) =
      mixedMoment B node3779 node3779Labels := by
    have ha : raw2460 = raw2461 := by apply Matrix.ext; unfold raw2460 raw2461; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5393 = raw2461Labels := by decide +kernel
    rw [ha, hj, canonical2461 B hB]
  have hc1 : mixedMoment B raw2460 (Fin.cases (1 : Fin 2) singletonSmall5393) =
      mixedMoment B node3797 node3797Labels := by
    have ha : raw2460 = raw2462 := by apply Matrix.ext; unfold raw2460 raw2462; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5393 = raw2462Labels := by decide +kernel
    rw [ha, hj, canonical2462 B hB]
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

theorem zero5460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5460 node5460Labels = 0 := by
  exact mixedMoment_alpha B hF node5460 node5460Labels 2 permutation152
    (by decide +kernel)

theorem zero5486 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5486 node5486Labels = 0 := by
  exact mixedMoment_order_one B hB node5486 node5486Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2330 node2330Labels = Sparse.eval nodeValue2330 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2330) = mixedMoment B node2330 node2330Labels := rfl
  simpa [nodeValue2330, Sparse.eval] using hc.symm

theorem sound2332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2332 node2332Labels = Sparse.eval nodeValue2332 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2332) = mixedMoment B node2332 node2332Labels := rfl
  simpa [nodeValue2332, Sparse.eval] using hc.symm

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

theorem sound3404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3404 node3404Labels = Sparse.eval nodeValue3404 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3404) = mixedMoment B node3404 node3404Labels := rfl
  simpa [nodeValue3404, Sparse.eval] using hc.symm

theorem sound3410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3410 node3410Labels = Sparse.eval nodeValue3410 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3410) = mixedMoment B node3410 node3410Labels := rfl
  simpa [nodeValue3410, Sparse.eval] using hc.symm

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

theorem sound3779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3779 node3779Labels = Sparse.eval nodeValue3779 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3779) = mixedMoment B node3779 node3779Labels := rfl
  simpa [nodeValue3779, Sparse.eval] using hc.symm

theorem sound3797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3797 node3797Labels = Sparse.eval nodeValue3797 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3797) = mixedMoment B node3797 node3797Labels := rfl
  simpa [nodeValue3797, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4939 node4939Labels = Sparse.eval nodeValue4939 (mixedVector B) := by
  have h := singleton4939 B _hB
  rw [sound2330 B _hB _hF, sound3404 B _hB _hF] at h
  norm_num [nodeValue4939, nodeValue2330, nodeValue3404, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4941 node4941Labels = Sparse.eval nodeValue4941 (mixedVector B) := by
  have h := singleton4941 B _hB
  rw [sound2332 B _hB _hF, sound3410 B _hB _hF] at h
  norm_num [nodeValue4941, nodeValue2332, nodeValue3410, Sparse.eval] at h ⊢
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

theorem sound5393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5393 node5393Labels = Sparse.eval nodeValue5393 (mixedVector B) := by
  have h := singleton5393 B _hB
  rw [sound3779 B _hB _hF, sound3797 B _hB _hF] at h
  norm_num [nodeValue5393, nodeValue3779, nodeValue3797, Sparse.eval] at h ⊢
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

theorem sound5460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5460 node5460Labels = Sparse.eval nodeValue5460 (mixedVector B) := by
  simpa only [nodeValue5460, Sparse.eval_nil] using zero5460 B _hB _hF

theorem sound5486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5486 node5486Labels = Sparse.eval nodeValue5486 (mixedVector B) := by
  simpa only [nodeValue5486, Sparse.eval_nil] using zero5486 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources82
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2647 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2647 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2647 + difference 0 1) (sourceB2647 + difference 1 0) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA2647 + difference 0 1) (sourceB2647 + difference 1 0) sourceC2647) = raw37200 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37200; decide +kernel
    rw [ha]
    exact (canonical37200 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2647 + difference 0 2) (sourceB2647 + difference 2 0) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA2647 + difference 0 2) (sourceB2647 + difference 2 0) sourceC2647) = raw36130 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw36130; decide +kernel
    rw [ha]
    exact (canonical36130 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2647 + difference 0 3) (sourceB2647 + difference 3 0) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA2647 + difference 0 3) (sourceB2647 + difference 3 0) sourceC2647) = raw37201 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37201; decide +kernel
    rw [ha]
    exact (canonical37201 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2647 + difference 0 4) (sourceB2647 + difference 4 0) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA2647 + difference 0 4) (sourceB2647 + difference 4 0) sourceC2647) = raw37202 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37202; decide +kernel
    rw [ha]
    exact (canonical37202 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2647 + difference 0 5) (sourceB2647 + difference 5 0) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA2647 + difference 0 5) (sourceB2647 + difference 5 0) sourceC2647) = raw37203 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37203; decide +kernel
    rw [ha]
    exact (canonical37203 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2647 + difference 1 0) (sourceB2647 + difference 0 1) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA2647 + difference 1 0) (sourceB2647 + difference 0 1) sourceC2647) = raw26972 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw26972; decide +kernel
    rw [ha]
    exact (canonical26972 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2647 + difference 1 2) (sourceB2647 + difference 2 1) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA2647 + difference 1 2) (sourceB2647 + difference 2 1) sourceC2647) = raw17674 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw17674; decide +kernel
    rw [ha]
    exact (canonical17674 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2647 + difference 1 3) (sourceB2647 + difference 3 1) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA2647 + difference 1 3) (sourceB2647 + difference 3 1) sourceC2647) = raw17670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw17670; decide +kernel
    rw [ha]
    exact (canonical17670 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2647 + difference 1 4) (sourceB2647 + difference 4 1) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA2647 + difference 1 4) (sourceB2647 + difference 4 1) sourceC2647) = raw37204 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37204; decide +kernel
    rw [ha]
    exact (canonical37204 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2647 + difference 1 5) (sourceB2647 + difference 5 1) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA2647 + difference 1 5) (sourceB2647 + difference 5 1) sourceC2647) = raw37205 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37205; decide +kernel
    rw [ha]
    exact (canonical37205 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2647 + difference 2 0) (sourceB2647 + difference 0 2) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4939) := by
    have ha : (tripleCharges (sourceA2647 + difference 2 0) (sourceB2647 + difference 0 2) sourceC2647) = raw37206 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37206; decide +kernel
    rw [ha]
    exact (canonical37206 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2647 + difference 2 1) (sourceB2647 + difference 1 2) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4939) := by
    have ha : (tripleCharges (sourceA2647 + difference 2 1) (sourceB2647 + difference 1 2) sourceC2647) = raw37207 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37207; decide +kernel
    rw [ha]
    exact (canonical37207 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2647 + difference 2 3) (sourceB2647 + difference 3 2) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA2647 + difference 2 3) (sourceB2647 + difference 3 2) sourceC2647) = raw37208 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37208; decide +kernel
    rw [ha]
    exact (canonical37208 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2647 + difference 2 4) (sourceB2647 + difference 4 2) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2647 + difference 2 4) (sourceB2647 + difference 4 2) sourceC2647) = raw37209 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37209; decide +kernel
    rw [ha]
    exact (canonical37209 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2647 + difference 2 5) (sourceB2647 + difference 5 2) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2647 + difference 2 5) (sourceB2647 + difference 5 2) sourceC2647) = raw37210 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37210; decide +kernel
    rw [ha]
    exact (canonical37210 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2647 + difference 3 0) (sourceB2647 + difference 0 3) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4939) := by
    have ha : (tripleCharges (sourceA2647 + difference 3 0) (sourceB2647 + difference 0 3) sourceC2647) = raw37211 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37211; decide +kernel
    rw [ha]
    exact (canonical37211 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2647 + difference 3 1) (sourceB2647 + difference 1 3) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4939) := by
    have ha : (tripleCharges (sourceA2647 + difference 3 1) (sourceB2647 + difference 1 3) sourceC2647) = raw37212 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37212; decide +kernel
    rw [ha]
    exact (canonical37212 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2647 + difference 3 2) (sourceB2647 + difference 2 3) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA2647 + difference 3 2) (sourceB2647 + difference 2 3) sourceC2647) = raw36139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw36139; decide +kernel
    rw [ha]
    exact (canonical36139 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2647 + difference 3 4) (sourceB2647 + difference 4 3) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2647 + difference 3 4) (sourceB2647 + difference 4 3) sourceC2647) = raw37213 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37213; decide +kernel
    rw [ha]
    exact (canonical37213 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2647 + difference 3 5) (sourceB2647 + difference 5 3) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2647 + difference 3 5) (sourceB2647 + difference 5 3) sourceC2647) = raw37214 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37214; decide +kernel
    rw [ha]
    exact (canonical37214 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2647 + difference 4 0) (sourceB2647 + difference 0 4) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4941) := by
    have ha : (tripleCharges (sourceA2647 + difference 4 0) (sourceB2647 + difference 0 4) sourceC2647) = raw37215 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37215; decide +kernel
    rw [ha]
    exact (canonical37215 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2647 + difference 4 1) (sourceB2647 + difference 1 4) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4941) := by
    have ha : (tripleCharges (sourceA2647 + difference 4 1) (sourceB2647 + difference 1 4) sourceC2647) = raw37216 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37216; decide +kernel
    rw [ha]
    exact (canonical37216 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2647 + difference 4 2) (sourceB2647 + difference 2 4) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2647 + difference 4 2) (sourceB2647 + difference 2 4) sourceC2647) = raw35231 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw35231; decide +kernel
    rw [ha]
    exact (canonical35231 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2647 + difference 4 3) (sourceB2647 + difference 3 4) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2647 + difference 4 3) (sourceB2647 + difference 3 4) sourceC2647) = raw35228 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw35228; decide +kernel
    rw [ha]
    exact (canonical35228 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2647 + difference 4 5) (sourceB2647 + difference 5 4) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5460) := by
    have ha : (tripleCharges (sourceA2647 + difference 4 5) (sourceB2647 + difference 5 4) sourceC2647) = raw37217 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw37217; decide +kernel
    rw [ha]
    exact (canonical37217 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2647 + difference 5 0) (sourceB2647 + difference 0 5) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4941) := by
    have ha : (tripleCharges (sourceA2647 + difference 5 0) (sourceB2647 + difference 0 5) sourceC2647) = raw36131 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw36131; decide +kernel
    rw [ha]
    exact (canonical36131 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2647 + difference 5 1) (sourceB2647 + difference 1 5) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4941) := by
    have ha : (tripleCharges (sourceA2647 + difference 5 1) (sourceB2647 + difference 1 5) sourceC2647) = raw36132 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw36132; decide +kernel
    rw [ha]
    exact (canonical36132 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2647 + difference 5 2) (sourceB2647 + difference 2 5) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2647 + difference 5 2) (sourceB2647 + difference 2 5) sourceC2647) = raw17672 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw17672; decide +kernel
    rw [ha]
    exact (canonical17672 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2647 + difference 5 3) (sourceB2647 + difference 3 5) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2647 + difference 5 3) (sourceB2647 + difference 3 5) sourceC2647) = raw17668 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw17668; decide +kernel
    rw [ha]
    exact (canonical17668 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2647 + difference 5 4) (sourceB2647 + difference 4 5) sourceC2647) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5460) := by
    have ha : (tripleCharges (sourceA2647 + difference 5 4) (sourceB2647 + difference 4 5) sourceC2647) = raw36133 := by
      apply Matrix.ext; unfold tripleCharges sourceA2647 sourceB2647 sourceC2647 difference raw36133; decide +kernel
    rw [ha]
    exact (canonical36133 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2647 sourceB2647 sourceC2647
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2647, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2105 : Integer.Sparse.reindex keyMap MixedData.row2105 = numericRow2105 := by decide +kernel

theorem numericCheck2105 (x : Master → ℝ) : Integer.Sparse.eval numericRow2105 x =
    (8640 : ℝ) * reducedSource2105 x := by
  norm_num [numericRow2105, reducedSource2105, Integer.Sparse.eval, Sparse.eval, nodeValue4939, nodeValue4941, nodeValue5167, nodeValue5393, nodeValue5418, nodeValue5460, nodeValue5465, nodeValue5482, nodeValue5486] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2105 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2105 (mixedVector B) = 0 := by
  have h4939 : mixedVector B (Sum.inr 4939) = Sparse.eval nodeValue4939 (mixedVector B) := by
    change mixedMoment B node4939 node4939Labels = _
    exact sound4939 B hB hF
  have h4941 : mixedVector B (Sum.inr 4941) = Sparse.eval nodeValue4941 (mixedVector B) := by
    change mixedMoment B node4941 node4941Labels = _
    exact sound4941 B hB hF
  have h5167 : mixedVector B (Sum.inr 5167) = Sparse.eval nodeValue5167 (mixedVector B) := by
    change mixedMoment B node5167 node5167Labels = _
    exact sound5167_e B hB hF
  have h5393 : mixedVector B (Sum.inr 5393) = Sparse.eval nodeValue5393 (mixedVector B) := by
    change mixedMoment B node5393 node5393Labels = _
    exact sound5393 B hB hF
  have h5418 : mixedVector B (Sum.inr 5418) = Sparse.eval nodeValue5418 (mixedVector B) := by
    change mixedMoment B node5418 node5418Labels = _
    exact sound5418_e B hB hF
  have h5460 : mixedVector B (Sum.inr 5460) = Sparse.eval nodeValue5460 (mixedVector B) := by
    change mixedMoment B node5460 node5460Labels = _
    exact sound5460 B hB hF
  have h5465 : mixedVector B (Sum.inr 5465) = Sparse.eval nodeValue5465 (mixedVector B) := by
    change mixedMoment B node5465 node5465Labels = _
    exact sound5465_e B hB hF
  have h5482 : mixedVector B (Sum.inr 5482) = Sparse.eval nodeValue5482 (mixedVector B) := by
    change mixedMoment B node5482 node5482Labels = _
    exact sound5482_e B hB hF
  have h5486 : mixedVector B (Sum.inr 5486) = Sparse.eval nodeValue5486 (mixedVector B) := by
    change mixedMoment B node5486 node5486Labels = _
    exact sound5486 B hB hF
  simpa only [sourceForm2647, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4939, h4941, h5167, h5393, h5418, h5460, h5465, h5482, h5486, reducedSource2105] using sourceEq2647 B hB

theorem rowSound2105_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2105 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2105, numericCheck2105, reducedZero2105 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2105_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2105_e_oai
