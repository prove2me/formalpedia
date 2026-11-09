-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound10_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T19:27:29.370775+00:00
-- url     : https://prove2.me/submissions/c01c662e-4230-4de1-a3fb-7be1ed5a01c5

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E062
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E143
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E150
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

theorem canonical2325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2325 raw2325Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw2325 raw2325Labels = mixedMoment B raw2325step0 raw2325step0Labels := by
      have ha : raw2325step0 = (fun i j => raw2325 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2325step0 raw2325; decide +kernel
      have hl : raw2325step0Labels = raw2325Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2325 raw2325Labels permutation2 permutation4
    mixedMoment B raw2325step0 raw2325step0Labels = mixedMoment B raw2325step1 raw2325step1Labels := by
      have ha : raw2325step1 = raw2325step0 := by apply Matrix.ext; unfold raw2325step1 raw2325step0; decide +kernel
      have hl : raw2325step0Labels = labelEmbedding7 ∘ raw2325step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2325step0 raw2325step0Labels raw2325step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

theorem canonical2326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2326 raw2326Labels = mixedMoment B node2788 node2788Labels := by
  calc
    mixedMoment B raw2326 raw2326Labels = mixedMoment B raw2326step0 raw2326step0Labels := by
      have ha : raw2326step0 = (fun i j => raw2326 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2326step0 raw2326; decide +kernel
      have hl : raw2326step0Labels = raw2326Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2326 raw2326Labels permutation2 permutation4
    _ = mixedMoment B node2788 node2788Labels := by rfl

theorem canonical2327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2327 raw2327Labels = mixedMoment B node3633 node3633Labels := by
  calc
    mixedMoment B raw2327 raw2327Labels = mixedMoment B raw2327step0 raw2327step0Labels := by
      have ha : raw2327step0 = (fun i j => raw2327 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2327step0 raw2327; decide +kernel
      have hl : raw2327step0Labels = raw2327Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2327 raw2327Labels permutation3 permutation6
    mixedMoment B raw2327step0 raw2327step0Labels = mixedMoment B raw2327step1 raw2327step1Labels := by
      have ha : raw2327step1 = -raw2327step0 := by apply Matrix.ext; change ∀ i j, raw2327step1 i j = -(raw2327step0 i j); unfold raw2327step1 raw2327step0; decide +kernel
      have hl : raw2327step1Labels = raw2327step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2327step1 raw2327step1Labels = mixedMoment B raw2327step2 raw2327step2Labels := by
      have ha : raw2327step2 = raw2327step1 := by apply Matrix.ext; unfold raw2327step2 raw2327step1; decide +kernel
      have hl : raw2327step1Labels = labelEmbedding1 ∘ raw2327step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2327step1 raw2327step1Labels raw2327step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3633 node3633Labels := by rfl

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

theorem canonical2544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2544 raw2544Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw2544 raw2544Labels = mixedMoment B raw2544step0 raw2544step0Labels := by
      have ha : raw2544step0 = (fun i j => raw2544 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2544step0 raw2544; decide +kernel
      have hl : raw2544step0Labels = raw2544Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2544 raw2544Labels permutation8 permutation4
    mixedMoment B raw2544step0 raw2544step0Labels = mixedMoment B raw2544step1 raw2544step1Labels := by
      have ha : raw2544step1 = raw2544step0 := by apply Matrix.ext; unfold raw2544step1 raw2544step0; decide +kernel
      have hl : raw2544step0Labels = labelEmbedding7 ∘ raw2544step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2544step0 raw2544step0Labels raw2544step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

theorem canonical2545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2545 raw2545Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw2545 raw2545Labels = mixedMoment B raw2545step0 raw2545step0Labels := by
      have ha : raw2545step0 = (fun i j => raw2545 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2545step0 raw2545; decide +kernel
      have hl : raw2545step0Labels = raw2545Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2545 raw2545Labels permutation8 permutation4
    _ = mixedMoment B node3862 node3862Labels := by rfl

theorem canonical2546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2546 raw2546Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw2546 raw2546Labels = mixedMoment B raw2546step0 raw2546step0Labels := by
      have ha : raw2546step0 = (fun i j => raw2546 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2546step0 raw2546; decide +kernel
      have hl : raw2546step0Labels = raw2546Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2546 raw2546Labels permutation9 permutation6
    mixedMoment B raw2546step0 raw2546step0Labels = mixedMoment B raw2546step1 raw2546step1Labels := by
      have ha : raw2546step1 = -raw2546step0 := by apply Matrix.ext; change ∀ i j, raw2546step1 i j = -(raw2546step0 i j); unfold raw2546step1 raw2546step0; decide +kernel
      have hl : raw2546step1Labels = raw2546step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2546step1 raw2546step1Labels = mixedMoment B raw2546step2 raw2546step2Labels := by
      have ha : raw2546step2 = raw2546step1 := by apply Matrix.ext; unfold raw2546step2 raw2546step1; decide +kernel
      have hl : raw2546step1Labels = labelEmbedding1 ∘ raw2546step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2546step1 raw2546step1Labels raw2546step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3907 node3907Labels := by rfl

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

theorem canonical284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw284 raw284Labels = mixedMoment B node2788 node2788Labels := by
  calc
    mixedMoment B raw284 raw284Labels = mixedMoment B raw284step0 raw284step0Labels := by
      have ha : raw284step0 = (fun i j => raw284 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw284step0 raw284; decide +kernel
      have hl : raw284step0Labels = raw284Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw284 raw284Labels permutation2 permutation5
    mixedMoment B raw284step0 raw284step0Labels = mixedMoment B raw284step1 raw284step1Labels := by
      have ha : raw284step1 = raw284step0 := by apply Matrix.ext; unfold raw284step1 raw284step0; decide +kernel
      have hl : raw284step0Labels = labelEmbedding1 ∘ raw284step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw284step0 raw284step0Labels raw284step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2788 node2788Labels := by rfl

theorem canonical285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw285 raw285Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw285 raw285Labels = mixedMoment B raw285step0 raw285step0Labels := by
      have ha : raw285step0 = (fun i j => raw285 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw285step0 raw285; decide +kernel
      have hl : raw285step0Labels = raw285Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw285 raw285Labels permutation2 permutation5
    _ = mixedMoment B node420 node420Labels := by rfl

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

theorem canonical2568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2568 raw2568Labels = mixedMoment B node5456 node5456Labels := by
  calc
    _ = mixedMoment B node5456 node5456Labels := by rfl

theorem canonical2569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2569 raw2569Labels = mixedMoment B node3916 node3916Labels := by
  calc
    _ = mixedMoment B node3916 node3916Labels := by rfl

theorem canonical2570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2570 raw2570Labels = mixedMoment B node3916 node3916Labels := by
  calc
    mixedMoment B raw2570 raw2570Labels = mixedMoment B raw2570step0 raw2570step0Labels := by
      have ha : raw2570step0 = (fun i j => raw2570 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2570step0 raw2570; decide +kernel
      have hl : raw2570step0Labels = raw2570Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2570 raw2570Labels permutation7 permutation3
    mixedMoment B raw2570step0 raw2570step0Labels = mixedMoment B raw2570step1 raw2570step1Labels := by
      have ha : raw2570step1 = -raw2570step0 := by apply Matrix.ext; change ∀ i j, raw2570step1 i j = -(raw2570step0 i j); unfold raw2570step1 raw2570step0; decide +kernel
      have hl : raw2570step1Labels = raw2570step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2570step1 raw2570step1Labels = mixedMoment B raw2570step2 raw2570step2Labels := by
      have ha : raw2570step2 = raw2570step1 := by apply Matrix.ext; unfold raw2570step2 raw2570step1; decide +kernel
      have hl : raw2570step1Labels = labelEmbedding1 ∘ raw2570step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2570step1 raw2570step1Labels raw2570step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3916 node3916Labels := by rfl

theorem canonical2616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2616 raw2616Labels = mixedMoment B node5491 node5491Labels := by
  calc
    _ = mixedMoment B node5491 node5491Labels := by rfl

theorem canonical2617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2617 raw2617Labels = mixedMoment B node4014 node4014Labels := by
  calc
    _ = mixedMoment B node4014 node4014Labels := by rfl

theorem canonical2618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2618 raw2618Labels = mixedMoment B node4014 node4014Labels := by
  calc
    mixedMoment B raw2618 raw2618Labels = mixedMoment B raw2618step0 raw2618step0Labels := by
      have ha : raw2618step0 = (fun i j => raw2618 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2618step0 raw2618; decide +kernel
      have hl : raw2618step0Labels = raw2618Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2618 raw2618Labels permutation10 permutation3
    mixedMoment B raw2618step0 raw2618step0Labels = mixedMoment B raw2618step1 raw2618step1Labels := by
      have ha : raw2618step1 = raw2618step0 := by apply Matrix.ext; unfold raw2618step1 raw2618step0; decide +kernel
      have hl : raw2618step0Labels = labelEmbedding1 ∘ raw2618step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2618step0 raw2618step0Labels raw2618step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4014 node4014Labels := by rfl

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

theorem canonical2825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2825 raw2825Labels = mixedMoment B node5496 node5496Labels := by
  calc
    mixedMoment B raw2825 raw2825Labels = mixedMoment B raw2825step0 raw2825step0Labels := by
      have hz : ∀ j, raw2825 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2825step0 = (fun i j => raw2825 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2825step0 raw2825; decide +kernel
      have hl : raw2825step0Labels = raw2825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2825 raw2825Labels permutation520 hz
    mixedMoment B raw2825step0 raw2825step0Labels = mixedMoment B raw2825step1 raw2825step1Labels := by
      have hz : ∀ j, raw2825step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2825step1 = (fun i j => raw2825step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2825step1 raw2825step0; decide +kernel
      have hl : raw2825step1Labels = raw2825step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2825step0 raw2825step0Labels permutation104 hz
    mixedMoment B raw2825step1 raw2825step1Labels = mixedMoment B raw2825step2 raw2825step2Labels := by
      have hz : ∀ j, raw2825step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2825step2 = (fun i j => raw2825step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2825step2 raw2825step1; decide +kernel
      have hl : raw2825step2Labels = raw2825step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2825step1 raw2825step1Labels permutation20 hz
    mixedMoment B raw2825step2 raw2825step2Labels = mixedMoment B raw2825step3 raw2825step3Labels := by
      have hz : ∀ j, raw2825step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw2825step3 = (fun i j => raw2825step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw2825step3 raw2825step2; decide +kernel
      have hl : raw2825step3Labels = raw2825step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2825step2 raw2825step2Labels permutation4 hz
    mixedMoment B raw2825step3 raw2825step3Labels = mixedMoment B raw2825step4 raw2825step4Labels := by
      have ha : raw2825step4 = (fun i j => raw2825step3 (permutation0 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2825step4 raw2825step3; decide +kernel
      have hl : raw2825step4Labels = raw2825step3Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2825step3 raw2825step3Labels permutation0 permutation6
    mixedMoment B raw2825step4 raw2825step4Labels = mixedMoment B raw2825step5 raw2825step5Labels := by
      have ha : raw2825step5 = raw2825step4 := by apply Matrix.ext; unfold raw2825step5 raw2825step4; decide +kernel
      have hl : raw2825step4Labels = labelEmbedding9 ∘ raw2825step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2825step4 raw2825step4Labels raw2825step5Labels labelEmbedding9 hl
    _ = mixedMoment B node5496 node5496Labels := by rfl

theorem canonical2843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2843 raw2843Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw2843 raw2843Labels = mixedMoment B raw2843step0 raw2843step0Labels := by
      have hz : ∀ j, raw2843 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2843step0 = (fun i j => raw2843 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2843step0 raw2843; decide +kernel
      have hl : raw2843step0Labels = raw2843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2843 raw2843Labels permutation520 hz
    mixedMoment B raw2843step0 raw2843step0Labels = mixedMoment B raw2843step1 raw2843step1Labels := by
      have hz : ∀ j, raw2843step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2843step1 = (fun i j => raw2843step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2843step1 raw2843step0; decide +kernel
      have hl : raw2843step1Labels = raw2843step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2843step0 raw2843step0Labels permutation104 hz
    mixedMoment B raw2843step1 raw2843step1Labels = mixedMoment B raw2843step2 raw2843step2Labels := by
      have hz : ∀ j, raw2843step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2843step2 = (fun i j => raw2843step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2843step2 raw2843step1; decide +kernel
      have hl : raw2843step2Labels = raw2843step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2843step1 raw2843step1Labels permutation20 hz
    mixedMoment B raw2843step2 raw2843step2Labels = mixedMoment B raw2843step3 raw2843step3Labels := by
      have ha : raw2843step3 = (fun i j => raw2843step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2843step3 raw2843step2; decide +kernel
      have hl : raw2843step3Labels = raw2843step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2843step2 raw2843step2Labels permutation7 permutation6
    mixedMoment B raw2843step3 raw2843step3Labels = mixedMoment B raw2843step4 raw2843step4Labels := by
      have ha : raw2843step4 = -raw2843step3 := by apply Matrix.ext; change ∀ i j, raw2843step4 i j = -(raw2843step3 i j); unfold raw2843step4 raw2843step3; decide +kernel
      have hl : raw2843step4Labels = raw2843step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2843step4 raw2843step4Labels = mixedMoment B raw2843step5 raw2843step5Labels := by
      have ha : raw2843step5 = raw2843step4 := by apply Matrix.ext; unfold raw2843step5 raw2843step4; decide +kernel
      have hl : raw2843step4Labels = labelEmbedding9 ∘ raw2843step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2843step4 raw2843step4Labels raw2843step5Labels labelEmbedding9 hl
    _ = mixedMoment B node5455 node5455Labels := by rfl

theorem canonical2881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2881 raw2881Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw2881 raw2881Labels = mixedMoment B raw2881step0 raw2881step0Labels := by
      have hz : ∀ j, raw2881 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2881step0 = (fun i j => raw2881 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2881step0 raw2881; decide +kernel
      have hl : raw2881step0Labels = raw2881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2881 raw2881Labels permutation434 hz
    mixedMoment B raw2881step0 raw2881step0Labels = mixedMoment B raw2881step1 raw2881step1Labels := by
      have hz : ∀ j, raw2881step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2881step1 = (fun i j => raw2881step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2881step1 raw2881step0; decide +kernel
      have hl : raw2881step1Labels = raw2881step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2881step0 raw2881step0Labels permutation80 hz
    mixedMoment B raw2881step1 raw2881step1Labels = mixedMoment B raw2881step2 raw2881step2Labels := by
      have ha : raw2881step2 = (fun i j => raw2881step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2881step2 raw2881step1; decide +kernel
      have hl : raw2881step2Labels = raw2881step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2881step1 raw2881step1Labels permutation29 permutation6
    mixedMoment B raw2881step2 raw2881step2Labels = mixedMoment B raw2881step3 raw2881step3Labels := by
      have ha : raw2881step3 = -raw2881step2 := by apply Matrix.ext; change ∀ i j, raw2881step3 i j = -(raw2881step2 i j); unfold raw2881step3 raw2881step2; decide +kernel
      have hl : raw2881step3Labels = raw2881step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2881step3 raw2881step3Labels = mixedMoment B raw2881step4 raw2881step4Labels := by
      have ha : raw2881step4 = raw2881step3 := by apply Matrix.ext; unfold raw2881step4 raw2881step3; decide +kernel
      have hl : raw2881step3Labels = labelEmbedding9 ∘ raw2881step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2881step3 raw2881step3Labels raw2881step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5453 node5453Labels := by rfl

theorem canonical2882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2882 raw2882Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw2882 raw2882Labels = mixedMoment B raw2882step0 raw2882step0Labels := by
      have hz : ∀ j, raw2882 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2882step0 = (fun i j => raw2882 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2882step0 raw2882; decide +kernel
      have hl : raw2882step0Labels = raw2882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2882 raw2882Labels permutation434 hz
    mixedMoment B raw2882step0 raw2882step0Labels = mixedMoment B raw2882step1 raw2882step1Labels := by
      have hz : ∀ j, raw2882step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2882step1 = (fun i j => raw2882step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2882step1 raw2882step0; decide +kernel
      have hl : raw2882step1Labels = raw2882step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2882step0 raw2882step0Labels permutation56 hz
    mixedMoment B raw2882step1 raw2882step1Labels = mixedMoment B raw2882step2 raw2882step2Labels := by
      have ha : raw2882step2 = (fun i j => raw2882step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2882step2 raw2882step1; decide +kernel
      have hl : raw2882step2Labels = raw2882step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2882step1 raw2882step1Labels permutation29 permutation6
    mixedMoment B raw2882step2 raw2882step2Labels = mixedMoment B raw2882step3 raw2882step3Labels := by
      have ha : raw2882step3 = -raw2882step2 := by apply Matrix.ext; change ∀ i j, raw2882step3 i j = -(raw2882step2 i j); unfold raw2882step3 raw2882step2; decide +kernel
      have hl : raw2882step3Labels = raw2882step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2882step3 raw2882step3Labels = mixedMoment B raw2882step4 raw2882step4Labels := by
      have ha : raw2882step4 = raw2882step3 := by apply Matrix.ext; unfold raw2882step4 raw2882step3; decide +kernel
      have hl : raw2882step3Labels = labelEmbedding9 ∘ raw2882step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2882step3 raw2882step3Labels raw2882step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5453 node5453Labels := by rfl

theorem canonical2883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2883 raw2883Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw2883 raw2883Labels = mixedMoment B raw2883step0 raw2883step0Labels := by
      have hz : ∀ j, raw2883 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2883step0 = (fun i j => raw2883 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2883step0 raw2883; decide +kernel
      have hl : raw2883step0Labels = raw2883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2883 raw2883Labels permutation346 hz
    mixedMoment B raw2883step0 raw2883step0Labels = mixedMoment B raw2883step1 raw2883step1Labels := by
      have hz : ∀ j, raw2883step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2883step1 = (fun i j => raw2883step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2883step1 raw2883step0; decide +kernel
      have hl : raw2883step1Labels = raw2883step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2883step0 raw2883step0Labels permutation56 hz
    mixedMoment B raw2883step1 raw2883step1Labels = mixedMoment B raw2883step2 raw2883step2Labels := by
      have ha : raw2883step2 = (fun i j => raw2883step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2883step2 raw2883step1; decide +kernel
      have hl : raw2883step2Labels = raw2883step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2883step1 raw2883step1Labels permutation29 permutation6
    mixedMoment B raw2883step2 raw2883step2Labels = mixedMoment B raw2883step3 raw2883step3Labels := by
      have ha : raw2883step3 = -raw2883step2 := by apply Matrix.ext; change ∀ i j, raw2883step3 i j = -(raw2883step2 i j); unfold raw2883step3 raw2883step2; decide +kernel
      have hl : raw2883step3Labels = raw2883step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2883step3 raw2883step3Labels = mixedMoment B raw2883step4 raw2883step4Labels := by
      have ha : raw2883step4 = raw2883step3 := by apply Matrix.ext; unfold raw2883step4 raw2883step3; decide +kernel
      have hl : raw2883step3Labels = labelEmbedding9 ∘ raw2883step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2883step3 raw2883step3Labels raw2883step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5453 node5453Labels := by rfl

theorem canonical2884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2884 raw2884Labels = mixedMoment B node5456 node5456Labels := by
  calc
    mixedMoment B raw2884 raw2884Labels = mixedMoment B raw2884step0 raw2884step0Labels := by
      have hz : ∀ j, raw2884 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2884step0 = (fun i j => raw2884 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2884step0 raw2884; decide +kernel
      have hl : raw2884step0Labels = raw2884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2884 raw2884Labels permutation434 hz
    mixedMoment B raw2884step0 raw2884step0Labels = mixedMoment B raw2884step1 raw2884step1Labels := by
      have hz : ∀ j, raw2884step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2884step1 = (fun i j => raw2884step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2884step1 raw2884step0; decide +kernel
      have hl : raw2884step1Labels = raw2884step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2884step0 raw2884step0Labels permutation80 hz
    mixedMoment B raw2884step1 raw2884step1Labels = mixedMoment B raw2884step2 raw2884step2Labels := by
      have hz : ∀ j, raw2884step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2884step2 = (fun i j => raw2884step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2884step2 raw2884step1; decide +kernel
      have hl : raw2884step2Labels = raw2884step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2884step1 raw2884step1Labels permutation14 hz
    mixedMoment B raw2884step2 raw2884step2Labels = mixedMoment B raw2884step3 raw2884step3Labels := by
      have ha : raw2884step3 = (fun i j => raw2884step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2884step3 raw2884step2; decide +kernel
      have hl : raw2884step3Labels = raw2884step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2884step2 raw2884step2Labels permutation3 permutation2
    mixedMoment B raw2884step3 raw2884step3Labels = mixedMoment B raw2884step4 raw2884step4Labels := by
      have ha : raw2884step4 = -raw2884step3 := by apply Matrix.ext; change ∀ i j, raw2884step4 i j = -(raw2884step3 i j); unfold raw2884step4 raw2884step3; decide +kernel
      have hl : raw2884step4Labels = raw2884step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5456 node5456Labels := by rfl

theorem canonical2885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2885 raw2885Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw2885 raw2885Labels = mixedMoment B raw2885step0 raw2885step0Labels := by
      have hz : ∀ j, raw2885 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2885step0 = (fun i j => raw2885 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2885step0 raw2885; decide +kernel
      have hl : raw2885step0Labels = raw2885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2885 raw2885Labels permutation434 hz
    mixedMoment B raw2885step0 raw2885step0Labels = mixedMoment B raw2885step1 raw2885step1Labels := by
      have hz : ∀ j, raw2885step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2885step1 = (fun i j => raw2885step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2885step1 raw2885step0; decide +kernel
      have hl : raw2885step1Labels = raw2885step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2885step0 raw2885step0Labels permutation80 hz
    mixedMoment B raw2885step1 raw2885step1Labels = mixedMoment B raw2885step2 raw2885step2Labels := by
      have hz : ∀ j, raw2885step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2885step2 = (fun i j => raw2885step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2885step2 raw2885step1; decide +kernel
      have hl : raw2885step2Labels = raw2885step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2885step1 raw2885step1Labels permutation14 hz
    mixedMoment B raw2885step2 raw2885step2Labels = mixedMoment B raw2885step3 raw2885step3Labels := by
      have ha : raw2885step3 = (fun i j => raw2885step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw2885step3 raw2885step2; decide +kernel
      have hl : raw2885step3Labels = raw2885step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2885step2 raw2885step2Labels permutation2 permutation7
    mixedMoment B raw2885step3 raw2885step3Labels = mixedMoment B raw2885step4 raw2885step4Labels := by
      have ha : raw2885step4 = raw2885step3 := by apply Matrix.ext; unfold raw2885step4 raw2885step3; decide +kernel
      have hl : raw2885step3Labels = labelEmbedding10 ∘ raw2885step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2885step3 raw2885step3Labels raw2885step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5455 node5455Labels := by rfl

theorem canonical2886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2886 raw2886Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw2886 raw2886Labels = mixedMoment B raw2886step0 raw2886step0Labels := by
      have hz : ∀ j, raw2886 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2886step0 = (fun i j => raw2886 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2886step0 raw2886; decide +kernel
      have hl : raw2886step0Labels = raw2886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2886 raw2886Labels permutation434 hz
    mixedMoment B raw2886step0 raw2886step0Labels = mixedMoment B raw2886step1 raw2886step1Labels := by
      have hz : ∀ j, raw2886step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2886step1 = (fun i j => raw2886step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2886step1 raw2886step0; decide +kernel
      have hl : raw2886step1Labels = raw2886step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2886step0 raw2886step0Labels permutation80 hz
    mixedMoment B raw2886step1 raw2886step1Labels = mixedMoment B raw2886step2 raw2886step2Labels := by
      have ha : raw2886step2 = (fun i j => raw2886step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2886step2 raw2886step1; decide +kernel
      have hl : raw2886step2Labels = raw2886step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2886step1 raw2886step1Labels permutation29 permutation4
    mixedMoment B raw2886step2 raw2886step2Labels = mixedMoment B raw2886step3 raw2886step3Labels := by
      have ha : raw2886step3 = raw2886step2 := by apply Matrix.ext; unfold raw2886step3 raw2886step2; decide +kernel
      have hl : raw2886step2Labels = labelEmbedding7 ∘ raw2886step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2886step2 raw2886step2Labels raw2886step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5441 node5441Labels := by rfl

theorem canonical2887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2887 raw2887Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw2887 raw2887Labels = mixedMoment B raw2887step0 raw2887step0Labels := by
      have hz : ∀ j, raw2887 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2887step0 = (fun i j => raw2887 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2887step0 raw2887; decide +kernel
      have hl : raw2887step0Labels = raw2887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2887 raw2887Labels permutation434 hz
    mixedMoment B raw2887step0 raw2887step0Labels = mixedMoment B raw2887step1 raw2887step1Labels := by
      have ha : raw2887step1 = (fun i j => raw2887step0 (permutation137 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2887step1 raw2887step0; decide +kernel
      have hl : raw2887step1Labels = raw2887step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2887step0 raw2887step0Labels permutation137 permutation4
    mixedMoment B raw2887step1 raw2887step1Labels = mixedMoment B raw2887step2 raw2887step2Labels := by
      have ha : raw2887step2 = raw2887step1 := by apply Matrix.ext; unfold raw2887step2 raw2887step1; decide +kernel
      have hl : raw2887step1Labels = labelEmbedding7 ∘ raw2887step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2887step1 raw2887step1Labels raw2887step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

theorem canonical2888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2888 raw2888Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw2888 raw2888Labels = mixedMoment B raw2888step0 raw2888step0Labels := by
      have hz : ∀ j, raw2888 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2888step0 = (fun i j => raw2888 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2888step0 raw2888; decide +kernel
      have hl : raw2888step0Labels = raw2888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2888 raw2888Labels permutation346 hz
    mixedMoment B raw2888step0 raw2888step0Labels = mixedMoment B raw2888step1 raw2888step1Labels := by
      have ha : raw2888step1 = (fun i j => raw2888step0 (permutation137 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2888step1 raw2888step0; decide +kernel
      have hl : raw2888step1Labels = raw2888step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2888step0 raw2888step0Labels permutation137 permutation4
    mixedMoment B raw2888step1 raw2888step1Labels = mixedMoment B raw2888step2 raw2888step2Labels := by
      have ha : raw2888step2 = raw2888step1 := by apply Matrix.ext; unfold raw2888step2 raw2888step1; decide +kernel
      have hl : raw2888step1Labels = labelEmbedding7 ∘ raw2888step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2888step1 raw2888step1Labels raw2888step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

theorem canonical2889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2889 raw2889Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw2889 raw2889Labels = mixedMoment B raw2889step0 raw2889step0Labels := by
      have hz : ∀ j, raw2889 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2889step0 = (fun i j => raw2889 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2889step0 raw2889; decide +kernel
      have hl : raw2889step0Labels = raw2889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2889 raw2889Labels permutation434 hz
    mixedMoment B raw2889step0 raw2889step0Labels = mixedMoment B raw2889step1 raw2889step1Labels := by
      have hz : ∀ j, raw2889step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2889step1 = (fun i j => raw2889step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2889step1 raw2889step0; decide +kernel
      have hl : raw2889step1Labels = raw2889step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2889step0 raw2889step0Labels permutation80 hz
    mixedMoment B raw2889step1 raw2889step1Labels = mixedMoment B raw2889step2 raw2889step2Labels := by
      have ha : raw2889step2 = (fun i j => raw2889step1 (permutation28 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2889step2 raw2889step1; decide +kernel
      have hl : raw2889step2Labels = raw2889step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2889step1 raw2889step1Labels permutation28 permutation4
    mixedMoment B raw2889step2 raw2889step2Labels = mixedMoment B raw2889step3 raw2889step3Labels := by
      have ha : raw2889step3 = raw2889step2 := by apply Matrix.ext; unfold raw2889step3 raw2889step2; decide +kernel
      have hl : raw2889step2Labels = labelEmbedding7 ∘ raw2889step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2889step2 raw2889step2Labels raw2889step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

theorem canonical2890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2890 raw2890Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw2890 raw2890Labels = mixedMoment B raw2890step0 raw2890step0Labels := by
      have hz : ∀ j, raw2890 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2890step0 = (fun i j => raw2890 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2890step0 raw2890; decide +kernel
      have hl : raw2890step0Labels = raw2890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2890 raw2890Labels permutation434 hz
    mixedMoment B raw2890step0 raw2890step0Labels = mixedMoment B raw2890step1 raw2890step1Labels := by
      have hz : ∀ j, raw2890step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2890step1 = (fun i j => raw2890step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2890step1 raw2890step0; decide +kernel
      have hl : raw2890step1Labels = raw2890step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2890step0 raw2890step0Labels permutation80 hz
    mixedMoment B raw2890step1 raw2890step1Labels = mixedMoment B raw2890step2 raw2890step2Labels := by
      have ha : raw2890step2 = (fun i j => raw2890step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2890step2 raw2890step1; decide +kernel
      have hl : raw2890step2Labels = raw2890step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2890step1 raw2890step1Labels permutation10 permutation6
    mixedMoment B raw2890step2 raw2890step2Labels = mixedMoment B raw2890step3 raw2890step3Labels := by
      have ha : raw2890step3 = raw2890step2 := by apply Matrix.ext; unfold raw2890step3 raw2890step2; decide +kernel
      have hl : raw2890step2Labels = labelEmbedding9 ∘ raw2890step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2890step2 raw2890step2Labels raw2890step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5491 node5491Labels := by rfl

theorem canonical2891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2891 raw2891Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw2891 raw2891Labels = mixedMoment B raw2891step0 raw2891step0Labels := by
      have hz : ∀ j, raw2891 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2891step0 = (fun i j => raw2891 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2891step0 raw2891; decide +kernel
      have hl : raw2891step0Labels = raw2891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2891 raw2891Labels permutation434 hz
    mixedMoment B raw2891step0 raw2891step0Labels = mixedMoment B raw2891step1 raw2891step1Labels := by
      have hz : ∀ j, raw2891step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2891step1 = (fun i j => raw2891step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2891step1 raw2891step0; decide +kernel
      have hl : raw2891step1Labels = raw2891step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2891step0 raw2891step0Labels permutation56 hz
    mixedMoment B raw2891step1 raw2891step1Labels = mixedMoment B raw2891step2 raw2891step2Labels := by
      have ha : raw2891step2 = (fun i j => raw2891step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2891step2 raw2891step1; decide +kernel
      have hl : raw2891step2Labels = raw2891step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2891step1 raw2891step1Labels permutation29 permutation4
    mixedMoment B raw2891step2 raw2891step2Labels = mixedMoment B raw2891step3 raw2891step3Labels := by
      have ha : raw2891step3 = raw2891step2 := by apply Matrix.ext; unfold raw2891step3 raw2891step2; decide +kernel
      have hl : raw2891step2Labels = labelEmbedding7 ∘ raw2891step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2891step2 raw2891step2Labels raw2891step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5441 node5441Labels := by rfl

theorem canonical2892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2892 raw2892Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw2892 raw2892Labels = mixedMoment B raw2892step0 raw2892step0Labels := by
      have hz : ∀ j, raw2892 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2892step0 = (fun i j => raw2892 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2892step0 raw2892; decide +kernel
      have hl : raw2892step0Labels = raw2892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2892 raw2892Labels permutation434 hz
    mixedMoment B raw2892step0 raw2892step0Labels = mixedMoment B raw2892step1 raw2892step1Labels := by
      have ha : raw2892step1 = (fun i j => raw2892step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2892step1 raw2892step0; decide +kernel
      have hl : raw2892step1Labels = raw2892step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2892step0 raw2892step0Labels permutation143 permutation4
    mixedMoment B raw2892step1 raw2892step1Labels = mixedMoment B raw2892step2 raw2892step2Labels := by
      have ha : raw2892step2 = raw2892step1 := by apply Matrix.ext; unfold raw2892step2 raw2892step1; decide +kernel
      have hl : raw2892step1Labels = labelEmbedding7 ∘ raw2892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2892step1 raw2892step1Labels raw2892step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

theorem canonical2893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2893 raw2893Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw2893 raw2893Labels = mixedMoment B raw2893step0 raw2893step0Labels := by
      have hz : ∀ j, raw2893 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2893step0 = (fun i j => raw2893 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2893step0 raw2893; decide +kernel
      have hl : raw2893step0Labels = raw2893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2893 raw2893Labels permutation265 hz
    mixedMoment B raw2893step0 raw2893step0Labels = mixedMoment B raw2893step1 raw2893step1Labels := by
      have ha : raw2893step1 = (fun i j => raw2893step0 (permutation137 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2893step1 raw2893step0; decide +kernel
      have hl : raw2893step1Labels = raw2893step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2893step0 raw2893step0Labels permutation137 permutation4
    mixedMoment B raw2893step1 raw2893step1Labels = mixedMoment B raw2893step2 raw2893step2Labels := by
      have ha : raw2893step2 = raw2893step1 := by apply Matrix.ext; unfold raw2893step2 raw2893step1; decide +kernel
      have hl : raw2893step1Labels = labelEmbedding7 ∘ raw2893step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2893step1 raw2893step1Labels raw2893step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

theorem canonical2894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2894 raw2894Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw2894 raw2894Labels = mixedMoment B raw2894step0 raw2894step0Labels := by
      have hz : ∀ j, raw2894 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2894step0 = (fun i j => raw2894 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2894step0 raw2894; decide +kernel
      have hl : raw2894step0Labels = raw2894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2894 raw2894Labels permutation434 hz
    mixedMoment B raw2894step0 raw2894step0Labels = mixedMoment B raw2894step1 raw2894step1Labels := by
      have hz : ∀ j, raw2894step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2894step1 = (fun i j => raw2894step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2894step1 raw2894step0; decide +kernel
      have hl : raw2894step1Labels = raw2894step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2894step0 raw2894step0Labels permutation56 hz
    mixedMoment B raw2894step1 raw2894step1Labels = mixedMoment B raw2894step2 raw2894step2Labels := by
      have ha : raw2894step2 = (fun i j => raw2894step1 (permutation28 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2894step2 raw2894step1; decide +kernel
      have hl : raw2894step2Labels = raw2894step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2894step1 raw2894step1Labels permutation28 permutation4
    mixedMoment B raw2894step2 raw2894step2Labels = mixedMoment B raw2894step3 raw2894step3Labels := by
      have ha : raw2894step3 = raw2894step2 := by apply Matrix.ext; unfold raw2894step3 raw2894step2; decide +kernel
      have hl : raw2894step2Labels = labelEmbedding7 ∘ raw2894step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2894step2 raw2894step2Labels raw2894step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

theorem canonical2895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2895 raw2895Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw2895 raw2895Labels = mixedMoment B raw2895step0 raw2895step0Labels := by
      have hz : ∀ j, raw2895 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2895step0 = (fun i j => raw2895 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2895step0 raw2895; decide +kernel
      have hl : raw2895step0Labels = raw2895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2895 raw2895Labels permutation434 hz
    mixedMoment B raw2895step0 raw2895step0Labels = mixedMoment B raw2895step1 raw2895step1Labels := by
      have hz : ∀ j, raw2895step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2895step1 = (fun i j => raw2895step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2895step1 raw2895step0; decide +kernel
      have hl : raw2895step1Labels = raw2895step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2895step0 raw2895step0Labels permutation56 hz
    mixedMoment B raw2895step1 raw2895step1Labels = mixedMoment B raw2895step2 raw2895step2Labels := by
      have ha : raw2895step2 = (fun i j => raw2895step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2895step2 raw2895step1; decide +kernel
      have hl : raw2895step2Labels = raw2895step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2895step1 raw2895step1Labels permutation10 permutation6
    mixedMoment B raw2895step2 raw2895step2Labels = mixedMoment B raw2895step3 raw2895step3Labels := by
      have ha : raw2895step3 = raw2895step2 := by apply Matrix.ext; unfold raw2895step3 raw2895step2; decide +kernel
      have hl : raw2895step2Labels = labelEmbedding9 ∘ raw2895step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2895step2 raw2895step2Labels raw2895step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5491 node5491Labels := by rfl

theorem canonical2896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2896 raw2896Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw2896 raw2896Labels = mixedMoment B raw2896step0 raw2896step0Labels := by
      have hz : ∀ j, raw2896 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2896step0 = (fun i j => raw2896 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2896step0 raw2896; decide +kernel
      have hl : raw2896step0Labels = raw2896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2896 raw2896Labels permutation346 hz
    mixedMoment B raw2896step0 raw2896step0Labels = mixedMoment B raw2896step1 raw2896step1Labels := by
      have hz : ∀ j, raw2896step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2896step1 = (fun i j => raw2896step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2896step1 raw2896step0; decide +kernel
      have hl : raw2896step1Labels = raw2896step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2896step0 raw2896step0Labels permutation56 hz
    mixedMoment B raw2896step1 raw2896step1Labels = mixedMoment B raw2896step2 raw2896step2Labels := by
      have ha : raw2896step2 = (fun i j => raw2896step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2896step2 raw2896step1; decide +kernel
      have hl : raw2896step2Labels = raw2896step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2896step1 raw2896step1Labels permutation29 permutation4
    mixedMoment B raw2896step2 raw2896step2Labels = mixedMoment B raw2896step3 raw2896step3Labels := by
      have ha : raw2896step3 = raw2896step2 := by apply Matrix.ext; unfold raw2896step3 raw2896step2; decide +kernel
      have hl : raw2896step2Labels = labelEmbedding7 ∘ raw2896step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2896step2 raw2896step2Labels raw2896step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5441 node5441Labels := by rfl

theorem canonical2897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2897 raw2897Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw2897 raw2897Labels = mixedMoment B raw2897step0 raw2897step0Labels := by
      have hz : ∀ j, raw2897 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2897step0 = (fun i j => raw2897 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2897step0 raw2897; decide +kernel
      have hl : raw2897step0Labels = raw2897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2897 raw2897Labels permutation346 hz
    mixedMoment B raw2897step0 raw2897step0Labels = mixedMoment B raw2897step1 raw2897step1Labels := by
      have ha : raw2897step1 = (fun i j => raw2897step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2897step1 raw2897step0; decide +kernel
      have hl : raw2897step1Labels = raw2897step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2897step0 raw2897step0Labels permutation143 permutation4
    mixedMoment B raw2897step1 raw2897step1Labels = mixedMoment B raw2897step2 raw2897step2Labels := by
      have ha : raw2897step2 = raw2897step1 := by apply Matrix.ext; unfold raw2897step2 raw2897step1; decide +kernel
      have hl : raw2897step1Labels = labelEmbedding7 ∘ raw2897step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2897step1 raw2897step1Labels raw2897step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

theorem canonical2898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2898 raw2898Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw2898 raw2898Labels = mixedMoment B raw2898step0 raw2898step0Labels := by
      have hz : ∀ j, raw2898 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2898step0 = (fun i j => raw2898 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2898step0 raw2898; decide +kernel
      have hl : raw2898step0Labels = raw2898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2898 raw2898Labels permutation265 hz
    mixedMoment B raw2898step0 raw2898step0Labels = mixedMoment B raw2898step1 raw2898step1Labels := by
      have ha : raw2898step1 = (fun i j => raw2898step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2898step1 raw2898step0; decide +kernel
      have hl : raw2898step1Labels = raw2898step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2898step0 raw2898step0Labels permutation143 permutation4
    mixedMoment B raw2898step1 raw2898step1Labels = mixedMoment B raw2898step2 raw2898step2Labels := by
      have ha : raw2898step2 = raw2898step1 := by apply Matrix.ext; unfold raw2898step2 raw2898step1; decide +kernel
      have hl : raw2898step1Labels = labelEmbedding7 ∘ raw2898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2898step1 raw2898step1Labels raw2898step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

theorem canonical2899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2899 raw2899Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw2899 raw2899Labels = mixedMoment B raw2899step0 raw2899step0Labels := by
      have hz : ∀ j, raw2899 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2899step0 = (fun i j => raw2899 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2899step0 raw2899; decide +kernel
      have hl : raw2899step0Labels = raw2899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2899 raw2899Labels permutation346 hz
    mixedMoment B raw2899step0 raw2899step0Labels = mixedMoment B raw2899step1 raw2899step1Labels := by
      have hz : ∀ j, raw2899step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2899step1 = (fun i j => raw2899step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2899step1 raw2899step0; decide +kernel
      have hl : raw2899step1Labels = raw2899step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2899step0 raw2899step0Labels permutation56 hz
    mixedMoment B raw2899step1 raw2899step1Labels = mixedMoment B raw2899step2 raw2899step2Labels := by
      have ha : raw2899step2 = (fun i j => raw2899step1 (permutation28 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2899step2 raw2899step1; decide +kernel
      have hl : raw2899step2Labels = raw2899step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2899step1 raw2899step1Labels permutation28 permutation4
    mixedMoment B raw2899step2 raw2899step2Labels = mixedMoment B raw2899step3 raw2899step3Labels := by
      have ha : raw2899step3 = raw2899step2 := by apply Matrix.ext; unfold raw2899step3 raw2899step2; decide +kernel
      have hl : raw2899step2Labels = labelEmbedding7 ∘ raw2899step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2899step2 raw2899step2Labels raw2899step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

theorem canonical2900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2900 raw2900Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw2900 raw2900Labels = mixedMoment B raw2900step0 raw2900step0Labels := by
      have hz : ∀ j, raw2900 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2900step0 = (fun i j => raw2900 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2900step0 raw2900; decide +kernel
      have hl : raw2900step0Labels = raw2900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2900 raw2900Labels permutation346 hz
    mixedMoment B raw2900step0 raw2900step0Labels = mixedMoment B raw2900step1 raw2900step1Labels := by
      have hz : ∀ j, raw2900step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2900step1 = (fun i j => raw2900step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2900step1 raw2900step0; decide +kernel
      have hl : raw2900step1Labels = raw2900step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2900step0 raw2900step0Labels permutation56 hz
    mixedMoment B raw2900step1 raw2900step1Labels = mixedMoment B raw2900step2 raw2900step2Labels := by
      have ha : raw2900step2 = (fun i j => raw2900step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2900step2 raw2900step1; decide +kernel
      have hl : raw2900step2Labels = raw2900step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2900step1 raw2900step1Labels permutation10 permutation6
    mixedMoment B raw2900step2 raw2900step2Labels = mixedMoment B raw2900step3 raw2900step3Labels := by
      have ha : raw2900step3 = raw2900step2 := by apply Matrix.ext; unfold raw2900step3 raw2900step2; decide +kernel
      have hl : raw2900step2Labels = labelEmbedding9 ∘ raw2900step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2900step2 raw2900step2Labels raw2900step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5491 node5491Labels := by rfl

theorem canonical2901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2901 raw2901Labels = mixedMoment B node4094 node4094Labels := by
  calc
    mixedMoment B raw2901 raw2901Labels = mixedMoment B raw2901step0 raw2901step0Labels := by
      have hz : ∀ j, raw2901 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2901step0 = (fun i j => raw2901 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2901step0 raw2901; decide +kernel
      have hl : raw2901step0Labels = raw2901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2901 raw2901Labels permutation520 hz
    mixedMoment B raw2901step0 raw2901step0Labels = mixedMoment B raw2901step1 raw2901step1Labels := by
      have hz : ∀ j, raw2901step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2901step1 = (fun i j => raw2901step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2901step1 raw2901step0; decide +kernel
      have hl : raw2901step1Labels = raw2901step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2901step0 raw2901step0Labels permutation104 hz
    mixedMoment B raw2901step1 raw2901step1Labels = mixedMoment B raw2901step2 raw2901step2Labels := by
      have hz : ∀ j, raw2901step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2901step2 = (fun i j => raw2901step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2901step2 raw2901step1; decide +kernel
      have hl : raw2901step2Labels = raw2901step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2901step1 raw2901step1Labels permutation20 hz
    mixedMoment B raw2901step2 raw2901step2Labels = mixedMoment B raw2901step3 raw2901step3Labels := by
      have hz : ∀ j, raw2901step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw2901step3 = (fun i j => raw2901step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw2901step3 raw2901step2; decide +kernel
      have hl : raw2901step3Labels = raw2901step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2901step2 raw2901step2Labels permutation4 hz
    mixedMoment B raw2901step3 raw2901step3Labels = mixedMoment B raw2901step4 raw2901step4Labels := by
      have hz : ∀ i, raw2901step3 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw2901step4 = (fun i j => raw2901step3 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw2901step4 raw2901step3; decide +kernel
      have hl : raw2901step4Labels = (fun j => raw2901step3Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2901step3 raw2901step3Labels permutation2 hz
    mixedMoment B raw2901step4 raw2901step4Labels = mixedMoment B raw2901step5 raw2901step5Labels := by
      have ha : raw2901step5 = (fun i j => raw2901step4 (permutation1 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2901step5 raw2901step4; decide +kernel
      have hl : raw2901step5Labels = raw2901step4Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2901step4 raw2901step4Labels permutation1 permutation0
    mixedMoment B raw2901step5 raw2901step5Labels = mixedMoment B raw2901step6 raw2901step6Labels := by
      have ha : raw2901step6 = raw2901step5 := by apply Matrix.ext; unfold raw2901step6 raw2901step5; decide +kernel
      have hl : raw2901step5Labels = labelEmbedding3 ∘ raw2901step6Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2901step5 raw2901step5Labels raw2901step6Labels labelEmbedding3 hl
    _ = mixedMoment B node4094 node4094Labels := by rfl

theorem canonical2902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2902 raw2902Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw2902 raw2902Labels = mixedMoment B raw2902step0 raw2902step0Labels := by
      have hz : ∀ j, raw2902 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2902step0 = (fun i j => raw2902 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2902step0 raw2902; decide +kernel
      have hl : raw2902step0Labels = raw2902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2902 raw2902Labels permutation520 hz
    mixedMoment B raw2902step0 raw2902step0Labels = mixedMoment B raw2902step1 raw2902step1Labels := by
      have hz : ∀ j, raw2902step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2902step1 = (fun i j => raw2902step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2902step1 raw2902step0; decide +kernel
      have hl : raw2902step1Labels = raw2902step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2902step0 raw2902step0Labels permutation104 hz
    mixedMoment B raw2902step1 raw2902step1Labels = mixedMoment B raw2902step2 raw2902step2Labels := by
      have hz : ∀ j, raw2902step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2902step2 = (fun i j => raw2902step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2902step2 raw2902step1; decide +kernel
      have hl : raw2902step2Labels = raw2902step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2902step1 raw2902step1Labels permutation14 hz
    mixedMoment B raw2902step2 raw2902step2Labels = mixedMoment B raw2902step3 raw2902step3Labels := by
      have ha : raw2902step3 = (fun i j => raw2902step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2902step3 raw2902step2; decide +kernel
      have hl : raw2902step3Labels = raw2902step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2902step2 raw2902step2Labels permutation7 permutation6
    mixedMoment B raw2902step3 raw2902step3Labels = mixedMoment B raw2902step4 raw2902step4Labels := by
      have ha : raw2902step4 = -raw2902step3 := by apply Matrix.ext; change ∀ i j, raw2902step4 i j = -(raw2902step3 i j); unfold raw2902step4 raw2902step3; decide +kernel
      have hl : raw2902step4Labels = raw2902step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2902step4 raw2902step4Labels = mixedMoment B raw2902step5 raw2902step5Labels := by
      have ha : raw2902step5 = raw2902step4 := by apply Matrix.ext; unfold raw2902step5 raw2902step4; decide +kernel
      have hl : raw2902step4Labels = labelEmbedding9 ∘ raw2902step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2902step4 raw2902step4Labels raw2902step5Labels labelEmbedding9 hl
    _ = mixedMoment B node5455 node5455Labels := by rfl

theorem canonical2903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2903 raw2903Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw2903 raw2903Labels = mixedMoment B raw2903step0 raw2903step0Labels := by
      have hz : ∀ j, raw2903 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2903step0 = (fun i j => raw2903 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2903step0 raw2903; decide +kernel
      have hl : raw2903step0Labels = raw2903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2903 raw2903Labels permutation520 hz
    mixedMoment B raw2903step0 raw2903step0Labels = mixedMoment B raw2903step1 raw2903step1Labels := by
      have hz : ∀ j, raw2903step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2903step1 = (fun i j => raw2903step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2903step1 raw2903step0; decide +kernel
      have hl : raw2903step1Labels = raw2903step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2903step0 raw2903step0Labels permutation80 hz
    mixedMoment B raw2903step1 raw2903step1Labels = mixedMoment B raw2903step2 raw2903step2Labels := by
      have hz : ∀ j, raw2903step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2903step2 = (fun i j => raw2903step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2903step2 raw2903step1; decide +kernel
      have hl : raw2903step2Labels = raw2903step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2903step1 raw2903step1Labels permutation14 hz
    mixedMoment B raw2903step2 raw2903step2Labels = mixedMoment B raw2903step3 raw2903step3Labels := by
      have ha : raw2903step3 = (fun i j => raw2903step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2903step3 raw2903step2; decide +kernel
      have hl : raw2903step3Labels = raw2903step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2903step2 raw2903step2Labels permutation7 permutation6
    mixedMoment B raw2903step3 raw2903step3Labels = mixedMoment B raw2903step4 raw2903step4Labels := by
      have ha : raw2903step4 = -raw2903step3 := by apply Matrix.ext; change ∀ i j, raw2903step4 i j = -(raw2903step3 i j); unfold raw2903step4 raw2903step3; decide +kernel
      have hl : raw2903step4Labels = raw2903step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2903step4 raw2903step4Labels = mixedMoment B raw2903step5 raw2903step5Labels := by
      have ha : raw2903step5 = raw2903step4 := by apply Matrix.ext; unfold raw2903step5 raw2903step4; decide +kernel
      have hl : raw2903step4Labels = labelEmbedding9 ∘ raw2903step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2903step4 raw2903step4Labels raw2903step5Labels labelEmbedding9 hl
    _ = mixedMoment B node5455 node5455Labels := by rfl

theorem canonical2904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2904 raw2904Labels = mixedMoment B node5308 node5308Labels := by
  calc
    mixedMoment B raw2904 raw2904Labels = mixedMoment B raw2904step0 raw2904step0Labels := by
      have hz : ∀ j, raw2904 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2904step0 = (fun i j => raw2904 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2904step0 raw2904; decide +kernel
      have hl : raw2904step0Labels = raw2904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2904 raw2904Labels permutation434 hz
    mixedMoment B raw2904step0 raw2904step0Labels = mixedMoment B raw2904step1 raw2904step1Labels := by
      have hz : ∀ j, raw2904step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2904step1 = (fun i j => raw2904step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2904step1 raw2904step0; decide +kernel
      have hl : raw2904step1Labels = raw2904step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2904step0 raw2904step0Labels permutation80 hz
    mixedMoment B raw2904step1 raw2904step1Labels = mixedMoment B raw2904step2 raw2904step2Labels := by
      have hz : ∀ j, raw2904step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2904step2 = (fun i j => raw2904step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2904step2 raw2904step1; decide +kernel
      have hl : raw2904step2Labels = raw2904step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2904step1 raw2904step1Labels permutation14 hz
    mixedMoment B raw2904step2 raw2904step2Labels = mixedMoment B raw2904step3 raw2904step3Labels := by
      have ha : raw2904step3 = (fun i j => raw2904step2 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2904step3 raw2904step2; decide +kernel
      have hl : raw2904step3Labels = raw2904step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2904step2 raw2904step2Labels permutation7 permutation4
    mixedMoment B raw2904step3 raw2904step3Labels = mixedMoment B raw2904step4 raw2904step4Labels := by
      have ha : raw2904step4 = raw2904step3 := by apply Matrix.ext; unfold raw2904step4 raw2904step3; decide +kernel
      have hl : raw2904step3Labels = labelEmbedding7 ∘ raw2904step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2904step3 raw2904step3Labels raw2904step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5308 node5308Labels := by rfl

theorem canonical2905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2905 raw2905Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw2905 raw2905Labels = mixedMoment B raw2905step0 raw2905step0Labels := by
      have hz : ∀ j, raw2905 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2905step0 = (fun i j => raw2905 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2905step0 raw2905; decide +kernel
      have hl : raw2905step0Labels = raw2905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2905 raw2905Labels permutation434 hz
    mixedMoment B raw2905step0 raw2905step0Labels = mixedMoment B raw2905step1 raw2905step1Labels := by
      have hz : ∀ j, raw2905step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2905step1 = (fun i j => raw2905step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2905step1 raw2905step0; decide +kernel
      have hl : raw2905step1Labels = raw2905step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2905step0 raw2905step0Labels permutation80 hz
    mixedMoment B raw2905step1 raw2905step1Labels = mixedMoment B raw2905step2 raw2905step2Labels := by
      have ha : raw2905step2 = (fun i j => raw2905step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2905step2 raw2905step1; decide +kernel
      have hl : raw2905step2Labels = raw2905step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2905step1 raw2905step1Labels permutation29 permutation4
    mixedMoment B raw2905step2 raw2905step2Labels = mixedMoment B raw2905step3 raw2905step3Labels := by
      have ha : raw2905step3 = raw2905step2 := by apply Matrix.ext; unfold raw2905step3 raw2905step2; decide +kernel
      have hl : raw2905step2Labels = labelEmbedding7 ∘ raw2905step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2905step2 raw2905step2Labels raw2905step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

theorem canonical2906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2906 raw2906Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw2906 raw2906Labels = mixedMoment B raw2906step0 raw2906step0Labels := by
      have hz : ∀ j, raw2906 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2906step0 = (fun i j => raw2906 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2906step0 raw2906; decide +kernel
      have hl : raw2906step0Labels = raw2906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2906 raw2906Labels permutation434 hz
    mixedMoment B raw2906step0 raw2906step0Labels = mixedMoment B raw2906step1 raw2906step1Labels := by
      have hz : ∀ j, raw2906step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2906step1 = (fun i j => raw2906step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2906step1 raw2906step0; decide +kernel
      have hl : raw2906step1Labels = raw2906step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2906step0 raw2906step0Labels permutation56 hz
    mixedMoment B raw2906step1 raw2906step1Labels = mixedMoment B raw2906step2 raw2906step2Labels := by
      have ha : raw2906step2 = (fun i j => raw2906step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2906step2 raw2906step1; decide +kernel
      have hl : raw2906step2Labels = raw2906step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2906step1 raw2906step1Labels permutation29 permutation4
    mixedMoment B raw2906step2 raw2906step2Labels = mixedMoment B raw2906step3 raw2906step3Labels := by
      have ha : raw2906step3 = raw2906step2 := by apply Matrix.ext; unfold raw2906step3 raw2906step2; decide +kernel
      have hl : raw2906step2Labels = labelEmbedding7 ∘ raw2906step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2906step2 raw2906step2Labels raw2906step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

theorem canonical2907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2907 raw2907Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw2907 raw2907Labels = mixedMoment B raw2907step0 raw2907step0Labels := by
      have hz : ∀ j, raw2907 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2907step0 = (fun i j => raw2907 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2907step0 raw2907; decide +kernel
      have hl : raw2907step0Labels = raw2907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2907 raw2907Labels permutation346 hz
    mixedMoment B raw2907step0 raw2907step0Labels = mixedMoment B raw2907step1 raw2907step1Labels := by
      have hz : ∀ j, raw2907step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2907step1 = (fun i j => raw2907step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2907step1 raw2907step0; decide +kernel
      have hl : raw2907step1Labels = raw2907step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2907step0 raw2907step0Labels permutation56 hz
    mixedMoment B raw2907step1 raw2907step1Labels = mixedMoment B raw2907step2 raw2907step2Labels := by
      have ha : raw2907step2 = (fun i j => raw2907step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2907step2 raw2907step1; decide +kernel
      have hl : raw2907step2Labels = raw2907step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2907step1 raw2907step1Labels permutation29 permutation4
    mixedMoment B raw2907step2 raw2907step2Labels = mixedMoment B raw2907step3 raw2907step3Labels := by
      have ha : raw2907step3 = raw2907step2 := by apply Matrix.ext; unfold raw2907step3 raw2907step2; decide +kernel
      have hl : raw2907step2Labels = labelEmbedding7 ∘ raw2907step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2907step2 raw2907step2Labels raw2907step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

theorem canonical2908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2908 raw2908Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw2908 raw2908Labels = mixedMoment B raw2908step0 raw2908step0Labels := by
      have hz : ∀ j, raw2908 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2908step0 = (fun i j => raw2908 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2908step0 raw2908; decide +kernel
      have hl : raw2908step0Labels = raw2908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2908 raw2908Labels permutation434 hz
    mixedMoment B raw2908step0 raw2908step0Labels = mixedMoment B raw2908step1 raw2908step1Labels := by
      have hz : ∀ j, raw2908step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2908step1 = (fun i j => raw2908step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2908step1 raw2908step0; decide +kernel
      have hl : raw2908step1Labels = raw2908step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2908step0 raw2908step0Labels permutation80 hz
    mixedMoment B raw2908step1 raw2908step1Labels = mixedMoment B raw2908step2 raw2908step2Labels := by
      have hz : ∀ j, raw2908step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2908step2 = (fun i j => raw2908step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2908step2 raw2908step1; decide +kernel
      have hl : raw2908step2Labels = raw2908step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2908step1 raw2908step1Labels permutation14 hz
    mixedMoment B raw2908step2 raw2908step2Labels = mixedMoment B raw2908step3 raw2908step3Labels := by
      have ha : raw2908step3 = (fun i j => raw2908step2 (permutation6 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2908step3 raw2908step2; decide +kernel
      have hl : raw2908step3Labels = raw2908step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2908step2 raw2908step2Labels permutation6 permutation4
    mixedMoment B raw2908step3 raw2908step3Labels = mixedMoment B raw2908step4 raw2908step4Labels := by
      have ha : raw2908step4 = raw2908step3 := by apply Matrix.ext; unfold raw2908step4 raw2908step3; decide +kernel
      have hl : raw2908step3Labels = labelEmbedding7 ∘ raw2908step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2908step3 raw2908step3Labels raw2908step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

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

theorem canonical554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw554 raw554Labels = mixedMoment B node3916 node3916Labels := by
  calc
    mixedMoment B raw554 raw554Labels = mixedMoment B raw554step0 raw554step0Labels := by
      have ha : raw554step0 = (fun i j => raw554 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw554step0 raw554; decide +kernel
      have hl : raw554step0Labels = raw554Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw554 raw554Labels permutation2 permutation5
    mixedMoment B raw554step0 raw554step0Labels = mixedMoment B raw554step1 raw554step1Labels := by
      have ha : raw554step1 = raw554step0 := by apply Matrix.ext; unfold raw554step1 raw554step0; decide +kernel
      have hl : raw554step0Labels = labelEmbedding1 ∘ raw554step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw554step0 raw554step0Labels raw554step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3916 node3916Labels := by rfl

theorem canonical555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw555 raw555Labels = mixedMoment B node507 node507Labels := by
  calc
    mixedMoment B raw555 raw555Labels = mixedMoment B raw555step0 raw555step0Labels := by
      have ha : raw555step0 = (fun i j => raw555 (permutation5 i) (permutation2 j)) := by apply Matrix.ext; unfold raw555step0 raw555; decide +kernel
      have hl : raw555step0Labels = raw555Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw555 raw555Labels permutation5 permutation2
    _ = mixedMoment B node507 node507Labels := by rfl

theorem canonical626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw626 raw626Labels = mixedMoment B node4014 node4014Labels := by
  calc
    mixedMoment B raw626 raw626Labels = mixedMoment B raw626step0 raw626step0Labels := by
      have ha : raw626step0 = (fun i j => raw626 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw626step0 raw626; decide +kernel
      have hl : raw626step0Labels = raw626Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw626 raw626Labels permutation8 permutation5
    mixedMoment B raw626step0 raw626step0Labels = mixedMoment B raw626step1 raw626step1Labels := by
      have ha : raw626step1 = raw626step0 := by apply Matrix.ext; unfold raw626step1 raw626step0; decide +kernel
      have hl : raw626step0Labels = labelEmbedding1 ∘ raw626step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw626step0 raw626step0Labels raw626step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4014 node4014Labels := by rfl

theorem canonical627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw627 raw627Labels = mixedMoment B node527 node527Labels := by
  calc
    mixedMoment B raw627 raw627Labels = mixedMoment B raw627step0 raw627step0Labels := by
      have ha : raw627step0 = (fun i j => raw627 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw627step0 raw627; decide +kernel
      have hl : raw627step0Labels = raw627Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw627 raw627Labels permutation10 permutation4
    _ = mixedMoment B node527 node527Labels := by rfl

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

theorem canonical662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw662 raw662Labels = mixedMoment B node4094 node4094Labels := by
  calc
    _ = mixedMoment B node4094 node4094Labels := by rfl

theorem canonical663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw663 raw663Labels = mixedMoment B node6 node6Labels := by
  calc
    _ = mixedMoment B node6 node6Labels := by rfl

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

theorem canonical7731 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7731 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7731 = injectiveMoment H raw7731step0 := by
      have heq : raw7731step0 = (fun i j => raw7731 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7731 permutation11 permutation1
    _ = injectiveMoment H node65 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4943 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4943 = injectiveMoment H node227 := by
  rfl

theorem canonical4950 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4950 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw4950 = injectiveMoment H raw4950step0 := by
      have heq : raw4950step0 = raw4950.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4950).symm
    injectiveMoment H raw4950step0 = injectiveMoment H raw4950step1 := by
      have hz : ∀ i, raw4950step0 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw4950step1 = (fun i j => raw4950step0 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4950step0 permutation5 hz
    _ = injectiveMoment H node11 := by rfl

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

theorem sound227 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node227 = Sparse.eval value227 (momentVector H) := by
  have heq : pivotMatrix227 = (fun u v => node227 (pivotPermutation227 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node227 = injectiveMoment H pivotMatrix227 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix227 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix227 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix227 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix227 (0 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix227 (1 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix227 (1 : Fin 3) = raw4950 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4950 hH).trans (sound11 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix227 (2 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix227 (2 : Fin 3) = raw4956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4956 hH).trans (sound62 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node227 + (injectiveMoment H (mergeFirst pivotMatrix227 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix227 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix227 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value227, value11, value62, Sparse.eval] at hc ⊢
  linarith

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

theorem canonical4117 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4117 = injectiveMoment H node207 := by
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

theorem canonical7678 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7678 = injectiveMoment H node65 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair507 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node507 node507Labels = Sparse.eval singlePairValue507 (familyPairVector B) := by
  have hp := single_label_three B hB node507
  have hl : node507Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node507 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node507 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node507 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node507 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node507 (EqualityPatterns.family3.label 1) = PairSemantics.raw5214 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node507 PairSemantics.raw5214; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5214 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node507 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node507 (EqualityPatterns.family3.label 2) = PairSemantics.raw8985 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node507 PairSemantics.raw8985; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8985 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node507 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node507 (EqualityPatterns.family3.label 3) = PairSemantics.raw5183 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node507 PairSemantics.raw5183; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5183 hH).trans (PairSemantics.sound4 hH)
  have hm4 : familyPairMoment B (groupedColumns node507 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value41 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node507 (EqualityPatterns.family3.label 4) = PairSemantics.raw4141 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node507 PairSemantics.raw4141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4141 hH).trans (PairSemantics.sound41 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue507, PairSemantics.value0, PairSemantics.value4, PairSemantics.value41, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair527 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node527 node527Labels = Sparse.eval singlePairValue527 (familyPairVector B) := by
  have hp := single_label_three B hB node527
  have hl : node527Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node527 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node527 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node527 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node527 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node527 (EqualityPatterns.family3.label 1) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node527 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm2 : familyPairMoment B (groupedColumns node527 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node527 (EqualityPatterns.family3.label 2) = PairSemantics.raw7731 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node527 PairSemantics.raw7731; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7731 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node527 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node527 (EqualityPatterns.family3.label 3) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node527 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm4 : familyPairMoment B (groupedColumns node527 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value227 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node527 (EqualityPatterns.family3.label 4) = PairSemantics.raw4943 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node527 PairSemantics.raw4943; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4943 hH).trans (PairSemantics.sound227 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue527, PairSemantics.value0, PairSemantics.value4, PairSemantics.value65, PairSemantics.value227, Sparse.eval] at hp ⊢
  linarith only [hp]

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

theorem singleton2788 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2788 node2788Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node420 node420Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw284 singletonSmall2788
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2788) = raw284Labels := by decide +kernel
  rw [hl, canonical284 B hB] at h
  have hc0 : mixedMoment B raw284 (Fin.cases (0 : Fin 1) singletonSmall2788) =
      mixedMoment B node420 node420Labels := by
    have ha : raw284 = raw285 := by apply Matrix.ext; unfold raw284 raw285; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2788 = raw285Labels := by decide +kernel
    rw [ha, hj, canonical285 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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

theorem singleton3916 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3916 node3916Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node507 node507Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw554 singletonSmall3916
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3916) = raw554Labels := by decide +kernel
  rw [hl, canonical554 B hB] at h
  have hc0 : mixedMoment B raw554 (Fin.cases (0 : Fin 1) singletonSmall3916) =
      mixedMoment B node507 node507Labels := by
    have ha : raw554 = raw555 := by apply Matrix.ext; unfold raw554 raw555; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3916 = raw555Labels := by decide +kernel
    rw [ha, hj, canonical555 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4014 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4014 node4014Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node527 node527Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw626 singletonSmall4014
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4014) = raw626Labels := by decide +kernel
  rw [hl, canonical626 B hB] at h
  have hc0 : mixedMoment B raw626 (Fin.cases (0 : Fin 1) singletonSmall4014) =
      mixedMoment B node527 node527Labels := by
    have ha : raw626 = raw627 := by apply Matrix.ext; unfold raw626 raw627; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4014 = raw627Labels := by decide +kernel
    rw [ha, hj, canonical627 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

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

theorem singleton5310 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5310 node5310Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2788 node2788Labels + mixedMoment B node3633 node3633Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2325 singletonSmall5310
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5310) = raw2325Labels := by decide +kernel
  rw [hl, canonical2325 B hB] at h
  have hc0 : mixedMoment B raw2325 (Fin.cases (0 : Fin 2) singletonSmall5310) =
      mixedMoment B node2788 node2788Labels := by
    have ha : raw2325 = raw2326 := by apply Matrix.ext; unfold raw2325 raw2326; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5310 = raw2326Labels := by decide +kernel
    rw [ha, hj, canonical2326 B hB]
  have hc1 : mixedMoment B raw2325 (Fin.cases (1 : Fin 2) singletonSmall5310) =
      mixedMoment B node3633 node3633Labels := by
    have ha : raw2325 = raw2327 := by apply Matrix.ext; unfold raw2325 raw2327; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5310 = raw2327Labels := by decide +kernel
    rw [ha, hj, canonical2327 B hB]
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

theorem singleton5443 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5443 node5443Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3862 node3862Labels + mixedMoment B node3907 node3907Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2544 singletonSmall5443
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5443) = raw2544Labels := by decide +kernel
  rw [hl, canonical2544 B hB] at h
  have hc0 : mixedMoment B raw2544 (Fin.cases (0 : Fin 2) singletonSmall5443) =
      mixedMoment B node3862 node3862Labels := by
    have ha : raw2544 = raw2545 := by apply Matrix.ext; unfold raw2544 raw2545; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5443 = raw2545Labels := by decide +kernel
    rw [ha, hj, canonical2545 B hB]
  have hc1 : mixedMoment B raw2544 (Fin.cases (1 : Fin 2) singletonSmall5443) =
      mixedMoment B node3907 node3907Labels := by
    have ha : raw2544 = raw2546 := by apply Matrix.ext; unfold raw2544 raw2546; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5443 = raw2546Labels := by decide +kernel
    rw [ha, hj, canonical2546 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton5456 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5456 node5456Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3916 node3916Labels + mixedMoment B node3916 node3916Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2568 singletonSmall5456
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5456) = raw2568Labels := by decide +kernel
  rw [hl, canonical2568 B hB] at h
  have hc0 : mixedMoment B raw2568 (Fin.cases (0 : Fin 2) singletonSmall5456) =
      mixedMoment B node3916 node3916Labels := by
    have ha : raw2568 = raw2569 := by apply Matrix.ext; unfold raw2568 raw2569; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5456 = raw2569Labels := by decide +kernel
    rw [ha, hj, canonical2569 B hB]
  have hc1 : mixedMoment B raw2568 (Fin.cases (1 : Fin 2) singletonSmall5456) =
      mixedMoment B node3916 node3916Labels := by
    have ha : raw2568 = raw2570 := by apply Matrix.ext; unfold raw2568 raw2570; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5456 = raw2570Labels := by decide +kernel
    rw [ha, hj, canonical2570 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5491 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5491 node5491Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node4014 node4014Labels + mixedMoment B node4014 node4014Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2616 singletonSmall5491
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5491) = raw2616Labels := by decide +kernel
  rw [hl, canonical2616 B hB] at h
  have hc0 : mixedMoment B raw2616 (Fin.cases (0 : Fin 2) singletonSmall5491) =
      mixedMoment B node4014 node4014Labels := by
    have ha : raw2616 = raw2617 := by apply Matrix.ext; unfold raw2616 raw2617; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5491 = raw2617Labels := by decide +kernel
    rw [ha, hj, canonical2617 B hB]
  have hc1 : mixedMoment B raw2616 (Fin.cases (1 : Fin 2) singletonSmall5491) =
      mixedMoment B node4014 node4014Labels := by
    have ha : raw2616 = raw2618 := by apply Matrix.ext; unfold raw2616 raw2618; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5491 = raw2618Labels := by decide +kernel
    rw [ha, hj, canonical2618 B hB]
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

theorem zero5441 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5441 node5441Labels = 0 := by
  exact mixedMoment_order_one B hB node5441 node5441Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5455 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5455 node5455Labels = 0 := by
  exact mixedMoment_order_one B hB node5455 node5455Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5496 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5496 node5496Labels = 0 := by
  exact mixedMoment_order_one B hB node5496 node5496Labels 1
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

theorem sound420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node420 node420Labels = Sparse.eval nodeValue420 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue420 (familyPairVector B) := singlePair420 B _hB
    _ = _ := by norm_num [singlePairValue420, nodeValue420, Sparse.eval, mixedVector] <;> ring

theorem sound496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node496 node496Labels = Sparse.eval nodeValue496 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue496 (familyPairVector B) := singlePair496 B _hB
    _ = _ := by norm_num [singlePairValue496, nodeValue496, Sparse.eval, mixedVector] <;> ring

theorem sound505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node505 node505Labels = Sparse.eval nodeValue505 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue505 (familyPairVector B) := singlePair505 B _hB
    _ = _ := by norm_num [singlePairValue505, nodeValue505, Sparse.eval, mixedVector] <;> ring

theorem sound2788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2788 node2788Labels = Sparse.eval nodeValue2788 (mixedVector B) := by
  have h := singleton2788 B _hB
  rw [sound420 B _hB _hF] at h
  norm_num [nodeValue2788, nodeValue420, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3633 node3633Labels = Sparse.eval nodeValue3633 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3633) = mixedMoment B node3633 node3633Labels := rfl
  simpa [nodeValue3633, Sparse.eval] using hc.symm

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

theorem sound3912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3912 node3912Labels = Sparse.eval nodeValue3912 (mixedVector B) := by
  have h := singleton3912 B _hB
  rw [sound505 B _hB _hF] at h
  norm_num [nodeValue3912, nodeValue505, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5310 node5310Labels = Sparse.eval nodeValue5310 (mixedVector B) := by
  have h := singleton5310 B _hB
  rw [sound2788 B _hB _hF, sound3633 B _hB _hF] at h
  norm_num [nodeValue5310, nodeValue2788, nodeValue3633, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5443 node5443Labels = Sparse.eval nodeValue5443 (mixedVector B) := by
  have h := singleton5443 B _hB
  rw [sound3862 B _hB _hF, sound3907 B _hB _hF] at h
  norm_num [nodeValue5443, nodeValue3862, nodeValue3907, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5453 node5453Labels = Sparse.eval nodeValue5453 (mixedVector B) := by
  have h := singleton5453 B _hB
  rw [sound3912 B _hB _hF] at h
  norm_num [nodeValue5453, nodeValue3912, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5455 node5455Labels = Sparse.eval nodeValue5455 (mixedVector B) := by
  simpa only [nodeValue5455, Sparse.eval_nil] using zero5455 B _hB _hF

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

theorem sound6 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node6 node6Labels = Sparse.eval nodeValue6 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue6 (familyPairVector B) := singlePair6 B _hB
    _ = _ := by norm_num [singlePairValue6, nodeValue6, Sparse.eval, mixedVector]

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

theorem sound507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node507 node507Labels = Sparse.eval nodeValue507 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue507 (familyPairVector B) := singlePair507 B _hB
    _ = _ := by norm_num [singlePairValue507, nodeValue507, Sparse.eval, mixedVector] <;> ring

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

theorem sound527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node527 node527Labels = Sparse.eval nodeValue527 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue527 (familyPairVector B) := singlePair527 B _hB
    _ = _ := by norm_num [singlePairValue527, nodeValue527, Sparse.eval, mixedVector]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3916 node3916Labels = Sparse.eval nodeValue3916 (mixedVector B) := by
  have h := singleton3916 B _hB
  rw [sound507 B _hB _hF] at h
  norm_num [nodeValue3916, nodeValue507, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4014 node4014Labels = Sparse.eval nodeValue4014 (mixedVector B) := by
  have h := singleton4014 B _hB
  rw [sound527 B _hB _hF] at h
  norm_num [nodeValue4014, nodeValue527, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4094 node4094Labels = Sparse.eval nodeValue4094 (mixedVector B) := by
  have h := singleton4094 B _hB
  rw [sound6 B _hB _hF] at h
  norm_num [nodeValue4094, nodeValue6, Sparse.eval] at h ⊢
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

theorem zero5308 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5308 node5308Labels = 0 := by
  exact mixedMoment_order_one B hB node5308 node5308Labels 1
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

theorem sound5306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5306 node5306Labels = Sparse.eval nodeValue5306 (mixedVector B) := by
  have h := singleton5306 B _hB
  rw [sound2784 B _hB _hF, sound3623 B _hB _hF] at h
  norm_num [nodeValue5306, nodeValue2784, nodeValue3623, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5308 node5308Labels = Sparse.eval nodeValue5308 (mixedVector B) := by
  simpa only [nodeValue5308, Sparse.eval_nil] using zero5308 B _hB _hF

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

theorem sound5441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5441 node5441Labels = Sparse.eval nodeValue5441 (mixedVector B) := by
  simpa only [nodeValue5441, Sparse.eval_nil] using zero5441 B _hB _hF

theorem sound5456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5456 node5456Labels = Sparse.eval nodeValue5456 (mixedVector B) := by
  have h := singleton5456 B _hB
  rw [sound3916 B _hB _hF] at h
  norm_num [nodeValue5456, nodeValue3916, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5491 node5491Labels = Sparse.eval nodeValue5491 (mixedVector B) := by
  have h := singleton5491 B _hB
  rw [sound4014 B _hB _hF] at h
  norm_num [nodeValue5491, nodeValue4014, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5496 node5496Labels = Sparse.eval nodeValue5496 (mixedVector B) := by
  simpa only [nodeValue5496, Sparse.eval_nil] using zero5496 B _hB _hF

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

theorem sourceEq10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm10 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA10 + difference 0 1) (sourceB10 + difference 1 0) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA10 + difference 0 1) (sourceB10 + difference 1 0) sourceC10) = raw2881 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2881; decide +kernel
    rw [ha]
    exact (canonical2881 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA10 + difference 0 2) (sourceB10 + difference 2 0) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA10 + difference 0 2) (sourceB10 + difference 2 0) sourceC10) = raw2882 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2882; decide +kernel
    rw [ha]
    exact (canonical2882 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA10 + difference 0 3) (sourceB10 + difference 3 0) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA10 + difference 0 3) (sourceB10 + difference 3 0) sourceC10) = raw2883 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2883; decide +kernel
    rw [ha]
    exact (canonical2883 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA10 + difference 0 4) (sourceB10 + difference 4 0) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5456) := by
    have ha : (tripleCharges (sourceA10 + difference 0 4) (sourceB10 + difference 4 0) sourceC10) = raw2884 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2884; decide +kernel
    rw [ha]
    exact (canonical2884 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA10 + difference 0 5) (sourceB10 + difference 5 0) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA10 + difference 0 5) (sourceB10 + difference 5 0) sourceC10) = raw2885 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2885; decide +kernel
    rw [ha]
    exact (canonical2885 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA10 + difference 1 0) (sourceB10 + difference 0 1) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA10 + difference 1 0) (sourceB10 + difference 0 1) sourceC10) = raw2886 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2886; decide +kernel
    rw [ha]
    exact (canonical2886 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA10 + difference 1 2) (sourceB10 + difference 2 1) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA10 + difference 1 2) (sourceB10 + difference 2 1) sourceC10) = raw2887 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2887; decide +kernel
    rw [ha]
    exact (canonical2887 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA10 + difference 1 3) (sourceB10 + difference 3 1) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA10 + difference 1 3) (sourceB10 + difference 3 1) sourceC10) = raw2888 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2888; decide +kernel
    rw [ha]
    exact (canonical2888 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA10 + difference 1 4) (sourceB10 + difference 4 1) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA10 + difference 1 4) (sourceB10 + difference 4 1) sourceC10) = raw2889 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2889; decide +kernel
    rw [ha]
    exact (canonical2889 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA10 + difference 1 5) (sourceB10 + difference 5 1) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA10 + difference 1 5) (sourceB10 + difference 5 1) sourceC10) = raw2890 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2890; decide +kernel
    rw [ha]
    exact (canonical2890 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA10 + difference 2 0) (sourceB10 + difference 0 2) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA10 + difference 2 0) (sourceB10 + difference 0 2) sourceC10) = raw2891 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2891; decide +kernel
    rw [ha]
    exact (canonical2891 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA10 + difference 2 1) (sourceB10 + difference 1 2) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA10 + difference 2 1) (sourceB10 + difference 1 2) sourceC10) = raw2892 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2892; decide +kernel
    rw [ha]
    exact (canonical2892 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA10 + difference 2 3) (sourceB10 + difference 3 2) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA10 + difference 2 3) (sourceB10 + difference 3 2) sourceC10) = raw2893 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2893; decide +kernel
    rw [ha]
    exact (canonical2893 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA10 + difference 2 4) (sourceB10 + difference 4 2) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA10 + difference 2 4) (sourceB10 + difference 4 2) sourceC10) = raw2894 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2894; decide +kernel
    rw [ha]
    exact (canonical2894 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA10 + difference 2 5) (sourceB10 + difference 5 2) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA10 + difference 2 5) (sourceB10 + difference 5 2) sourceC10) = raw2895 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2895; decide +kernel
    rw [ha]
    exact (canonical2895 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA10 + difference 3 0) (sourceB10 + difference 0 3) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA10 + difference 3 0) (sourceB10 + difference 0 3) sourceC10) = raw2896 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2896; decide +kernel
    rw [ha]
    exact (canonical2896 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA10 + difference 3 1) (sourceB10 + difference 1 3) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA10 + difference 3 1) (sourceB10 + difference 1 3) sourceC10) = raw2897 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2897; decide +kernel
    rw [ha]
    exact (canonical2897 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA10 + difference 3 2) (sourceB10 + difference 2 3) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA10 + difference 3 2) (sourceB10 + difference 2 3) sourceC10) = raw2898 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2898; decide +kernel
    rw [ha]
    exact (canonical2898 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA10 + difference 3 4) (sourceB10 + difference 4 3) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA10 + difference 3 4) (sourceB10 + difference 4 3) sourceC10) = raw2899 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2899; decide +kernel
    rw [ha]
    exact (canonical2899 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA10 + difference 3 5) (sourceB10 + difference 5 3) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA10 + difference 3 5) (sourceB10 + difference 5 3) sourceC10) = raw2900 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2900; decide +kernel
    rw [ha]
    exact (canonical2900 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA10 + difference 4 0) (sourceB10 + difference 0 4) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4094) := by
    have ha : (tripleCharges (sourceA10 + difference 4 0) (sourceB10 + difference 0 4) sourceC10) = raw2901 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2901; decide +kernel
    rw [ha]
    exact (canonical2901 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA10 + difference 4 1) (sourceB10 + difference 1 4) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA10 + difference 4 1) (sourceB10 + difference 1 4) sourceC10) = raw2843 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2843; decide +kernel
    rw [ha]
    exact (canonical2843 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA10 + difference 4 2) (sourceB10 + difference 2 4) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA10 + difference 4 2) (sourceB10 + difference 2 4) sourceC10) = raw2902 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2902; decide +kernel
    rw [ha]
    exact (canonical2902 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA10 + difference 4 3) (sourceB10 + difference 3 4) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA10 + difference 4 3) (sourceB10 + difference 3 4) sourceC10) = raw2903 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2903; decide +kernel
    rw [ha]
    exact (canonical2903 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA10 + difference 4 5) (sourceB10 + difference 5 4) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5496) := by
    have ha : (tripleCharges (sourceA10 + difference 4 5) (sourceB10 + difference 5 4) sourceC10) = raw2825 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2825; decide +kernel
    rw [ha]
    exact (canonical2825 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA10 + difference 5 0) (sourceB10 + difference 0 5) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA10 + difference 5 0) (sourceB10 + difference 0 5) sourceC10) = raw2904 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2904; decide +kernel
    rw [ha]
    exact (canonical2904 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA10 + difference 5 1) (sourceB10 + difference 1 5) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA10 + difference 5 1) (sourceB10 + difference 1 5) sourceC10) = raw2905 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2905; decide +kernel
    rw [ha]
    exact (canonical2905 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA10 + difference 5 2) (sourceB10 + difference 2 5) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA10 + difference 5 2) (sourceB10 + difference 2 5) sourceC10) = raw2906 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2906; decide +kernel
    rw [ha]
    exact (canonical2906 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA10 + difference 5 3) (sourceB10 + difference 3 5) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA10 + difference 5 3) (sourceB10 + difference 3 5) sourceC10) = raw2907 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2907; decide +kernel
    rw [ha]
    exact (canonical2907 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA10 + difference 5 4) (sourceB10 + difference 4 5) sourceC10) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA10 + difference 5 4) (sourceB10 + difference 4 5) sourceC10) = raw2908 := by
      apply Matrix.ext; unfold tripleCharges sourceA10 sourceB10 sourceC10 difference raw2908; decide +kernel
    rw [ha]
    exact (canonical2908 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA10 sourceB10 sourceC10
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm10, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck10 : Integer.Sparse.reindex keyMap MixedData.row10 = numericRow10 := by decide +kernel

theorem numericCheck10 (x : Master → ℝ) : Integer.Sparse.eval numericRow10 x =
    (40 : ℝ) * reducedSource10 x := by
  norm_num [numericRow10, reducedSource10, Integer.Sparse.eval, Sparse.eval, nodeValue4094, nodeValue5306, nodeValue5308, nodeValue5310, nodeValue5439, nodeValue5441, nodeValue5443, nodeValue5453, nodeValue5455, nodeValue5456, nodeValue5491, nodeValue5496]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero10 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource10 (mixedVector B) = 0 := by
  have h4094 : mixedVector B (Sum.inr 4094) = Sparse.eval nodeValue4094 (mixedVector B) := by
    change mixedMoment B node4094 node4094Labels = _
    exact sound4094 B hB hF
  have h5306 : mixedVector B (Sum.inr 5306) = Sparse.eval nodeValue5306 (mixedVector B) := by
    change mixedMoment B node5306 node5306Labels = _
    exact sound5306 B hB hF
  have h5308 : mixedVector B (Sum.inr 5308) = Sparse.eval nodeValue5308 (mixedVector B) := by
    change mixedMoment B node5308 node5308Labels = _
    exact sound5308 B hB hF
  have h5310 : mixedVector B (Sum.inr 5310) = Sparse.eval nodeValue5310 (mixedVector B) := by
    change mixedMoment B node5310 node5310Labels = _
    exact sound5310 B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439_e B hB hF
  have h5441 : mixedVector B (Sum.inr 5441) = Sparse.eval nodeValue5441 (mixedVector B) := by
    change mixedMoment B node5441 node5441Labels = _
    exact sound5441 B hB hF
  have h5443 : mixedVector B (Sum.inr 5443) = Sparse.eval nodeValue5443 (mixedVector B) := by
    change mixedMoment B node5443 node5443Labels = _
    exact sound5443 B hB hF
  have h5453 : mixedVector B (Sum.inr 5453) = Sparse.eval nodeValue5453 (mixedVector B) := by
    change mixedMoment B node5453 node5453Labels = _
    exact sound5453 B hB hF
  have h5455 : mixedVector B (Sum.inr 5455) = Sparse.eval nodeValue5455 (mixedVector B) := by
    change mixedMoment B node5455 node5455Labels = _
    exact sound5455 B hB hF
  have h5456 : mixedVector B (Sum.inr 5456) = Sparse.eval nodeValue5456 (mixedVector B) := by
    change mixedMoment B node5456 node5456Labels = _
    exact sound5456 B hB hF
  have h5491 : mixedVector B (Sum.inr 5491) = Sparse.eval nodeValue5491 (mixedVector B) := by
    change mixedMoment B node5491 node5491Labels = _
    exact sound5491 B hB hF
  have h5496 : mixedVector B (Sum.inr 5496) = Sparse.eval nodeValue5496 (mixedVector B) := by
    change mixedMoment B node5496 node5496Labels = _
    exact sound5496 B hB hF
  simpa only [sourceForm10, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4094, h5306, h5308, h5310, h5439, h5441, h5443, h5453, h5455, h5456, h5491, h5496, reducedSource10] using sourceEq10 B hB

theorem rowSound10_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row10 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck10, numericCheck10, reducedZero10 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound10_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound10_e_oai
