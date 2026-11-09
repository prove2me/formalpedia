-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T19:49:28.531216+00:00
-- url     : https://prove2.me/submissions/4670c92c-6c6d-4e30-82ab-bf47ede09119

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E114
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5174_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical78 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw78 raw78Labels = mixedMoment B node1301 node1301Labels := by
  calc
    mixedMoment B raw78 raw78Labels = mixedMoment B raw78step0 raw78step0Labels := by
      have ha : raw78step0 = (fun i j => raw78 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw78step0 raw78; decide +kernel
      have hl : raw78step0Labels = raw78Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw78 raw78Labels permutation8 permutation5
    mixedMoment B raw78step0 raw78step0Labels = mixedMoment B raw78step1 raw78step1Labels := by
      have ha : raw78step1 = raw78step0 := by apply Matrix.ext; unfold raw78step1 raw78step0; decide +kernel
      have hl : raw78step0Labels = labelEmbedding1 ∘ raw78step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw78step0 raw78step0Labels raw78step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1301 node1301Labels := by rfl

theorem canonical79 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw79 raw79Labels = mixedMoment B node157 node157Labels := by
  calc
    mixedMoment B raw79 raw79Labels = mixedMoment B raw79step0 raw79step0Labels := by
      have ha : raw79step0 = (fun i j => raw79 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw79step0 raw79; decide +kernel
      have hl : raw79step0Labels = raw79Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw79 raw79Labels permutation10 permutation4
    _ = mixedMoment B node157 node157Labels := by rfl

theorem canonical92 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw92 raw92Labels = mixedMoment B node1312 node1312Labels := by
  calc
    mixedMoment B raw92 raw92Labels = mixedMoment B raw92step0 raw92step0Labels := by
      have ha : raw92step0 = (fun i j => raw92 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw92step0 raw92; decide +kernel
      have hl : raw92step0Labels = raw92Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw92 raw92Labels permutation2 permutation5
    mixedMoment B raw92step0 raw92step0Labels = mixedMoment B raw92step1 raw92step1Labels := by
      have ha : raw92step1 = raw92step0 := by apply Matrix.ext; unfold raw92step1 raw92step0; decide +kernel
      have hl : raw92step0Labels = labelEmbedding1 ∘ raw92step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw92step0 raw92step0Labels raw92step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1312 node1312Labels := by rfl

theorem canonical93 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw93 raw93Labels = mixedMoment B node161 node161Labels := by
  calc
    mixedMoment B raw93 raw93Labels = mixedMoment B raw93step0 raw93step0Labels := by
      have ha : raw93step0 = (fun i j => raw93 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw93step0 raw93; decide +kernel
      have hl : raw93step0Labels = raw93Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw93 raw93Labels permutation2 permutation4
    _ = mixedMoment B node161 node161Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical1280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1280 raw1280Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw1280 raw1280Labels = mixedMoment B raw1280step0 raw1280step0Labels := by
      have ha : raw1280step0 = (fun i j => raw1280 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1280step0 raw1280; decide +kernel
      have hl : raw1280step0Labels = raw1280Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1280 raw1280Labels permutation2 permutation6
    mixedMoment B raw1280step0 raw1280step0Labels = mixedMoment B raw1280step1 raw1280step1Labels := by
      have ha : raw1280step1 = -raw1280step0 := by apply Matrix.ext; change ∀ i j, raw1280step1 i j = -(raw1280step0 i j); unfold raw1280step1 raw1280step0; decide +kernel
      have hl : raw1280step1Labels = raw1280step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1280step1 raw1280step1Labels = mixedMoment B raw1280step2 raw1280step2Labels := by
      have ha : raw1280step2 = raw1280step1 := by apply Matrix.ext; unfold raw1280step2 raw1280step1; decide +kernel
      have hl : raw1280step1Labels = labelEmbedding1 ∘ raw1280step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1280step1 raw1280step1Labels raw1280step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1752 node1752Labels := by rfl

theorem canonical1371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1371 raw1371Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw1371 raw1371Labels = mixedMoment B raw1371step0 raw1371step0Labels := by
      have ha : raw1371step0 = (fun i j => raw1371 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1371step0 raw1371; decide +kernel
      have hl : raw1371step0Labels = raw1371Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1371 raw1371Labels permutation32 permutation4
    mixedMoment B raw1371step0 raw1371step0Labels = mixedMoment B raw1371step1 raw1371step1Labels := by
      have ha : raw1371step1 = raw1371step0 := by apply Matrix.ext; unfold raw1371step1 raw1371step0; decide +kernel
      have hl : raw1371step0Labels = labelEmbedding7 ∘ raw1371step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1371step0 raw1371step0Labels raw1371step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4546 node4546Labels := by rfl

theorem canonical1372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1372 raw1372Labels = mixedMoment B node1131 node1131Labels := by
  calc
    mixedMoment B raw1372 raw1372Labels = mixedMoment B raw1372step0 raw1372step0Labels := by
      have ha : raw1372step0 = (fun i j => raw1372 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1372step0 raw1372; decide +kernel
      have hl : raw1372step0Labels = raw1372Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1372 raw1372Labels permutation32 permutation4
    _ = mixedMoment B node1131 node1131Labels := by rfl

theorem canonical1373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1373 raw1373Labels = mixedMoment B node3264 node3264Labels := by
  calc
    mixedMoment B raw1373 raw1373Labels = mixedMoment B raw1373step0 raw1373step0Labels := by
      have ha : raw1373step0 = (fun i j => raw1373 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1373step0 raw1373; decide +kernel
      have hl : raw1373step0Labels = raw1373Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1373 raw1373Labels permutation32 permutation6
    mixedMoment B raw1373step0 raw1373step0Labels = mixedMoment B raw1373step1 raw1373step1Labels := by
      have ha : raw1373step1 = -raw1373step0 := by apply Matrix.ext; change ∀ i j, raw1373step1 i j = -(raw1373step0 i j); unfold raw1373step1 raw1373step0; decide +kernel
      have hl : raw1373step1Labels = raw1373step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1373step1 raw1373step1Labels = mixedMoment B raw1373step2 raw1373step2Labels := by
      have ha : raw1373step2 = raw1373step1 := by apply Matrix.ext; unfold raw1373step2 raw1373step1; decide +kernel
      have hl : raw1373step1Labels = labelEmbedding1 ∘ raw1373step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1373step1 raw1373step1Labels raw1373step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3264 node3264Labels := by rfl

theorem canonical1395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1395 raw1395Labels = mixedMoment B node4558 node4558Labels := by
  calc
    mixedMoment B raw1395 raw1395Labels = mixedMoment B raw1395step0 raw1395step0Labels := by
      have ha : raw1395step0 = (fun i j => raw1395 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1395step0 raw1395; decide +kernel
      have hl : raw1395step0Labels = raw1395Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1395 raw1395Labels permutation8 permutation4
    mixedMoment B raw1395step0 raw1395step0Labels = mixedMoment B raw1395step1 raw1395step1Labels := by
      have ha : raw1395step1 = raw1395step0 := by apply Matrix.ext; unfold raw1395step1 raw1395step0; decide +kernel
      have hl : raw1395step0Labels = labelEmbedding7 ∘ raw1395step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1395step0 raw1395step0Labels raw1395step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4558 node4558Labels := by rfl

theorem canonical1396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1396 raw1396Labels = mixedMoment B node1144 node1144Labels := by
  calc
    mixedMoment B raw1396 raw1396Labels = mixedMoment B raw1396step0 raw1396step0Labels := by
      have ha : raw1396step0 = (fun i j => raw1396 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1396step0 raw1396; decide +kernel
      have hl : raw1396step0Labels = raw1396Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1396 raw1396Labels permutation8 permutation4
    _ = mixedMoment B node1144 node1144Labels := by rfl

theorem canonical1397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1397 raw1397Labels = mixedMoment B node3276 node3276Labels := by
  calc
    mixedMoment B raw1397 raw1397Labels = mixedMoment B raw1397step0 raw1397step0Labels := by
      have ha : raw1397step0 = (fun i j => raw1397 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1397step0 raw1397; decide +kernel
      have hl : raw1397step0Labels = raw1397Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1397 raw1397Labels permutation8 permutation6
    mixedMoment B raw1397step0 raw1397step0Labels = mixedMoment B raw1397step1 raw1397step1Labels := by
      have ha : raw1397step1 = -raw1397step0 := by apply Matrix.ext; change ∀ i j, raw1397step1 i j = -(raw1397step0 i j); unfold raw1397step1 raw1397step0; decide +kernel
      have hl : raw1397step1Labels = raw1397step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1397step1 raw1397step1Labels = mixedMoment B raw1397step2 raw1397step2Labels := by
      have ha : raw1397step2 = raw1397step1 := by apply Matrix.ext; unfold raw1397step2 raw1397step1; decide +kernel
      have hl : raw1397step1Labels = labelEmbedding1 ∘ raw1397step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1397step1 raw1397step1Labels raw1397step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3276 node3276Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical1455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1455 raw1455Labels = mixedMoment B node4624 node4624Labels := by
  calc
    mixedMoment B raw1455 raw1455Labels = mixedMoment B raw1455step0 raw1455step0Labels := by
      have ha : raw1455step0 = (fun i j => raw1455 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1455step0 raw1455; decide +kernel
      have hl : raw1455step0Labels = raw1455Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1455 raw1455Labels permutation8 permutation4
    mixedMoment B raw1455step0 raw1455step0Labels = mixedMoment B raw1455step1 raw1455step1Labels := by
      have ha : raw1455step1 = raw1455step0 := by apply Matrix.ext; unfold raw1455step1 raw1455step0; decide +kernel
      have hl : raw1455step0Labels = labelEmbedding7 ∘ raw1455step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1455step0 raw1455step0Labels raw1455step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4624 node4624Labels := by rfl

theorem canonical1456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1456 raw1456Labels = mixedMoment B node1301 node1301Labels := by
  calc
    mixedMoment B raw1456 raw1456Labels = mixedMoment B raw1456step0 raw1456step0Labels := by
      have ha : raw1456step0 = (fun i j => raw1456 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1456step0 raw1456; decide +kernel
      have hl : raw1456step0Labels = raw1456Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1456 raw1456Labels permutation8 permutation4
    _ = mixedMoment B node1301 node1301Labels := by rfl

theorem canonical1457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1457 raw1457Labels = mixedMoment B node3309 node3309Labels := by
  calc
    mixedMoment B raw1457 raw1457Labels = mixedMoment B raw1457step0 raw1457step0Labels := by
      have ha : raw1457step0 = (fun i j => raw1457 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1457step0 raw1457; decide +kernel
      have hl : raw1457step0Labels = raw1457Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1457 raw1457Labels permutation10 permutation3
    mixedMoment B raw1457step0 raw1457step0Labels = mixedMoment B raw1457step1 raw1457step1Labels := by
      have ha : raw1457step1 = -raw1457step0 := by apply Matrix.ext; change ∀ i j, raw1457step1 i j = -(raw1457step0 i j); unfold raw1457step1 raw1457step0; decide +kernel
      have hl : raw1457step1Labels = raw1457step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1457step1 raw1457step1Labels = mixedMoment B raw1457step2 raw1457step2Labels := by
      have ha : raw1457step2 = raw1457step1 := by apply Matrix.ext; unfold raw1457step2 raw1457step1; decide +kernel
      have hl : raw1457step1Labels = labelEmbedding1 ∘ raw1457step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1457step1 raw1457step1Labels raw1457step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3309 node3309Labels := by rfl

theorem canonical1464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1464 raw1464Labels = mixedMoment B node4628 node4628Labels := by
  calc
    mixedMoment B raw1464 raw1464Labels = mixedMoment B raw1464step0 raw1464step0Labels := by
      have ha : raw1464step0 = (fun i j => raw1464 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1464step0 raw1464; decide +kernel
      have hl : raw1464step0Labels = raw1464Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1464 raw1464Labels permutation2 permutation4
    mixedMoment B raw1464step0 raw1464step0Labels = mixedMoment B raw1464step1 raw1464step1Labels := by
      have ha : raw1464step1 = raw1464step0 := by apply Matrix.ext; unfold raw1464step1 raw1464step0; decide +kernel
      have hl : raw1464step0Labels = labelEmbedding7 ∘ raw1464step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1464step0 raw1464step0Labels raw1464step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4628 node4628Labels := by rfl

theorem canonical1465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1465 raw1465Labels = mixedMoment B node1312 node1312Labels := by
  calc
    mixedMoment B raw1465 raw1465Labels = mixedMoment B raw1465step0 raw1465step0Labels := by
      have ha : raw1465step0 = (fun i j => raw1465 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1465step0 raw1465; decide +kernel
      have hl : raw1465step0Labels = raw1465Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1465 raw1465Labels permutation2 permutation4
    _ = mixedMoment B node1312 node1312Labels := by rfl

theorem canonical1466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1466 raw1466Labels = mixedMoment B node3312 node3312Labels := by
  calc
    mixedMoment B raw1466 raw1466Labels = mixedMoment B raw1466step0 raw1466step0Labels := by
      have ha : raw1466step0 = (fun i j => raw1466 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1466step0 raw1466; decide +kernel
      have hl : raw1466step0Labels = raw1466Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1466 raw1466Labels permutation2 permutation3
    mixedMoment B raw1466step0 raw1466step0Labels = mixedMoment B raw1466step1 raw1466step1Labels := by
      have ha : raw1466step1 = -raw1466step0 := by apply Matrix.ext; change ∀ i j, raw1466step1 i j = -(raw1466step0 i j); unfold raw1466step1 raw1466step0; decide +kernel
      have hl : raw1466step1Labels = raw1466step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1466step1 raw1466step1Labels = mixedMoment B raw1466step2 raw1466step2Labels := by
      have ha : raw1466step2 = raw1466step1 := by apply Matrix.ext; unfold raw1466step2 raw1466step1; decide +kernel
      have hl : raw1466step1Labels = labelEmbedding1 ∘ raw1466step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1466step1 raw1466step1Labels raw1466step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3312 node3312Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19719 raw19719Labels = mixedMoment B node4181 node4181Labels := by
  calc
    mixedMoment B raw19719 raw19719Labels = mixedMoment B raw19719step0 raw19719step0Labels := by
      have hz : ∀ j, raw19719 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19719step0 = (fun i j => raw19719 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19719step0 raw19719; decide +kernel
      have hl : raw19719step0Labels = raw19719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19719 raw19719Labels permutation434 hz
    mixedMoment B raw19719step0 raw19719step0Labels = mixedMoment B raw19719step1 raw19719step1Labels := by
      have hz : ∀ j, raw19719step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19719step1 = (fun i j => raw19719step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19719step1 raw19719step0; decide +kernel
      have hl : raw19719step1Labels = raw19719step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19719step0 raw19719step0Labels permutation80 hz
    mixedMoment B raw19719step1 raw19719step1Labels = mixedMoment B raw19719step2 raw19719step2Labels := by
      have hz : ∀ j, raw19719step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19719step2 = (fun i j => raw19719step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19719step2 raw19719step1; decide +kernel
      have hl : raw19719step2Labels = raw19719step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19719step1 raw19719step1Labels permutation14 hz
    mixedMoment B raw19719step2 raw19719step2Labels = mixedMoment B raw19719step3 raw19719step3Labels := by
      have ha : raw19719step3 = (fun i j => raw19719step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19719step3 raw19719step2; decide +kernel
      have hl : raw19719step3Labels = raw19719step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19719step2 raw19719step2Labels permutation2 permutation3
    mixedMoment B raw19719step3 raw19719step3Labels = mixedMoment B raw19719step4 raw19719step4Labels := by
      have ha : raw19719step4 = raw19719step3 := by apply Matrix.ext; unfold raw19719step4 raw19719step3; decide +kernel
      have hl : raw19719step3Labels = labelEmbedding6 ∘ raw19719step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19719step3 raw19719step3Labels raw19719step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4181 node4181Labels := by rfl

theorem canonical19720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19720 raw19720Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw19720 raw19720Labels = mixedMoment B raw19720step0 raw19720step0Labels := by
      have hz : ∀ j, raw19720 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19720step0 = (fun i j => raw19720 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19720step0 raw19720; decide +kernel
      have hl : raw19720step0Labels = raw19720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19720 raw19720Labels permutation434 hz
    mixedMoment B raw19720step0 raw19720step0Labels = mixedMoment B raw19720step1 raw19720step1Labels := by
      have hz : ∀ j, raw19720step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19720step1 = (fun i j => raw19720step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19720step1 raw19720step0; decide +kernel
      have hl : raw19720step1Labels = raw19720step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19720step0 raw19720step0Labels permutation80 hz
    mixedMoment B raw19720step1 raw19720step1Labels = mixedMoment B raw19720step2 raw19720step2Labels := by
      have ha : raw19720step2 = (fun i j => raw19720step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19720step2 raw19720step1; decide +kernel
      have hl : raw19720step2Labels = raw19720step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19720step1 raw19720step1Labels permutation31 permutation3
    mixedMoment B raw19720step2 raw19720step2Labels = mixedMoment B raw19720step3 raw19720step3Labels := by
      have ha : raw19720step3 = -raw19720step2 := by apply Matrix.ext; change ∀ i j, raw19720step3 i j = -(raw19720step2 i j); unfold raw19720step3 raw19720step2; decide +kernel
      have hl : raw19720step3Labels = raw19720step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19720step3 raw19720step3Labels = mixedMoment B raw19720step4 raw19720step4Labels := by
      have ha : raw19720step4 = raw19720step3 := by apply Matrix.ext; unfold raw19720step4 raw19720step3; decide +kernel
      have hl : raw19720step3Labels = labelEmbedding6 ∘ raw19720step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19720step3 raw19720step3Labels raw19720step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4356 node4356Labels := by rfl

theorem canonical19721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19721 raw19721Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw19721 raw19721Labels = mixedMoment B raw19721step0 raw19721step0Labels := by
      have hz : ∀ j, raw19721 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19721step0 = (fun i j => raw19721 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19721step0 raw19721; decide +kernel
      have hl : raw19721step0Labels = raw19721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19721 raw19721Labels permutation434 hz
    mixedMoment B raw19721step0 raw19721step0Labels = mixedMoment B raw19721step1 raw19721step1Labels := by
      have hz : ∀ j, raw19721step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19721step1 = (fun i j => raw19721step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19721step1 raw19721step0; decide +kernel
      have hl : raw19721step1Labels = raw19721step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19721step0 raw19721step0Labels permutation56 hz
    mixedMoment B raw19721step1 raw19721step1Labels = mixedMoment B raw19721step2 raw19721step2Labels := by
      have ha : raw19721step2 = (fun i j => raw19721step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19721step2 raw19721step1; decide +kernel
      have hl : raw19721step2Labels = raw19721step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19721step1 raw19721step1Labels permutation31 permutation3
    mixedMoment B raw19721step2 raw19721step2Labels = mixedMoment B raw19721step3 raw19721step3Labels := by
      have ha : raw19721step3 = -raw19721step2 := by apply Matrix.ext; change ∀ i j, raw19721step3 i j = -(raw19721step2 i j); unfold raw19721step3 raw19721step2; decide +kernel
      have hl : raw19721step3Labels = raw19721step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19721step3 raw19721step3Labels = mixedMoment B raw19721step4 raw19721step4Labels := by
      have ha : raw19721step4 = raw19721step3 := by apply Matrix.ext; unfold raw19721step4 raw19721step3; decide +kernel
      have hl : raw19721step3Labels = labelEmbedding6 ∘ raw19721step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19721step3 raw19721step3Labels raw19721step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4356 node4356Labels := by rfl

theorem canonical19722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19722 raw19722Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw19722 raw19722Labels = mixedMoment B raw19722step0 raw19722step0Labels := by
      have hz : ∀ j, raw19722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19722step0 = (fun i j => raw19722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19722step0 raw19722; decide +kernel
      have hl : raw19722step0Labels = raw19722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19722 raw19722Labels permutation346 hz
    mixedMoment B raw19722step0 raw19722step0Labels = mixedMoment B raw19722step1 raw19722step1Labels := by
      have hz : ∀ j, raw19722step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19722step1 = (fun i j => raw19722step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19722step1 raw19722step0; decide +kernel
      have hl : raw19722step1Labels = raw19722step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19722step0 raw19722step0Labels permutation56 hz
    mixedMoment B raw19722step1 raw19722step1Labels = mixedMoment B raw19722step2 raw19722step2Labels := by
      have ha : raw19722step2 = (fun i j => raw19722step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19722step2 raw19722step1; decide +kernel
      have hl : raw19722step2Labels = raw19722step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19722step1 raw19722step1Labels permutation31 permutation3
    mixedMoment B raw19722step2 raw19722step2Labels = mixedMoment B raw19722step3 raw19722step3Labels := by
      have ha : raw19722step3 = -raw19722step2 := by apply Matrix.ext; change ∀ i j, raw19722step3 i j = -(raw19722step2 i j); unfold raw19722step3 raw19722step2; decide +kernel
      have hl : raw19722step3Labels = raw19722step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19722step3 raw19722step3Labels = mixedMoment B raw19722step4 raw19722step4Labels := by
      have ha : raw19722step4 = raw19722step3 := by apply Matrix.ext; unfold raw19722step4 raw19722step3; decide +kernel
      have hl : raw19722step3Labels = labelEmbedding6 ∘ raw19722step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19722step3 raw19722step3Labels raw19722step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4356 node4356Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical159
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20384 raw20384Labels = mixedMoment B node4177 node4177Labels := by
  calc
    mixedMoment B raw20384 raw20384Labels = mixedMoment B raw20384step0 raw20384step0Labels := by
      have hz : ∀ j, raw20384 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20384step0 = (fun i j => raw20384 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20384step0 raw20384; decide +kernel
      have hl : raw20384step0Labels = raw20384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20384 raw20384Labels permutation434 hz
    mixedMoment B raw20384step0 raw20384step0Labels = mixedMoment B raw20384step1 raw20384step1Labels := by
      have hz : ∀ j, raw20384step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20384step1 = (fun i j => raw20384step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20384step1 raw20384step0; decide +kernel
      have hl : raw20384step1Labels = raw20384step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20384step0 raw20384step0Labels permutation80 hz
    mixedMoment B raw20384step1 raw20384step1Labels = mixedMoment B raw20384step2 raw20384step2Labels := by
      have ha : raw20384step2 = (fun i j => raw20384step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20384step2 raw20384step1; decide +kernel
      have hl : raw20384step2Labels = raw20384step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20384step1 raw20384step1Labels permutation10 permutation3
    mixedMoment B raw20384step2 raw20384step2Labels = mixedMoment B raw20384step3 raw20384step3Labels := by
      have ha : raw20384step3 = raw20384step2 := by apply Matrix.ext; unfold raw20384step3 raw20384step2; decide +kernel
      have hl : raw20384step2Labels = labelEmbedding6 ∘ raw20384step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20384step2 raw20384step2Labels raw20384step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4177 node4177Labels := by rfl

theorem canonical20385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20385 raw20385Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw20385 raw20385Labels = mixedMoment B raw20385step0 raw20385step0Labels := by
      have hz : ∀ j, raw20385 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20385step0 = (fun i j => raw20385 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20385step0 raw20385; decide +kernel
      have hl : raw20385step0Labels = raw20385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20385 raw20385Labels permutation434 hz
    mixedMoment B raw20385step0 raw20385step0Labels = mixedMoment B raw20385step1 raw20385step1Labels := by
      have ha : raw20385step1 = (fun i j => raw20385step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20385step1 raw20385step0; decide +kernel
      have hl : raw20385step1Labels = raw20385step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20385step0 raw20385step0Labels permutation40 permutation3
    mixedMoment B raw20385step1 raw20385step1Labels = mixedMoment B raw20385step2 raw20385step2Labels := by
      have ha : raw20385step2 = raw20385step1 := by apply Matrix.ext; unfold raw20385step2 raw20385step1; decide +kernel
      have hl : raw20385step1Labels = labelEmbedding6 ∘ raw20385step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20385step1 raw20385step1Labels raw20385step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4546 node4546Labels := by rfl

theorem canonical20386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20386 raw20386Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw20386 raw20386Labels = mixedMoment B raw20386step0 raw20386step0Labels := by
      have hz : ∀ j, raw20386 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20386step0 = (fun i j => raw20386 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20386step0 raw20386; decide +kernel
      have hl : raw20386step0Labels = raw20386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20386 raw20386Labels permutation346 hz
    mixedMoment B raw20386step0 raw20386step0Labels = mixedMoment B raw20386step1 raw20386step1Labels := by
      have ha : raw20386step1 = (fun i j => raw20386step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20386step1 raw20386step0; decide +kernel
      have hl : raw20386step1Labels = raw20386step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20386step0 raw20386step0Labels permutation40 permutation3
    mixedMoment B raw20386step1 raw20386step1Labels = mixedMoment B raw20386step2 raw20386step2Labels := by
      have ha : raw20386step2 = raw20386step1 := by apply Matrix.ext; unfold raw20386step2 raw20386step1; decide +kernel
      have hl : raw20386step1Labels = labelEmbedding6 ∘ raw20386step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20386step1 raw20386step1Labels raw20386step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4546 node4546Labels := by rfl

theorem canonical20387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20387 raw20387Labels = mixedMoment B node4177 node4177Labels := by
  calc
    mixedMoment B raw20387 raw20387Labels = mixedMoment B raw20387step0 raw20387step0Labels := by
      have hz : ∀ j, raw20387 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20387step0 = (fun i j => raw20387 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20387step0 raw20387; decide +kernel
      have hl : raw20387step0Labels = raw20387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20387 raw20387Labels permutation434 hz
    mixedMoment B raw20387step0 raw20387step0Labels = mixedMoment B raw20387step1 raw20387step1Labels := by
      have hz : ∀ j, raw20387step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20387step1 = (fun i j => raw20387step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20387step1 raw20387step0; decide +kernel
      have hl : raw20387step1Labels = raw20387step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20387step0 raw20387step0Labels permutation56 hz
    mixedMoment B raw20387step1 raw20387step1Labels = mixedMoment B raw20387step2 raw20387step2Labels := by
      have ha : raw20387step2 = (fun i j => raw20387step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20387step2 raw20387step1; decide +kernel
      have hl : raw20387step2Labels = raw20387step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20387step1 raw20387step1Labels permutation10 permutation3
    mixedMoment B raw20387step2 raw20387step2Labels = mixedMoment B raw20387step3 raw20387step3Labels := by
      have ha : raw20387step3 = raw20387step2 := by apply Matrix.ext; unfold raw20387step3 raw20387step2; decide +kernel
      have hl : raw20387step2Labels = labelEmbedding6 ∘ raw20387step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20387step2 raw20387step2Labels raw20387step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4177 node4177Labels := by rfl

theorem canonical20388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20388 raw20388Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw20388 raw20388Labels = mixedMoment B raw20388step0 raw20388step0Labels := by
      have hz : ∀ j, raw20388 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20388step0 = (fun i j => raw20388 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20388step0 raw20388; decide +kernel
      have hl : raw20388step0Labels = raw20388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20388 raw20388Labels permutation434 hz
    mixedMoment B raw20388step0 raw20388step0Labels = mixedMoment B raw20388step1 raw20388step1Labels := by
      have ha : raw20388step1 = (fun i j => raw20388step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20388step1 raw20388step0; decide +kernel
      have hl : raw20388step1Labels = raw20388step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20388step0 raw20388step0Labels permutation34 permutation3
    mixedMoment B raw20388step1 raw20388step1Labels = mixedMoment B raw20388step2 raw20388step2Labels := by
      have ha : raw20388step2 = raw20388step1 := by apply Matrix.ext; unfold raw20388step2 raw20388step1; decide +kernel
      have hl : raw20388step1Labels = labelEmbedding6 ∘ raw20388step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20388step1 raw20388step1Labels raw20388step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4546 node4546Labels := by rfl

theorem canonical20389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20389 raw20389Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw20389 raw20389Labels = mixedMoment B raw20389step0 raw20389step0Labels := by
      have hz : ∀ j, raw20389 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20389step0 = (fun i j => raw20389 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20389step0 raw20389; decide +kernel
      have hl : raw20389step0Labels = raw20389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20389 raw20389Labels permutation265 hz
    mixedMoment B raw20389step0 raw20389step0Labels = mixedMoment B raw20389step1 raw20389step1Labels := by
      have ha : raw20389step1 = (fun i j => raw20389step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20389step1 raw20389step0; decide +kernel
      have hl : raw20389step1Labels = raw20389step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20389step0 raw20389step0Labels permutation40 permutation3
    mixedMoment B raw20389step1 raw20389step1Labels = mixedMoment B raw20389step2 raw20389step2Labels := by
      have ha : raw20389step2 = raw20389step1 := by apply Matrix.ext; unfold raw20389step2 raw20389step1; decide +kernel
      have hl : raw20389step1Labels = labelEmbedding6 ∘ raw20389step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20389step1 raw20389step1Labels raw20389step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4546 node4546Labels := by rfl

theorem canonical20390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20390 raw20390Labels = mixedMoment B node4177 node4177Labels := by
  calc
    mixedMoment B raw20390 raw20390Labels = mixedMoment B raw20390step0 raw20390step0Labels := by
      have hz : ∀ j, raw20390 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20390step0 = (fun i j => raw20390 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20390step0 raw20390; decide +kernel
      have hl : raw20390step0Labels = raw20390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20390 raw20390Labels permutation346 hz
    mixedMoment B raw20390step0 raw20390step0Labels = mixedMoment B raw20390step1 raw20390step1Labels := by
      have hz : ∀ j, raw20390step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20390step1 = (fun i j => raw20390step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20390step1 raw20390step0; decide +kernel
      have hl : raw20390step1Labels = raw20390step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20390step0 raw20390step0Labels permutation56 hz
    mixedMoment B raw20390step1 raw20390step1Labels = mixedMoment B raw20390step2 raw20390step2Labels := by
      have ha : raw20390step2 = (fun i j => raw20390step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20390step2 raw20390step1; decide +kernel
      have hl : raw20390step2Labels = raw20390step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20390step1 raw20390step1Labels permutation10 permutation3
    mixedMoment B raw20390step2 raw20390step2Labels = mixedMoment B raw20390step3 raw20390step3Labels := by
      have ha : raw20390step3 = raw20390step2 := by apply Matrix.ext; unfold raw20390step3 raw20390step2; decide +kernel
      have hl : raw20390step2Labels = labelEmbedding6 ∘ raw20390step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20390step2 raw20390step2Labels raw20390step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4177 node4177Labels := by rfl

theorem canonical20391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20391 raw20391Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw20391 raw20391Labels = mixedMoment B raw20391step0 raw20391step0Labels := by
      have hz : ∀ j, raw20391 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20391step0 = (fun i j => raw20391 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20391step0 raw20391; decide +kernel
      have hl : raw20391step0Labels = raw20391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20391 raw20391Labels permutation346 hz
    mixedMoment B raw20391step0 raw20391step0Labels = mixedMoment B raw20391step1 raw20391step1Labels := by
      have ha : raw20391step1 = (fun i j => raw20391step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20391step1 raw20391step0; decide +kernel
      have hl : raw20391step1Labels = raw20391step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20391step0 raw20391step0Labels permutation34 permutation3
    mixedMoment B raw20391step1 raw20391step1Labels = mixedMoment B raw20391step2 raw20391step2Labels := by
      have ha : raw20391step2 = raw20391step1 := by apply Matrix.ext; unfold raw20391step2 raw20391step1; decide +kernel
      have hl : raw20391step1Labels = labelEmbedding6 ∘ raw20391step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20391step1 raw20391step1Labels raw20391step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4546 node4546Labels := by rfl

theorem canonical20392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20392 raw20392Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw20392 raw20392Labels = mixedMoment B raw20392step0 raw20392step0Labels := by
      have hz : ∀ j, raw20392 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20392step0 = (fun i j => raw20392 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20392step0 raw20392; decide +kernel
      have hl : raw20392step0Labels = raw20392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20392 raw20392Labels permutation265 hz
    mixedMoment B raw20392step0 raw20392step0Labels = mixedMoment B raw20392step1 raw20392step1Labels := by
      have ha : raw20392step1 = (fun i j => raw20392step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20392step1 raw20392step0; decide +kernel
      have hl : raw20392step1Labels = raw20392step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20392step0 raw20392step0Labels permutation34 permutation3
    mixedMoment B raw20392step1 raw20392step1Labels = mixedMoment B raw20392step2 raw20392step2Labels := by
      have ha : raw20392step2 = raw20392step1 := by apply Matrix.ext; unfold raw20392step2 raw20392step1; decide +kernel
      have hl : raw20392step1Labels = labelEmbedding6 ∘ raw20392step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20392step1 raw20392step1Labels raw20392step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4546 node4546Labels := by rfl

theorem canonical20393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20393 raw20393Labels = mixedMoment B node4191 node4191Labels := by
  calc
    mixedMoment B raw20393 raw20393Labels = mixedMoment B raw20393step0 raw20393step0Labels := by
      have hz : ∀ j, raw20393 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20393step0 = (fun i j => raw20393 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20393step0 raw20393; decide +kernel
      have hl : raw20393step0Labels = raw20393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20393 raw20393Labels permutation434 hz
    mixedMoment B raw20393step0 raw20393step0Labels = mixedMoment B raw20393step1 raw20393step1Labels := by
      have hz : ∀ j, raw20393step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20393step1 = (fun i j => raw20393step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20393step1 raw20393step0; decide +kernel
      have hl : raw20393step1Labels = raw20393step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20393step0 raw20393step0Labels permutation80 hz
    mixedMoment B raw20393step1 raw20393step1Labels = mixedMoment B raw20393step2 raw20393step2Labels := by
      have hz : ∀ j, raw20393step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20393step2 = (fun i j => raw20393step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20393step2 raw20393step1; decide +kernel
      have hl : raw20393step2Labels = raw20393step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20393step1 raw20393step1Labels permutation14 hz
    mixedMoment B raw20393step2 raw20393step2Labels = mixedMoment B raw20393step3 raw20393step3Labels := by
      have ha : raw20393step3 = (fun i j => raw20393step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20393step3 raw20393step2; decide +kernel
      have hl : raw20393step3Labels = raw20393step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20393step2 raw20393step2Labels permutation2 permutation3
    mixedMoment B raw20393step3 raw20393step3Labels = mixedMoment B raw20393step4 raw20393step4Labels := by
      have ha : raw20393step4 = raw20393step3 := by apply Matrix.ext; unfold raw20393step4 raw20393step3; decide +kernel
      have hl : raw20393step3Labels = labelEmbedding6 ∘ raw20393step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20393step3 raw20393step3Labels raw20393step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4191 node4191Labels := by rfl

theorem canonical20394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20394 raw20394Labels = mixedMoment B node4558 node4558Labels := by
  calc
    mixedMoment B raw20394 raw20394Labels = mixedMoment B raw20394step0 raw20394step0Labels := by
      have hz : ∀ j, raw20394 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20394step0 = (fun i j => raw20394 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20394step0 raw20394; decide +kernel
      have hl : raw20394step0Labels = raw20394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20394 raw20394Labels permutation434 hz
    mixedMoment B raw20394step0 raw20394step0Labels = mixedMoment B raw20394step1 raw20394step1Labels := by
      have hz : ∀ j, raw20394step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20394step1 = (fun i j => raw20394step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20394step1 raw20394step0; decide +kernel
      have hl : raw20394step1Labels = raw20394step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20394step0 raw20394step0Labels permutation80 hz
    mixedMoment B raw20394step1 raw20394step1Labels = mixedMoment B raw20394step2 raw20394step2Labels := by
      have ha : raw20394step2 = (fun i j => raw20394step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20394step2 raw20394step1; decide +kernel
      have hl : raw20394step2Labels = raw20394step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20394step1 raw20394step1Labels permutation8 permutation3
    mixedMoment B raw20394step2 raw20394step2Labels = mixedMoment B raw20394step3 raw20394step3Labels := by
      have ha : raw20394step3 = raw20394step2 := by apply Matrix.ext; unfold raw20394step3 raw20394step2; decide +kernel
      have hl : raw20394step2Labels = labelEmbedding6 ∘ raw20394step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20394step2 raw20394step2Labels raw20394step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4558 node4558Labels := by rfl

theorem canonical20395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20395 raw20395Labels = mixedMoment B node4558 node4558Labels := by
  calc
    mixedMoment B raw20395 raw20395Labels = mixedMoment B raw20395step0 raw20395step0Labels := by
      have hz : ∀ j, raw20395 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20395step0 = (fun i j => raw20395 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20395step0 raw20395; decide +kernel
      have hl : raw20395step0Labels = raw20395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20395 raw20395Labels permutation434 hz
    mixedMoment B raw20395step0 raw20395step0Labels = mixedMoment B raw20395step1 raw20395step1Labels := by
      have hz : ∀ j, raw20395step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20395step1 = (fun i j => raw20395step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20395step1 raw20395step0; decide +kernel
      have hl : raw20395step1Labels = raw20395step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20395step0 raw20395step0Labels permutation56 hz
    mixedMoment B raw20395step1 raw20395step1Labels = mixedMoment B raw20395step2 raw20395step2Labels := by
      have ha : raw20395step2 = (fun i j => raw20395step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20395step2 raw20395step1; decide +kernel
      have hl : raw20395step2Labels = raw20395step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20395step1 raw20395step1Labels permutation8 permutation3
    mixedMoment B raw20395step2 raw20395step2Labels = mixedMoment B raw20395step3 raw20395step3Labels := by
      have ha : raw20395step3 = raw20395step2 := by apply Matrix.ext; unfold raw20395step3 raw20395step2; decide +kernel
      have hl : raw20395step2Labels = labelEmbedding6 ∘ raw20395step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20395step2 raw20395step2Labels raw20395step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4558 node4558Labels := by rfl

theorem canonical20396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20396 raw20396Labels = mixedMoment B node4558 node4558Labels := by
  calc
    mixedMoment B raw20396 raw20396Labels = mixedMoment B raw20396step0 raw20396step0Labels := by
      have hz : ∀ j, raw20396 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20396step0 = (fun i j => raw20396 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20396step0 raw20396; decide +kernel
      have hl : raw20396step0Labels = raw20396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20396 raw20396Labels permutation346 hz
    mixedMoment B raw20396step0 raw20396step0Labels = mixedMoment B raw20396step1 raw20396step1Labels := by
      have hz : ∀ j, raw20396step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20396step1 = (fun i j => raw20396step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20396step1 raw20396step0; decide +kernel
      have hl : raw20396step1Labels = raw20396step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20396step0 raw20396step0Labels permutation56 hz
    mixedMoment B raw20396step1 raw20396step1Labels = mixedMoment B raw20396step2 raw20396step2Labels := by
      have ha : raw20396step2 = (fun i j => raw20396step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20396step2 raw20396step1; decide +kernel
      have hl : raw20396step2Labels = raw20396step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20396step1 raw20396step1Labels permutation8 permutation3
    mixedMoment B raw20396step2 raw20396step2Labels = mixedMoment B raw20396step3 raw20396step3Labels := by
      have ha : raw20396step3 = raw20396step2 := by apply Matrix.ext; unfold raw20396step3 raw20396step2; decide +kernel
      have hl : raw20396step2Labels = labelEmbedding6 ∘ raw20396step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20396step2 raw20396step2Labels raw20396step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4558 node4558Labels := by rfl

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

theorem canonical2307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2307 raw2307Labels = mixedMoment B node5296 node5296Labels := by
  calc
    mixedMoment B raw2307 raw2307Labels = mixedMoment B raw2307step0 raw2307step0Labels := by
      have ha : raw2307step0 = (fun i j => raw2307 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2307step0 raw2307; decide +kernel
      have hl : raw2307step0Labels = raw2307Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2307 raw2307Labels permutation2 permutation4
    mixedMoment B raw2307step0 raw2307step0Labels = mixedMoment B raw2307step1 raw2307step1Labels := by
      have ha : raw2307step1 = raw2307step0 := by apply Matrix.ext; unfold raw2307step1 raw2307step0; decide +kernel
      have hl : raw2307step0Labels = labelEmbedding7 ∘ raw2307step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2307step0 raw2307step0Labels raw2307step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5296 node5296Labels := by rfl

theorem canonical2308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2308 raw2308Labels = mixedMoment B node2770 node2770Labels := by
  calc
    mixedMoment B raw2308 raw2308Labels = mixedMoment B raw2308step0 raw2308step0Labels := by
      have ha : raw2308step0 = (fun i j => raw2308 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2308step0 raw2308; decide +kernel
      have hl : raw2308step0Labels = raw2308Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2308 raw2308Labels permutation2 permutation4
    _ = mixedMoment B node2770 node2770Labels := by rfl

theorem canonical2309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2309 raw2309Labels = mixedMoment B node3634 node3634Labels := by
  calc
    mixedMoment B raw2309 raw2309Labels = mixedMoment B raw2309step0 raw2309step0Labels := by
      have ha : raw2309step0 = (fun i j => raw2309 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2309step0 raw2309; decide +kernel
      have hl : raw2309step0Labels = raw2309Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2309 raw2309Labels permutation7 permutation3
    mixedMoment B raw2309step0 raw2309step0Labels = mixedMoment B raw2309step1 raw2309step1Labels := by
      have ha : raw2309step1 = raw2309step0 := by apply Matrix.ext; unfold raw2309step1 raw2309step0; decide +kernel
      have hl : raw2309step0Labels = labelEmbedding1 ∘ raw2309step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2309step0 raw2309step0Labels raw2309step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3634 node3634Labels := by rfl

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

theorem canonical274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw274 raw274Labels = mixedMoment B node2770 node2770Labels := by
  calc
    mixedMoment B raw274 raw274Labels = mixedMoment B raw274step0 raw274step0Labels := by
      have ha : raw274step0 = (fun i j => raw274 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw274step0 raw274; decide +kernel
      have hl : raw274step0Labels = raw274Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw274 raw274Labels permutation2 permutation5
    mixedMoment B raw274step0 raw274step0Labels = mixedMoment B raw274step1 raw274step1Labels := by
      have ha : raw274step1 = raw274step0 := by apply Matrix.ext; unfold raw274step1 raw274step0; decide +kernel
      have hl : raw274step0Labels = labelEmbedding1 ∘ raw274step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw274step0 raw274step0Labels raw274step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2770 node2770Labels := by rfl

theorem canonical275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw275 raw275Labels = mixedMoment B node407 node407Labels := by
  calc
    mixedMoment B raw275 raw275Labels = mixedMoment B raw275step0 raw275step0Labels := by
      have ha : raw275step0 = (fun i j => raw275 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw275step0 raw275; decide +kernel
      have hl : raw275step0Labels = raw275Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw275 raw275Labels permutation7 permutation4
    mixedMoment B raw275step0 raw275step0Labels = mixedMoment B raw275step1 raw275step1Labels := by
      have ha : raw275step1 = -raw275step0 := by apply Matrix.ext; change ∀ i j, raw275step1 i j = -(raw275step0 i j); unfold raw275step1 raw275step0; decide +kernel
      have hl : raw275step1Labels = raw275step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node407 node407Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4287 raw4287Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw4287 raw4287Labels = mixedMoment B raw4287step0 raw4287step0Labels := by
      have hz : ∀ j, raw4287 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4287step0 = (fun i j => raw4287 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4287step0 raw4287; decide +kernel
      have hl : raw4287step0Labels = raw4287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4287 raw4287Labels permutation434 hz
    mixedMoment B raw4287step0 raw4287step0Labels = mixedMoment B raw4287step1 raw4287step1Labels := by
      have hz : ∀ j, raw4287step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4287step1 = (fun i j => raw4287step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4287step1 raw4287step0; decide +kernel
      have hl : raw4287step1Labels = raw4287step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4287step0 raw4287step0Labels permutation80 hz
    mixedMoment B raw4287step1 raw4287step1Labels = mixedMoment B raw4287step2 raw4287step2Labels := by
      have ha : raw4287step2 = (fun i j => raw4287step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4287step2 raw4287step1; decide +kernel
      have hl : raw4287step2Labels = raw4287step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4287step1 raw4287step1Labels permutation10 permutation3
    mixedMoment B raw4287step2 raw4287step2Labels = mixedMoment B raw4287step3 raw4287step3Labels := by
      have ha : raw4287step3 = raw4287step2 := by apply Matrix.ext; unfold raw4287step3 raw4287step2; decide +kernel
      have hl : raw4287step2Labels = labelEmbedding6 ∘ raw4287step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4287step2 raw4287step2Labels raw4287step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

theorem canonical4292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4292 raw4292Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw4292 raw4292Labels = mixedMoment B raw4292step0 raw4292step0Labels := by
      have hz : ∀ j, raw4292 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4292step0 = (fun i j => raw4292 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4292step0 raw4292; decide +kernel
      have hl : raw4292step0Labels = raw4292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4292 raw4292Labels permutation434 hz
    mixedMoment B raw4292step0 raw4292step0Labels = mixedMoment B raw4292step1 raw4292step1Labels := by
      have hz : ∀ j, raw4292step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4292step1 = (fun i j => raw4292step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4292step1 raw4292step0; decide +kernel
      have hl : raw4292step1Labels = raw4292step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4292step0 raw4292step0Labels permutation56 hz
    mixedMoment B raw4292step1 raw4292step1Labels = mixedMoment B raw4292step2 raw4292step2Labels := by
      have ha : raw4292step2 = (fun i j => raw4292step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4292step2 raw4292step1; decide +kernel
      have hl : raw4292step2Labels = raw4292step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4292step1 raw4292step1Labels permutation10 permutation3
    mixedMoment B raw4292step2 raw4292step2Labels = mixedMoment B raw4292step3 raw4292step3Labels := by
      have ha : raw4292step3 = raw4292step2 := by apply Matrix.ext; unfold raw4292step3 raw4292step2; decide +kernel
      have hl : raw4292step2Labels = labelEmbedding6 ∘ raw4292step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4292step2 raw4292step2Labels raw4292step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

theorem canonical4297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4297 raw4297Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw4297 raw4297Labels = mixedMoment B raw4297step0 raw4297step0Labels := by
      have hz : ∀ j, raw4297 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4297step0 = (fun i j => raw4297 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4297step0 raw4297; decide +kernel
      have hl : raw4297step0Labels = raw4297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4297 raw4297Labels permutation346 hz
    mixedMoment B raw4297step0 raw4297step0Labels = mixedMoment B raw4297step1 raw4297step1Labels := by
      have hz : ∀ j, raw4297step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4297step1 = (fun i j => raw4297step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4297step1 raw4297step0; decide +kernel
      have hl : raw4297step1Labels = raw4297step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4297step0 raw4297step0Labels permutation56 hz
    mixedMoment B raw4297step1 raw4297step1Labels = mixedMoment B raw4297step2 raw4297step2Labels := by
      have ha : raw4297step2 = (fun i j => raw4297step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4297step2 raw4297step1; decide +kernel
      have hl : raw4297step2Labels = raw4297step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4297step1 raw4297step1Labels permutation10 permutation3
    mixedMoment B raw4297step2 raw4297step2Labels = mixedMoment B raw4297step3 raw4297step3Labels := by
      have ha : raw4297step3 = raw4297step2 := by apply Matrix.ext; unfold raw4297step3 raw4297step2; decide +kernel
      have hl : raw4297step2Labels = labelEmbedding6 ∘ raw4297step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4297step2 raw4297step2Labels raw4297step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

theorem canonical4303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4303 raw4303Labels = mixedMoment B node5174 node5174Labels := by
  calc
    mixedMoment B raw4303 raw4303Labels = mixedMoment B raw4303step0 raw4303step0Labels := by
      have hz : ∀ j, raw4303 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4303step0 = (fun i j => raw4303 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4303step0 raw4303; decide +kernel
      have hl : raw4303step0Labels = raw4303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4303 raw4303Labels permutation434 hz
    mixedMoment B raw4303step0 raw4303step0Labels = mixedMoment B raw4303step1 raw4303step1Labels := by
      have hz : ∀ j, raw4303step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4303step1 = (fun i j => raw4303step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4303step1 raw4303step0; decide +kernel
      have hl : raw4303step1Labels = raw4303step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4303step0 raw4303step0Labels permutation80 hz
    _ = mixedMoment B node5174 node5174Labels := by rfl

theorem canonical4304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4304 raw4304Labels = mixedMoment B node5174 node5174Labels := by
  calc
    mixedMoment B raw4304 raw4304Labels = mixedMoment B raw4304step0 raw4304step0Labels := by
      have hz : ∀ j, raw4304 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4304step0 = (fun i j => raw4304 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4304step0 raw4304; decide +kernel
      have hl : raw4304step0Labels = raw4304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4304 raw4304Labels permutation434 hz
    mixedMoment B raw4304step0 raw4304step0Labels = mixedMoment B raw4304step1 raw4304step1Labels := by
      have hz : ∀ j, raw4304step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4304step1 = (fun i j => raw4304step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4304step1 raw4304step0; decide +kernel
      have hl : raw4304step1Labels = raw4304step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4304step0 raw4304step0Labels permutation56 hz
    _ = mixedMoment B node5174 node5174Labels := by rfl

theorem canonical4305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4305 raw4305Labels = mixedMoment B node5174 node5174Labels := by
  calc
    mixedMoment B raw4305 raw4305Labels = mixedMoment B raw4305step0 raw4305step0Labels := by
      have hz : ∀ j, raw4305 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4305step0 = (fun i j => raw4305 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4305step0 raw4305; decide +kernel
      have hl : raw4305step0Labels = raw4305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4305 raw4305Labels permutation346 hz
    mixedMoment B raw4305step0 raw4305step0Labels = mixedMoment B raw4305step1 raw4305step1Labels := by
      have hz : ∀ j, raw4305step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4305step1 = (fun i j => raw4305step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4305step1 raw4305step0; decide +kernel
      have hl : raw4305step1Labels = raw4305step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4305step0 raw4305step0Labels permutation56 hz
    _ = mixedMoment B node5174 node5174Labels := by rfl

theorem canonical4306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4306 raw4306Labels = mixedMoment B node5309 node5309Labels := by
  calc
    mixedMoment B raw4306 raw4306Labels = mixedMoment B raw4306step0 raw4306step0Labels := by
      have hz : ∀ j, raw4306 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4306step0 = (fun i j => raw4306 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4306step0 raw4306; decide +kernel
      have hl : raw4306step0Labels = raw4306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4306 raw4306Labels permutation434 hz
    mixedMoment B raw4306step0 raw4306step0Labels = mixedMoment B raw4306step1 raw4306step1Labels := by
      have hz : ∀ j, raw4306step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4306step1 = (fun i j => raw4306step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4306step1 raw4306step0; decide +kernel
      have hl : raw4306step1Labels = raw4306step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4306step0 raw4306step0Labels permutation80 hz
    mixedMoment B raw4306step1 raw4306step1Labels = mixedMoment B raw4306step2 raw4306step2Labels := by
      have hz : ∀ j, raw4306step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4306step2 = (fun i j => raw4306step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4306step2 raw4306step1; decide +kernel
      have hl : raw4306step2Labels = raw4306step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4306step1 raw4306step1Labels permutation14 hz
    _ = mixedMoment B node5309 node5309Labels := by rfl

theorem canonical4307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4307 raw4307Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw4307 raw4307Labels = mixedMoment B raw4307step0 raw4307step0Labels := by
      have hz : ∀ j, raw4307 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4307step0 = (fun i j => raw4307 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4307step0 raw4307; decide +kernel
      have hl : raw4307step0Labels = raw4307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4307 raw4307Labels permutation434 hz
    mixedMoment B raw4307step0 raw4307step0Labels = mixedMoment B raw4307step1 raw4307step1Labels := by
      have hz : ∀ j, raw4307step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4307step1 = (fun i j => raw4307step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4307step1 raw4307step0; decide +kernel
      have hl : raw4307step1Labels = raw4307step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4307step0 raw4307step0Labels permutation80 hz
    mixedMoment B raw4307step1 raw4307step1Labels = mixedMoment B raw4307step2 raw4307step2Labels := by
      have hz : ∀ j, raw4307step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4307step2 = (fun i j => raw4307step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4307step2 raw4307step1; decide +kernel
      have hl : raw4307step2Labels = raw4307step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4307step1 raw4307step1Labels permutation14 hz
    mixedMoment B raw4307step2 raw4307step2Labels = mixedMoment B raw4307step3 raw4307step3Labels := by
      have ha : raw4307step3 = (fun i j => raw4307step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4307step3 raw4307step2; decide +kernel
      have hl : raw4307step3Labels = raw4307step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4307step2 raw4307step2Labels permutation7 permutation3
    mixedMoment B raw4307step3 raw4307step3Labels = mixedMoment B raw4307step4 raw4307step4Labels := by
      have ha : raw4307step4 = -raw4307step3 := by apply Matrix.ext; change ∀ i j, raw4307step4 i j = -(raw4307step3 i j); unfold raw4307step4 raw4307step3; decide +kernel
      have hl : raw4307step4Labels = raw4307step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4307step4 raw4307step4Labels = mixedMoment B raw4307step5 raw4307step5Labels := by
      have ha : raw4307step5 = raw4307step4 := by apply Matrix.ext; unfold raw4307step5 raw4307step4; decide +kernel
      have hl : raw4307step4Labels = labelEmbedding6 ∘ raw4307step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4307step4 raw4307step4Labels raw4307step5Labels labelEmbedding6 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

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

theorem canonical813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw813 raw813Labels = mixedMoment B node4177 node4177Labels := by
  calc
    mixedMoment B raw813 raw813Labels = mixedMoment B raw813step0 raw813step0Labels := by
      have ha : raw813step0 = (fun i j => raw813 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw813step0 raw813; decide +kernel
      have hl : raw813step0Labels = raw813Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw813 raw813Labels permutation8 permutation4
    mixedMoment B raw813step0 raw813step0Labels = mixedMoment B raw813step1 raw813step1Labels := by
      have ha : raw813step1 = raw813step0 := by apply Matrix.ext; unfold raw813step1 raw813step0; decide +kernel
      have hl : raw813step0Labels = labelEmbedding7 ∘ raw813step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw813step0 raw813step0Labels raw813step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4177 node4177Labels := by rfl

theorem canonical814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw814 raw814Labels = mixedMoment B node605 node605Labels := by
  calc
    mixedMoment B raw814 raw814Labels = mixedMoment B raw814step0 raw814step0Labels := by
      have ha : raw814step0 = (fun i j => raw814 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw814step0 raw814; decide +kernel
      have hl : raw814step0Labels = raw814Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw814 raw814Labels permutation8 permutation4
    _ = mixedMoment B node605 node605Labels := by rfl

theorem canonical815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw815 raw815Labels = mixedMoment B node1518 node1518Labels := by
  calc
    mixedMoment B raw815 raw815Labels = mixedMoment B raw815step0 raw815step0Labels := by
      have ha : raw815step0 = (fun i j => raw815 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw815step0 raw815; decide +kernel
      have hl : raw815step0Labels = raw815Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw815 raw815Labels permutation8 permutation6
    mixedMoment B raw815step0 raw815step0Labels = mixedMoment B raw815step1 raw815step1Labels := by
      have ha : raw815step1 = -raw815step0 := by apply Matrix.ext; change ∀ i j, raw815step1 i j = -(raw815step0 i j); unfold raw815step1 raw815step0; decide +kernel
      have hl : raw815step1Labels = raw815step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw815step1 raw815step1Labels = mixedMoment B raw815step2 raw815step2Labels := by
      have ha : raw815step2 = raw815step1 := by apply Matrix.ext; unfold raw815step2 raw815step1; decide +kernel
      have hl : raw815step1Labels = labelEmbedding1 ∘ raw815step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw815step1 raw815step1Labels raw815step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1518 node1518Labels := by rfl

theorem canonical819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw819 raw819Labels = mixedMoment B node4181 node4181Labels := by
  calc
    mixedMoment B raw819 raw819Labels = mixedMoment B raw819step0 raw819step0Labels := by
      have ha : raw819step0 = (fun i j => raw819 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw819step0 raw819; decide +kernel
      have hl : raw819step0Labels = raw819Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw819 raw819Labels permutation2 permutation4
    mixedMoment B raw819step0 raw819step0Labels = mixedMoment B raw819step1 raw819step1Labels := by
      have ha : raw819step1 = raw819step0 := by apply Matrix.ext; unfold raw819step1 raw819step0; decide +kernel
      have hl : raw819step0Labels = labelEmbedding7 ∘ raw819step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw819step0 raw819step0Labels raw819step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4181 node4181Labels := by rfl

theorem canonical820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw820 raw820Labels = mixedMoment B node609 node609Labels := by
  calc
    mixedMoment B raw820 raw820Labels = mixedMoment B raw820step0 raw820step0Labels := by
      have ha : raw820step0 = (fun i j => raw820 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw820step0 raw820; decide +kernel
      have hl : raw820step0Labels = raw820Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw820 raw820Labels permutation2 permutation4
    _ = mixedMoment B node609 node609Labels := by rfl

theorem canonical821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw821 raw821Labels = mixedMoment B node1521 node1521Labels := by
  calc
    mixedMoment B raw821 raw821Labels = mixedMoment B raw821step0 raw821step0Labels := by
      have ha : raw821step0 = (fun i j => raw821 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw821step0 raw821; decide +kernel
      have hl : raw821step0Labels = raw821Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw821 raw821Labels permutation2 permutation6
    mixedMoment B raw821step0 raw821step0Labels = mixedMoment B raw821step1 raw821step1Labels := by
      have ha : raw821step1 = -raw821step0 := by apply Matrix.ext; change ∀ i j, raw821step1 i j = -(raw821step0 i j); unfold raw821step1 raw821step0; decide +kernel
      have hl : raw821step1Labels = raw821step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw821step1 raw821step1Labels = mixedMoment B raw821step2 raw821step2Labels := by
      have ha : raw821step2 = raw821step1 := by apply Matrix.ext; unfold raw821step2 raw821step1; decide +kernel
      have hl : raw821step1Labels = labelEmbedding1 ∘ raw821step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw821step1 raw821step1Labels raw821step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1521 node1521Labels := by rfl

theorem canonical840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw840 raw840Labels = mixedMoment B node4191 node4191Labels := by
  calc
    mixedMoment B raw840 raw840Labels = mixedMoment B raw840step0 raw840step0Labels := by
      have ha : raw840step0 = (fun i j => raw840 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw840step0 raw840; decide +kernel
      have hl : raw840step0Labels = raw840Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw840 raw840Labels permutation2 permutation4
    mixedMoment B raw840step0 raw840step0Labels = mixedMoment B raw840step1 raw840step1Labels := by
      have ha : raw840step1 = raw840step0 := by apply Matrix.ext; unfold raw840step1 raw840step0; decide +kernel
      have hl : raw840step0Labels = labelEmbedding7 ∘ raw840step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw840step0 raw840step0Labels raw840step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4191 node4191Labels := by rfl

theorem canonical841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw841 raw841Labels = mixedMoment B node619 node619Labels := by
  calc
    mixedMoment B raw841 raw841Labels = mixedMoment B raw841step0 raw841step0Labels := by
      have ha : raw841step0 = (fun i j => raw841 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw841step0 raw841; decide +kernel
      have hl : raw841step0Labels = raw841Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw841 raw841Labels permutation2 permutation4
    _ = mixedMoment B node619 node619Labels := by rfl

theorem canonical842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw842 raw842Labels = mixedMoment B node1538 node1538Labels := by
  calc
    mixedMoment B raw842 raw842Labels = mixedMoment B raw842step0 raw842step0Labels := by
      have ha : raw842step0 = (fun i j => raw842 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw842step0 raw842; decide +kernel
      have hl : raw842step0Labels = raw842Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw842 raw842Labels permutation2 permutation6
    mixedMoment B raw842step0 raw842step0Labels = mixedMoment B raw842step1 raw842step1Labels := by
      have ha : raw842step1 = -raw842step0 := by apply Matrix.ext; change ∀ i j, raw842step1 i j = -(raw842step0 i j); unfold raw842step1 raw842step0; decide +kernel
      have hl : raw842step1Labels = raw842step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw842step1 raw842step1Labels = mixedMoment B raw842step2 raw842step2Labels := by
      have ha : raw842step2 = raw842step1 := by apply Matrix.ext; unfold raw842step2 raw842step1; decide +kernel
      have hl : raw842step1Labels = labelEmbedding1 ∘ raw842step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw842step1 raw842step1Labels raw842step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1538 node1538Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10198 raw10198Labels = mixedMoment B node4624 node4624Labels := by
  calc
    mixedMoment B raw10198 raw10198Labels = mixedMoment B raw10198step0 raw10198step0Labels := by
      have hz : ∀ j, raw10198 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10198step0 = (fun i j => raw10198 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10198step0 raw10198; decide +kernel
      have hl : raw10198step0Labels = raw10198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10198 raw10198Labels permutation434 hz
    mixedMoment B raw10198step0 raw10198step0Labels = mixedMoment B raw10198step1 raw10198step1Labels := by
      have hz : ∀ j, raw10198step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10198step1 = (fun i j => raw10198step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10198step1 raw10198step0; decide +kernel
      have hl : raw10198step1Labels = raw10198step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10198step0 raw10198step0Labels permutation80 hz
    _ = mixedMoment B node4624 node4624Labels := by rfl

theorem canonical10202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10202 raw10202Labels = mixedMoment B node4624 node4624Labels := by
  calc
    mixedMoment B raw10202 raw10202Labels = mixedMoment B raw10202step0 raw10202step0Labels := by
      have hz : ∀ j, raw10202 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10202step0 = (fun i j => raw10202 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10202step0 raw10202; decide +kernel
      have hl : raw10202step0Labels = raw10202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10202 raw10202Labels permutation434 hz
    mixedMoment B raw10202step0 raw10202step0Labels = mixedMoment B raw10202step1 raw10202step1Labels := by
      have hz : ∀ j, raw10202step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10202step1 = (fun i j => raw10202step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10202step1 raw10202step0; decide +kernel
      have hl : raw10202step1Labels = raw10202step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10202step0 raw10202step0Labels permutation56 hz
    _ = mixedMoment B node4624 node4624Labels := by rfl

theorem canonical10206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10206 raw10206Labels = mixedMoment B node4624 node4624Labels := by
  calc
    mixedMoment B raw10206 raw10206Labels = mixedMoment B raw10206step0 raw10206step0Labels := by
      have hz : ∀ j, raw10206 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10206step0 = (fun i j => raw10206 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10206step0 raw10206; decide +kernel
      have hl : raw10206step0Labels = raw10206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10206 raw10206Labels permutation346 hz
    mixedMoment B raw10206step0 raw10206step0Labels = mixedMoment B raw10206step1 raw10206step1Labels := by
      have hz : ∀ j, raw10206step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10206step1 = (fun i j => raw10206step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10206step1 raw10206step0; decide +kernel
      have hl : raw10206step1Labels = raw10206step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10206step0 raw10206step0Labels permutation56 hz
    _ = mixedMoment B node4624 node4624Labels := by rfl

theorem canonical10210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10210 raw10210Labels = mixedMoment B node4628 node4628Labels := by
  calc
    mixedMoment B raw10210 raw10210Labels = mixedMoment B raw10210step0 raw10210step0Labels := by
      have hz : ∀ j, raw10210 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10210step0 = (fun i j => raw10210 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10210step0 raw10210; decide +kernel
      have hl : raw10210step0Labels = raw10210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10210 raw10210Labels permutation434 hz
    mixedMoment B raw10210step0 raw10210step0Labels = mixedMoment B raw10210step1 raw10210step1Labels := by
      have hz : ∀ j, raw10210step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10210step1 = (fun i j => raw10210step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10210step1 raw10210step0; decide +kernel
      have hl : raw10210step1Labels = raw10210step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10210step0 raw10210step0Labels permutation80 hz
    mixedMoment B raw10210step1 raw10210step1Labels = mixedMoment B raw10210step2 raw10210step2Labels := by
      have hz : ∀ j, raw10210step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10210step2 = (fun i j => raw10210step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10210step2 raw10210step1; decide +kernel
      have hl : raw10210step2Labels = raw10210step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10210step1 raw10210step1Labels permutation14 hz
    _ = mixedMoment B node4628 node4628Labels := by rfl

theorem canonical10215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10215 raw10215Labels = mixedMoment B node5296 node5296Labels := by
  calc
    mixedMoment B raw10215 raw10215Labels = mixedMoment B raw10215step0 raw10215step0Labels := by
      have hz : ∀ j, raw10215 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10215step0 = (fun i j => raw10215 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10215step0 raw10215; decide +kernel
      have hl : raw10215step0Labels = raw10215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10215 raw10215Labels permutation434 hz
    mixedMoment B raw10215step0 raw10215step0Labels = mixedMoment B raw10215step1 raw10215step1Labels := by
      have hz : ∀ j, raw10215step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10215step1 = (fun i j => raw10215step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10215step1 raw10215step0; decide +kernel
      have hl : raw10215step1Labels = raw10215step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10215step0 raw10215step0Labels permutation80 hz
    mixedMoment B raw10215step1 raw10215step1Labels = mixedMoment B raw10215step2 raw10215step2Labels := by
      have hz : ∀ j, raw10215step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10215step2 = (fun i j => raw10215step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10215step2 raw10215step1; decide +kernel
      have hl : raw10215step2Labels = raw10215step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10215step1 raw10215step1Labels permutation14 hz
    _ = mixedMoment B node5296 node5296Labels := by rfl

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

theorem canonical1152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1152 raw1152Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw1152 raw1152Labels = mixedMoment B raw1152step0 raw1152step0Labels := by
      have ha : raw1152step0 = (fun i j => raw1152 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1152step0 raw1152; decide +kernel
      have hl : raw1152step0Labels = raw1152Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1152 raw1152Labels permutation8 permutation4
    mixedMoment B raw1152step0 raw1152step0Labels = mixedMoment B raw1152step1 raw1152step1Labels := by
      have ha : raw1152step1 = raw1152step0 := by apply Matrix.ext; unfold raw1152step1 raw1152step0; decide +kernel
      have hl : raw1152step0Labels = labelEmbedding7 ∘ raw1152step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1152step0 raw1152step0Labels raw1152step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4356 node4356Labels := by rfl

theorem canonical1153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1153 raw1153Labels = mixedMoment B node934 node934Labels := by
  calc
    mixedMoment B raw1153 raw1153Labels = mixedMoment B raw1153step0 raw1153step0Labels := by
      have ha : raw1153step0 = (fun i j => raw1153 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1153step0 raw1153; decide +kernel
      have hl : raw1153step0Labels = raw1153Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1153 raw1153Labels permutation8 permutation4
    _ = mixedMoment B node934 node934Labels := by rfl

theorem canonical1154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1154 raw1154Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw1154 raw1154Labels = mixedMoment B raw1154step0 raw1154step0Labels := by
      have ha : raw1154step0 = (fun i j => raw1154 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1154step0 raw1154; decide +kernel
      have hl : raw1154step0Labels = raw1154Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1154 raw1154Labels permutation8 permutation6
    mixedMoment B raw1154step0 raw1154step0Labels = mixedMoment B raw1154step1 raw1154step1Labels := by
      have ha : raw1154step1 = -raw1154step0 := by apply Matrix.ext; change ∀ i j, raw1154step1 i j = -(raw1154step0 i j); unfold raw1154step1 raw1154step0; decide +kernel
      have hl : raw1154step1Labels = raw1154step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1154step1 raw1154step1Labels = mixedMoment B raw1154step2 raw1154step2Labels := by
      have ha : raw1154step2 = raw1154step1 := by apply Matrix.ext; unfold raw1154step2 raw1154step1; decide +kernel
      have hl : raw1154step1Labels = labelEmbedding1 ∘ raw1154step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1154step1 raw1154step1Labels raw1154step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1692 node1692Labels := by rfl

theorem canonical1278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1278 raw1278Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw1278 raw1278Labels = mixedMoment B raw1278step0 raw1278step0Labels := by
      have ha : raw1278step0 = (fun i j => raw1278 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1278step0 raw1278; decide +kernel
      have hl : raw1278step0Labels = raw1278Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1278 raw1278Labels permutation2 permutation4
    mixedMoment B raw1278step0 raw1278step0Labels = mixedMoment B raw1278step1 raw1278step1Labels := by
      have ha : raw1278step1 = raw1278step0 := by apply Matrix.ext; unfold raw1278step1 raw1278step0; decide +kernel
      have hl : raw1278step0Labels = labelEmbedding7 ∘ raw1278step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1278step0 raw1278step0Labels raw1278step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

theorem canonical1279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1279 raw1279Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw1279 raw1279Labels = mixedMoment B raw1279step0 raw1279step0Labels := by
      have ha : raw1279step0 = (fun i j => raw1279 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1279step0 raw1279; decide +kernel
      have hl : raw1279step0Labels = raw1279Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1279 raw1279Labels permutation2 permutation4
    _ = mixedMoment B node1051 node1051Labels := by rfl

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

theorem canonical5197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5197 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw5197 = injectiveMoment H raw5197step0 := by
      have hz : ∀ j, raw5197 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5197step0 = (fun i j => raw5197 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5197 permutation21 hz
    _ = injectiveMoment H node11 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical784 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw784 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw784 = injectiveMoment H raw784step0 := by
      have heq : raw784step0 = raw784.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw784).symm
    injectiveMoment H raw784step0 = injectiveMoment H raw784step1 := by
      have heq : raw784step1 = (fun i j => raw784step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw784step0 permutation7 permutation6
    _ = injectiveMoment H node63 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7977 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7977 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw7977 = injectiveMoment H raw7977step0 := by
      have heq : raw7977step0 = raw7977.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7977).symm
    injectiveMoment H raw7977step0 = injectiveMoment H raw7977step1 := by
      have heq : raw7977step1 = (fun i j => raw7977step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7977step0 permutation5 permutation2
    _ = injectiveMoment H node10 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5177 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5177 = injectiveMoment H node11 := by
  clear _hH
  calc
    injectiveMoment H raw5177 = injectiveMoment H raw5177step0 := by
      have hz : ∀ j, raw5177 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5177step0 = (fun i j => raw5177 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5177 permutation15 hz
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5458 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5458 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5458 = injectiveMoment H raw5458step0 := by
      have heq : raw5458step0 = raw5458.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5458).symm
    injectiveMoment H raw5458step0 = injectiveMoment H raw5458step1 := by
      have heq : raw5458step1 = (fun i j => raw5458step0 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5458step0 permutation6 permutation2
    _ = injectiveMoment H node10 := by rfl

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

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical841 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw841 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw841 = injectiveMoment H raw841step0 := by
      have heq : raw841step0 = raw841.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw841).symm
    injectiveMoment H raw841step0 = injectiveMoment H raw841step1 := by
      have heq : raw841step1 = (fun i j => raw841step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw841step0 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical175 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw175 = injectiveMoment H node150 := by
  calc
    injectiveMoment H raw175 = injectiveMoment H raw175step0 := by
      have heq : raw175step0 = -raw175 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw175).symm
    injectiveMoment H raw175step0 = injectiveMoment H raw175step1 := by
      have heq : raw175step1 = (fun i j => raw175step0 (permutation11 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw175step0 permutation11 permutation6
    _ = injectiveMoment H node150 := by rfl

theorem canonical179 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw179 = injectiveMoment H node35 := by
  calc
    injectiveMoment H raw179 = injectiveMoment H raw179step0 := by
      have heq : raw179step0 = -raw179 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw179).symm
    injectiveMoment H raw179step0 = injectiveMoment H raw179step1 := by
      have heq : raw179step1 = (fun i j => raw179step0 (permutation3 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw179step0 permutation3 permutation6
    _ = injectiveMoment H node35 := by rfl

theorem canonical180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw180 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw180 = injectiveMoment H raw180step0 := by
      have heq : raw180step0 = raw180.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw180).symm
    _ = injectiveMoment H node9 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical208 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw208 = injectiveMoment H node16 := by
  rfl

theorem canonical211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw211 = injectiveMoment H node8 := by
  rfl

theorem canonical214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw214 = injectiveMoment H node9 := by
  rfl

theorem canonical215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw215 = injectiveMoment H node2 := by
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

theorem sound2 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node2 = Sparse.eval value2 (momentVector H) := by
  have hc : momentVector H 6 = injectiveMoment H node2 := rfl
  simp [value2, Sparse.eval, hc]

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

theorem sound8 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node8 = Sparse.eval value8 (momentVector H) := by
  have heq : pivotMatrix8 = (fun u v => node8 (pivotPermutation8 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node8 = injectiveMoment H pivotMatrix8 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix8 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix8 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix8 (0 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix8 (0 : Fin 2) = raw926 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical926 hH).trans (sound3 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix8 (1 : Fin 2)) =
      Sparse.eval value2 (momentVector H) := by
    have heq : mergeFirst pivotMatrix8 (1 : Fin 2) = raw215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical215 hH).trans (sound2 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node8 + (injectiveMoment H (mergeFirst pivotMatrix8 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix8 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value8, value2, value3, Sparse.eval] at hc ⊢
  linarith

theorem sound9 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node9 = Sparse.eval value9 (momentVector H) := by
  have hc : momentVector H 5 = injectiveMoment H node9 := rfl
  simp [value9, Sparse.eval, hc]

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

theorem sound16 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node16 = Sparse.eval value16 (momentVector H) := by
  have heq : pivotMatrix16 = (fun u v => node16 (pivotPermutation16 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node16 = injectiveMoment H pivotMatrix16 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix16 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix16 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix16 (0 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (0 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix16 (1 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (1 : Fin 3) = raw214 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical214 hH).trans (sound9 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix16 (2 : Fin 3)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (2 : Fin 3) = raw211 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical211 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node16 + (injectiveMoment H (mergeFirst pivotMatrix16 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix16 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix16 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value16, value10, value8, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound35 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node35 = Sparse.eval value35 (momentVector H) := by
  have hc : momentVector H 8 = injectiveMoment H node35 := rfl
  simp [value35, Sparse.eval, hc]

theorem sound52 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node52 = Sparse.eval value52 (momentVector H) := by
  have heq : pivotMatrix52 = (fun u v => node52.transpose (pivotPermutation52 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node52 = injectiveMoment H pivotMatrix52 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix52 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix52 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix52 (0 : Fin 2)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix52 (0 : Fin 2) = raw180 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical180 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix52 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix52 (1 : Fin 2) = raw841 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical841 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node52 + (injectiveMoment H (mergeFirst pivotMatrix52 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix52 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value52, value10, value9, Sparse.eval] at hc ⊢
  linarith

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

theorem sound63 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node63 = Sparse.eval value63 (momentVector H) := by
  have heq : pivotMatrix63 = (fun u v => node63.transpose (pivotPermutation63 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node63 = injectiveMoment H pivotMatrix63 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix63 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix63 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix63 (0 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix63 (0 : Fin 2) = raw5458 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5458 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix63 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix63 (1 : Fin 2) = raw7977 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7977 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node63 + (injectiveMoment H (mergeFirst pivotMatrix63 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix63 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value63, value10, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1447 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1447 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1447 = injectiveMoment H raw1447step0 := by
      have heq : raw1447step0 = raw1447.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1447).symm
    injectiveMoment H raw1447step0 = injectiveMoment H raw1447step1 := by
      have heq : raw1447step1 = (fun i j => raw1447step0 (permutation8 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1447step0 permutation8 permutation6
    _ = injectiveMoment H node52 := by rfl

theorem canonical1449 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1449 = injectiveMoment H node35 := by
  rfl

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

theorem canonical2862 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2862 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2862 = injectiveMoment H raw2862step0 := by
      have heq : raw2862step0 = (fun i j => raw2862 (permutation3 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2862 permutation3 permutation5
    _ = injectiveMoment H node56 := by rfl

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

theorem sound150 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node150 = Sparse.eval value150 (momentVector H) := by
  have heq : pivotMatrix150 = (fun u v => node150 (pivotPermutation150 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node150 = injectiveMoment H pivotMatrix150 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix150 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix150 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix150 (0 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix150 (0 : Fin 3) = raw2862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2862 hH).trans (sound56 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix150 (1 : Fin 3)) =
      Sparse.eval value35 (momentVector H) := by
    have heq : mergeFirst pivotMatrix150 (1 : Fin 3) = raw1449 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1449 hH).trans (sound35 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix150 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix150 (2 : Fin 3) = raw1447 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1447 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node150 + (injectiveMoment H (mergeFirst pivotMatrix150 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix150 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix150 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value150, value35, value52, value56, Sparse.eval] at hc ⊢
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

theorem singlePair407 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node407 node407Labels = Sparse.eval singlePairValue407 (familyPairVector B) := by
  have hp := single_label_three B hB node407
  have hl : node407Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node407 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node407 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node407 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node407 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node407 (EqualityPatterns.family3.label 1) = PairSemantics.raw5199 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node407 PairSemantics.raw5199; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5199 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node407 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node407 (EqualityPatterns.family3.label 2) = PairSemantics.raw7683 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node407 PairSemantics.raw7683; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7683 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node407 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node407 (EqualityPatterns.family3.label 3) = PairSemantics.raw900 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node407 PairSemantics.raw900; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical900 hH).trans (PairSemantics.sound3 hH)
  have hm4 : familyPairMoment B (groupedColumns node407 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value63 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node407 (EqualityPatterns.family3.label 4) = PairSemantics.raw784 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node407 PairSemantics.raw784; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical784 hH).trans (PairSemantics.sound63 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue407, PairSemantics.value0, PairSemantics.value3, PairSemantics.value11, PairSemantics.value63, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair157 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node157 node157Labels = Sparse.eval singlePairValue157 (familyPairVector B) := by
  have hp := single_label_three B hB node157
  have hl : node157Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node157 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node157 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node157 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node157 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node157 (EqualityPatterns.family3.label 1) = PairSemantics.raw5177 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node157 PairSemantics.raw5177
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5177 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node157 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node157 (EqualityPatterns.family3.label 2) = PairSemantics.raw5197 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node157 PairSemantics.raw5197
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5197 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node157 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node157 (EqualityPatterns.family3.label 3) = PairSemantics.raw208 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node157 PairSemantics.raw208
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical208 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node157 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value150 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node157 (EqualityPatterns.family3.label 4) = PairSemantics.raw175 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node157 PairSemantics.raw175
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical175 hH).trans (PairSemantics.sound150 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue157, PairSemantics.value0, PairSemantics.value11, PairSemantics.value16, PairSemantics.value150, Sparse.eval] at hp ⊢
  linarith only [hp]

theorem singlePair161 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node161 node161Labels = Sparse.eval singlePairValue161 (familyPairVector B) := by
  have hp := single_label_three B hB node161
  have hl : node161Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node161 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node161 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node161 PairSemantics.raw7979
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node161 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node161 (EqualityPatterns.family3.label 1) = PairSemantics.raw5199 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node161 PairSemantics.raw5199
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5199 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node161 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node161 (EqualityPatterns.family3.label 2) = PairSemantics.raw5199 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node161 PairSemantics.raw5199
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5199 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node161 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node161 (EqualityPatterns.family3.label 3) = PairSemantics.raw214 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node161 PairSemantics.raw214
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical214 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node161 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value35 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node161 (EqualityPatterns.family3.label 4) = PairSemantics.raw179 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node161 PairSemantics.raw179
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical179 hH).trans (PairSemantics.sound35 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue161, PairSemantics.value0, PairSemantics.value9, PairSemantics.value11, PairSemantics.value35, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton1301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1301 node1301Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node157 node157Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw78 singletonSmall1301
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1301) = raw78Labels := by decide +kernel
  rw [hl, canonical78 B hB] at h
  have hc0 : mixedMoment B raw78 (Fin.cases (0 : Fin 1) singletonSmall1301) =
      mixedMoment B node157 node157Labels := by
    have ha : raw78 = raw79 := by apply Matrix.ext; unfold raw78 raw79; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1301 = raw79Labels := by decide +kernel
    rw [ha, hj, canonical79 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton1312 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1312 node1312Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node161 node161Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw92 singletonSmall1312
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1312) = raw92Labels := by decide +kernel
  rw [hl, canonical92 B hB] at h
  have hc0 : mixedMoment B raw92 (Fin.cases (0 : Fin 1) singletonSmall1312) =
      mixedMoment B node161 node161Labels := by
    have ha : raw92 = raw93 := by apply Matrix.ext; unfold raw92 raw93; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1312 = raw93Labels := by decide +kernel
    rw [ha, hj, canonical93 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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

theorem singleton2770 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2770 node2770Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node407 node407Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw274 singletonSmall2770
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2770) = raw274Labels := by decide +kernel
  rw [hl, canonical274 B hB] at h
  have hc0 : mixedMoment B raw274 (Fin.cases (0 : Fin 1) singletonSmall2770) =
      mixedMoment B node407 node407Labels := by
    have ha : raw274 = raw275 := by apply Matrix.ext; unfold raw274 raw275; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2770 = raw275Labels := by decide +kernel
    rw [ha, hj, canonical275 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton4177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4177 node4177Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node605 node605Labels + mixedMoment B node1518 node1518Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw813 singletonSmall4177
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4177) = raw813Labels := by decide +kernel
  rw [hl, canonical813 B hB] at h
  have hc0 : mixedMoment B raw813 (Fin.cases (0 : Fin 2) singletonSmall4177) =
      mixedMoment B node605 node605Labels := by
    have ha : raw813 = raw814 := by apply Matrix.ext; unfold raw813 raw814; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4177 = raw814Labels := by decide +kernel
    rw [ha, hj, canonical814 B hB]
  have hc1 : mixedMoment B raw813 (Fin.cases (1 : Fin 2) singletonSmall4177) =
      mixedMoment B node1518 node1518Labels := by
    have ha : raw813 = raw815 := by apply Matrix.ext; unfold raw813 raw815; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4177 = raw815Labels := by decide +kernel
    rw [ha, hj, canonical815 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4181 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4181 node4181Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node609 node609Labels + mixedMoment B node1521 node1521Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw819 singletonSmall4181
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4181) = raw819Labels := by decide +kernel
  rw [hl, canonical819 B hB] at h
  have hc0 : mixedMoment B raw819 (Fin.cases (0 : Fin 2) singletonSmall4181) =
      mixedMoment B node609 node609Labels := by
    have ha : raw819 = raw820 := by apply Matrix.ext; unfold raw819 raw820; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4181 = raw820Labels := by decide +kernel
    rw [ha, hj, canonical820 B hB]
  have hc1 : mixedMoment B raw819 (Fin.cases (1 : Fin 2) singletonSmall4181) =
      mixedMoment B node1521 node1521Labels := by
    have ha : raw819 = raw821 := by apply Matrix.ext; unfold raw819 raw821; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4181 = raw821Labels := by decide +kernel
    rw [ha, hj, canonical821 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4191 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4191 node4191Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node619 node619Labels + mixedMoment B node1538 node1538Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw840 singletonSmall4191
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4191) = raw840Labels := by decide +kernel
  rw [hl, canonical840 B hB] at h
  have hc0 : mixedMoment B raw840 (Fin.cases (0 : Fin 2) singletonSmall4191) =
      mixedMoment B node619 node619Labels := by
    have ha : raw840 = raw841 := by apply Matrix.ext; unfold raw840 raw841; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4191 = raw841Labels := by decide +kernel
    rw [ha, hj, canonical841 B hB]
  have hc1 : mixedMoment B raw840 (Fin.cases (1 : Fin 2) singletonSmall4191) =
      mixedMoment B node1538 node1538Labels := by
    have ha : raw840 = raw842 := by apply Matrix.ext; unfold raw840 raw842; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4191 = raw842Labels := by decide +kernel
    rw [ha, hj, canonical842 B hB]
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

theorem singleton4356 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4356 node4356Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node934 node934Labels + mixedMoment B node1692 node1692Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1152 singletonSmall4356
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4356) = raw1152Labels := by decide +kernel
  rw [hl, canonical1152 B hB] at h
  have hc0 : mixedMoment B raw1152 (Fin.cases (0 : Fin 2) singletonSmall4356) =
      mixedMoment B node934 node934Labels := by
    have ha : raw1152 = raw1153 := by apply Matrix.ext; unfold raw1152 raw1153; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4356 = raw1153Labels := by decide +kernel
    rw [ha, hj, canonical1153 B hB]
  have hc1 : mixedMoment B raw1152 (Fin.cases (1 : Fin 2) singletonSmall4356) =
      mixedMoment B node1692 node1692Labels := by
    have ha : raw1152 = raw1154 := by apply Matrix.ext; unfold raw1152 raw1154; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4356 = raw1154Labels := by decide +kernel
    rw [ha, hj, canonical1154 B hB]
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

theorem singleton4468 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4468 node4468Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1051 node1051Labels + mixedMoment B node1752 node1752Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1278 singletonSmall4468
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4468) = raw1278Labels := by decide +kernel
  rw [hl, canonical1278 B hB] at h
  have hc0 : mixedMoment B raw1278 (Fin.cases (0 : Fin 2) singletonSmall4468) =
      mixedMoment B node1051 node1051Labels := by
    have ha : raw1278 = raw1279 := by apply Matrix.ext; unfold raw1278 raw1279; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4468 = raw1279Labels := by decide +kernel
    rw [ha, hj, canonical1279 B hB]
  have hc1 : mixedMoment B raw1278 (Fin.cases (1 : Fin 2) singletonSmall4468) =
      mixedMoment B node1752 node1752Labels := by
    have ha : raw1278 = raw1280 := by apply Matrix.ext; unfold raw1278 raw1280; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4468 = raw1280Labels := by decide +kernel
    rw [ha, hj, canonical1280 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton4546 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4546 node4546Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1131 node1131Labels + mixedMoment B node3264 node3264Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1371 singletonSmall4546
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4546) = raw1371Labels := by decide +kernel
  rw [hl, canonical1371 B hB] at h
  have hc0 : mixedMoment B raw1371 (Fin.cases (0 : Fin 2) singletonSmall4546) =
      mixedMoment B node1131 node1131Labels := by
    have ha : raw1371 = raw1372 := by apply Matrix.ext; unfold raw1371 raw1372; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4546 = raw1372Labels := by decide +kernel
    rw [ha, hj, canonical1372 B hB]
  have hc1 : mixedMoment B raw1371 (Fin.cases (1 : Fin 2) singletonSmall4546) =
      mixedMoment B node3264 node3264Labels := by
    have ha : raw1371 = raw1373 := by apply Matrix.ext; unfold raw1371 raw1373; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4546 = raw1373Labels := by decide +kernel
    rw [ha, hj, canonical1373 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4558 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4558 node4558Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1144 node1144Labels + mixedMoment B node3276 node3276Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1395 singletonSmall4558
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4558) = raw1395Labels := by decide +kernel
  rw [hl, canonical1395 B hB] at h
  have hc0 : mixedMoment B raw1395 (Fin.cases (0 : Fin 2) singletonSmall4558) =
      mixedMoment B node1144 node1144Labels := by
    have ha : raw1395 = raw1396 := by apply Matrix.ext; unfold raw1395 raw1396; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4558 = raw1396Labels := by decide +kernel
    rw [ha, hj, canonical1396 B hB]
  have hc1 : mixedMoment B raw1395 (Fin.cases (1 : Fin 2) singletonSmall4558) =
      mixedMoment B node3276 node3276Labels := by
    have ha : raw1395 = raw1397 := by apply Matrix.ext; unfold raw1395 raw1397; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4558 = raw1397Labels := by decide +kernel
    rw [ha, hj, canonical1397 B hB]
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

theorem singleton4624 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4624 node4624Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1301 node1301Labels + mixedMoment B node3309 node3309Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1455 singletonSmall4624
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4624) = raw1455Labels := by decide +kernel
  rw [hl, canonical1455 B hB] at h
  have hc0 : mixedMoment B raw1455 (Fin.cases (0 : Fin 2) singletonSmall4624) =
      mixedMoment B node1301 node1301Labels := by
    have ha : raw1455 = raw1456 := by apply Matrix.ext; unfold raw1455 raw1456; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4624 = raw1456Labels := by decide +kernel
    rw [ha, hj, canonical1456 B hB]
  have hc1 : mixedMoment B raw1455 (Fin.cases (1 : Fin 2) singletonSmall4624) =
      mixedMoment B node3309 node3309Labels := by
    have ha : raw1455 = raw1457 := by apply Matrix.ext; unfold raw1455 raw1457; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4624 = raw1457Labels := by decide +kernel
    rw [ha, hj, canonical1457 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4628 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4628 node4628Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1312 node1312Labels + mixedMoment B node3312 node3312Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1464 singletonSmall4628
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4628) = raw1464Labels := by decide +kernel
  rw [hl, canonical1464 B hB] at h
  have hc0 : mixedMoment B raw1464 (Fin.cases (0 : Fin 2) singletonSmall4628) =
      mixedMoment B node1312 node1312Labels := by
    have ha : raw1464 = raw1465 := by apply Matrix.ext; unfold raw1464 raw1465; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4628 = raw1465Labels := by decide +kernel
    rw [ha, hj, canonical1465 B hB]
  have hc1 : mixedMoment B raw1464 (Fin.cases (1 : Fin 2) singletonSmall4628) =
      mixedMoment B node3312 node3312Labels := by
    have ha : raw1464 = raw1466 := by apply Matrix.ext; unfold raw1464 raw1466; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4628 = raw1466Labels := by decide +kernel
    rw [ha, hj, canonical1466 B hB]
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

theorem singleton5296 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5296 node5296Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2770 node2770Labels + mixedMoment B node3634 node3634Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2307 singletonSmall5296
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5296) = raw2307Labels := by decide +kernel
  rw [hl, canonical2307 B hB] at h
  have hc0 : mixedMoment B raw2307 (Fin.cases (0 : Fin 2) singletonSmall5296) =
      mixedMoment B node2770 node2770Labels := by
    have ha : raw2307 = raw2308 := by apply Matrix.ext; unfold raw2307 raw2308; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5296 = raw2308Labels := by decide +kernel
    rw [ha, hj, canonical2308 B hB]
  have hc1 : mixedMoment B raw2307 (Fin.cases (1 : Fin 2) singletonSmall5296) =
      mixedMoment B node3634 node3634Labels := by
    have ha : raw2307 = raw2309 := by apply Matrix.ext; unfold raw2307 raw2309; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5296 = raw2309Labels := by decide +kernel
    rw [ha, hj, canonical2309 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node934 node934Labels = Sparse.eval nodeValue934 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 934) = mixedMoment B node934 node934Labels := rfl
  simpa [nodeValue934, Sparse.eval] using hc.symm

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

theorem sound1051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1051 node1051Labels = Sparse.eval nodeValue1051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1051) = mixedMoment B node1051 node1051Labels := rfl
  simpa [nodeValue1051, Sparse.eval] using hc.symm

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

theorem sound1131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1131 node1131Labels = Sparse.eval nodeValue1131 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1131) = mixedMoment B node1131 node1131Labels := rfl
  simpa [nodeValue1131, Sparse.eval] using hc.symm

theorem sound1144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1144 node1144Labels = Sparse.eval nodeValue1144 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1144) = mixedMoment B node1144 node1144Labels := rfl
  simpa [nodeValue1144, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node157 node157Labels = Sparse.eval nodeValue157 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue157 (familyPairVector B) := singlePair157 B _hB
    _ = _ := by
      norm_num [singlePairValue157, nodeValue157, Sparse.eval, mixedVector]
      ring

theorem sound161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node161 node161Labels = Sparse.eval nodeValue161 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue161 (familyPairVector B) := singlePair161 B _hB
    _ = _ := by
      norm_num [singlePairValue161, nodeValue161, Sparse.eval, mixedVector]
      ring

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

theorem sound1242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1242 node1242Labels = Sparse.eval nodeValue1242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1242) = mixedMoment B node1242 node1242Labels := rfl
  simpa [nodeValue1242, Sparse.eval] using hc.symm

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

theorem sound1301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1301 node1301Labels = Sparse.eval nodeValue1301 (mixedVector B) := by
  have h := singleton1301 B _hB
  rw [sound157 B _hB _hF] at h
  norm_num [nodeValue1301, nodeValue157, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1312 node1312Labels = Sparse.eval nodeValue1312 (mixedVector B) := by
  have h := singleton1312 B _hB
  rw [sound161 B _hB _hF] at h
  norm_num [nodeValue1312, nodeValue161, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound1518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1518 node1518Labels = Sparse.eval nodeValue1518 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1518) = mixedMoment B node1518 node1518Labels := rfl
  simpa [nodeValue1518, Sparse.eval] using hc.symm

theorem sound1521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1521 node1521Labels = Sparse.eval nodeValue1521 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1521) = mixedMoment B node1521 node1521Labels := rfl
  simpa [nodeValue1521, Sparse.eval] using hc.symm

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

theorem sound1692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1692 node1692Labels = Sparse.eval nodeValue1692 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1692) = mixedMoment B node1692 node1692Labels := rfl
  simpa [nodeValue1692, Sparse.eval] using hc.symm

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

theorem sound1752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1752 node1752Labels = Sparse.eval nodeValue1752 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1752) = mixedMoment B node1752 node1752Labels := rfl
  simpa [nodeValue1752, Sparse.eval] using hc.symm

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

theorem sound407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node407 node407Labels = Sparse.eval nodeValue407 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue407 (familyPairVector B) := singlePair407 B _hB
    _ = _ := by norm_num [singlePairValue407, nodeValue407, Sparse.eval, mixedVector]

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

theorem sound2770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2770 node2770Labels = Sparse.eval nodeValue2770 (mixedVector B) := by
  have h := singleton2770 B _hB
  rw [sound407 B _hB _hF] at h
  norm_num [nodeValue2770, nodeValue407, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound3264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3264 node3264Labels = Sparse.eval nodeValue3264 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3264) = mixedMoment B node3264 node3264Labels := rfl
  simpa [nodeValue3264, Sparse.eval] using hc.symm

theorem sound3276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3276 node3276Labels = Sparse.eval nodeValue3276 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3276) = mixedMoment B node3276 node3276Labels := rfl
  simpa [nodeValue3276, Sparse.eval] using hc.symm

theorem sound3300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3300 node3300Labels = Sparse.eval nodeValue3300 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3300) = mixedMoment B node3300 node3300Labels := rfl
  simpa [nodeValue3300, Sparse.eval] using hc.symm

theorem sound3309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3309 node3309Labels = Sparse.eval nodeValue3309 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3309) = mixedMoment B node3309 node3309Labels := rfl
  simpa [nodeValue3309, Sparse.eval] using hc.symm

theorem sound3312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3312 node3312Labels = Sparse.eval nodeValue3312 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3312) = mixedMoment B node3312 node3312Labels := rfl
  simpa [nodeValue3312, Sparse.eval] using hc.symm

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

theorem sound3634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3634 node3634Labels = Sparse.eval nodeValue3634 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3634) = mixedMoment B node3634 node3634Labels := rfl
  simpa [nodeValue3634, Sparse.eval] using hc.symm

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

theorem sound605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node605 node605Labels = Sparse.eval nodeValue605 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 605) = mixedMoment B node605 node605Labels := rfl
  simpa [nodeValue605, Sparse.eval] using hc.symm

theorem sound609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node609 node609Labels = Sparse.eval nodeValue609 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 609) = mixedMoment B node609 node609Labels := rfl
  simpa [nodeValue609, Sparse.eval] using hc.symm

theorem sound619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node619 node619Labels = Sparse.eval nodeValue619 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 619) = mixedMoment B node619 node619Labels := rfl
  simpa [nodeValue619, Sparse.eval] using hc.symm

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

theorem sound4177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4177 node4177Labels = Sparse.eval nodeValue4177 (mixedVector B) := by
  have h := singleton4177 B _hB
  rw [sound605 B _hB _hF, sound1518 B _hB _hF] at h
  norm_num [nodeValue4177, nodeValue605, nodeValue1518, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4181 node4181Labels = Sparse.eval nodeValue4181 (mixedVector B) := by
  have h := singleton4181 B _hB
  rw [sound609 B _hB _hF, sound1521 B _hB _hF] at h
  norm_num [nodeValue4181, nodeValue609, nodeValue1521, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4191 node4191Labels = Sparse.eval nodeValue4191 (mixedVector B) := by
  have h := singleton4191 B _hB
  rw [sound619 B _hB _hF, sound1538 B _hB _hF] at h
  norm_num [nodeValue4191, nodeValue619, nodeValue1538, Sparse.eval] at h ⊢
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

theorem sound4356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4356 node4356Labels = Sparse.eval nodeValue4356 (mixedVector B) := by
  have h := singleton4356 B _hB
  rw [sound934 B _hB _hF, sound1692 B _hB _hF] at h
  norm_num [nodeValue4356, nodeValue934, nodeValue1692, Sparse.eval] at h ⊢
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

theorem sound4468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4468 node4468Labels = Sparse.eval nodeValue4468 (mixedVector B) := by
  have h := singleton4468 B _hB
  rw [sound1051 B _hB _hF, sound1752 B _hB _hF] at h
  norm_num [nodeValue4468, nodeValue1051, nodeValue1752, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4546 node4546Labels = Sparse.eval nodeValue4546 (mixedVector B) := by
  have h := singleton4546 B _hB
  rw [sound1131 B _hB _hF, sound3264 B _hB _hF] at h
  norm_num [nodeValue4546, nodeValue1131, nodeValue3264, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4558 node4558Labels = Sparse.eval nodeValue4558 (mixedVector B) := by
  have h := singleton4558 B _hB
  rw [sound1144 B _hB _hF, sound3276 B _hB _hF] at h
  norm_num [nodeValue4558, nodeValue1144, nodeValue3276, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4624 node4624Labels = Sparse.eval nodeValue4624 (mixedVector B) := by
  have h := singleton4624 B _hB
  rw [sound1301 B _hB _hF, sound3309 B _hB _hF] at h
  norm_num [nodeValue4624, nodeValue1301, nodeValue3309, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4628 node4628Labels = Sparse.eval nodeValue4628 (mixedVector B) := by
  have h := singleton4628 B _hB
  rw [sound1312 B _hB _hF, sound3312 B _hB _hF] at h
  norm_num [nodeValue4628, nodeValue1312, nodeValue3312, Sparse.eval] at h ⊢
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

theorem zero5309 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5309 node5309Labels = 0 := by
  exact mixedMoment_order_one B hB node5309 node5309Labels 1
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

theorem sound5296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5296 node5296Labels = Sparse.eval nodeValue5296 (mixedVector B) := by
  have h := singleton5296 B _hB
  rw [sound2770 B _hB _hF, sound3634 B _hB _hF] at h
  norm_num [nodeValue5296, nodeValue2770, nodeValue3634, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5309 node5309Labels = Sparse.eval nodeValue5309 (mixedVector B) := by
  simpa only [nodeValue5309, Sparse.eval_nil] using zero5309 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources39
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1265 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1265 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1265 + difference 0 1) (sourceB1265 + difference 1 0) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA1265 + difference 0 1) (sourceB1265 + difference 1 0) sourceC1265) = raw4303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw4303; decide +kernel
    rw [ha]
    exact (canonical4303 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1265 + difference 0 2) (sourceB1265 + difference 2 0) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA1265 + difference 0 2) (sourceB1265 + difference 2 0) sourceC1265) = raw4304 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw4304; decide +kernel
    rw [ha]
    exact (canonical4304 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1265 + difference 0 3) (sourceB1265 + difference 3 0) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA1265 + difference 0 3) (sourceB1265 + difference 3 0) sourceC1265) = raw4305 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw4305; decide +kernel
    rw [ha]
    exact (canonical4305 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1265 + difference 0 4) (sourceB1265 + difference 4 0) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA1265 + difference 0 4) (sourceB1265 + difference 4 0) sourceC1265) = raw10215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw10215; decide +kernel
    rw [ha]
    exact (canonical10215 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1265 + difference 0 5) (sourceB1265 + difference 5 0) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5309) := by
    have ha : (tripleCharges (sourceA1265 + difference 0 5) (sourceB1265 + difference 5 0) sourceC1265) = raw4306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw4306; decide +kernel
    rw [ha]
    exact (canonical4306 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1265 + difference 1 0) (sourceB1265 + difference 0 1) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4177) := by
    have ha : (tripleCharges (sourceA1265 + difference 1 0) (sourceB1265 + difference 0 1) sourceC1265) = raw20384 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20384; decide +kernel
    rw [ha]
    exact (canonical20384 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1265 + difference 1 2) (sourceB1265 + difference 2 1) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1265 + difference 1 2) (sourceB1265 + difference 2 1) sourceC1265) = raw20385 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20385; decide +kernel
    rw [ha]
    exact (canonical20385 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1265 + difference 1 3) (sourceB1265 + difference 3 1) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1265 + difference 1 3) (sourceB1265 + difference 3 1) sourceC1265) = raw20386 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20386; decide +kernel
    rw [ha]
    exact (canonical20386 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1265 + difference 1 4) (sourceB1265 + difference 4 1) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1265 + difference 1 4) (sourceB1265 + difference 4 1) sourceC1265) = raw4287 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw4287; decide +kernel
    rw [ha]
    exact (canonical4287 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1265 + difference 1 5) (sourceB1265 + difference 5 1) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1265 + difference 1 5) (sourceB1265 + difference 5 1) sourceC1265) = raw10198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw10198; decide +kernel
    rw [ha]
    exact (canonical10198 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1265 + difference 2 0) (sourceB1265 + difference 0 2) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4177) := by
    have ha : (tripleCharges (sourceA1265 + difference 2 0) (sourceB1265 + difference 0 2) sourceC1265) = raw20387 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20387; decide +kernel
    rw [ha]
    exact (canonical20387 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1265 + difference 2 1) (sourceB1265 + difference 1 2) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1265 + difference 2 1) (sourceB1265 + difference 1 2) sourceC1265) = raw20388 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20388; decide +kernel
    rw [ha]
    exact (canonical20388 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1265 + difference 2 3) (sourceB1265 + difference 3 2) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1265 + difference 2 3) (sourceB1265 + difference 3 2) sourceC1265) = raw20389 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20389; decide +kernel
    rw [ha]
    exact (canonical20389 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1265 + difference 2 4) (sourceB1265 + difference 4 2) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1265 + difference 2 4) (sourceB1265 + difference 4 2) sourceC1265) = raw4292 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw4292; decide +kernel
    rw [ha]
    exact (canonical4292 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1265 + difference 2 5) (sourceB1265 + difference 5 2) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1265 + difference 2 5) (sourceB1265 + difference 5 2) sourceC1265) = raw10202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw10202; decide +kernel
    rw [ha]
    exact (canonical10202 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1265 + difference 3 0) (sourceB1265 + difference 0 3) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4177) := by
    have ha : (tripleCharges (sourceA1265 + difference 3 0) (sourceB1265 + difference 0 3) sourceC1265) = raw20390 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20390; decide +kernel
    rw [ha]
    exact (canonical20390 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1265 + difference 3 1) (sourceB1265 + difference 1 3) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1265 + difference 3 1) (sourceB1265 + difference 1 3) sourceC1265) = raw20391 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20391; decide +kernel
    rw [ha]
    exact (canonical20391 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1265 + difference 3 2) (sourceB1265 + difference 2 3) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1265 + difference 3 2) (sourceB1265 + difference 2 3) sourceC1265) = raw20392 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20392; decide +kernel
    rw [ha]
    exact (canonical20392 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1265 + difference 3 4) (sourceB1265 + difference 4 3) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1265 + difference 3 4) (sourceB1265 + difference 4 3) sourceC1265) = raw4297 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw4297; decide +kernel
    rw [ha]
    exact (canonical4297 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1265 + difference 3 5) (sourceB1265 + difference 5 3) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1265 + difference 3 5) (sourceB1265 + difference 5 3) sourceC1265) = raw10206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw10206; decide +kernel
    rw [ha]
    exact (canonical10206 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1265 + difference 4 0) (sourceB1265 + difference 0 4) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4191) := by
    have ha : (tripleCharges (sourceA1265 + difference 4 0) (sourceB1265 + difference 0 4) sourceC1265) = raw20393 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20393; decide +kernel
    rw [ha]
    exact (canonical20393 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1265 + difference 4 1) (sourceB1265 + difference 1 4) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4558) := by
    have ha : (tripleCharges (sourceA1265 + difference 4 1) (sourceB1265 + difference 1 4) sourceC1265) = raw20394 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20394; decide +kernel
    rw [ha]
    exact (canonical20394 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1265 + difference 4 2) (sourceB1265 + difference 2 4) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4558) := by
    have ha : (tripleCharges (sourceA1265 + difference 4 2) (sourceB1265 + difference 2 4) sourceC1265) = raw20395 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20395; decide +kernel
    rw [ha]
    exact (canonical20395 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1265 + difference 4 3) (sourceB1265 + difference 3 4) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4558) := by
    have ha : (tripleCharges (sourceA1265 + difference 4 3) (sourceB1265 + difference 3 4) sourceC1265) = raw20396 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20396; decide +kernel
    rw [ha]
    exact (canonical20396 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1265 + difference 4 5) (sourceB1265 + difference 5 4) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4628) := by
    have ha : (tripleCharges (sourceA1265 + difference 4 5) (sourceB1265 + difference 5 4) sourceC1265) = raw10210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw10210; decide +kernel
    rw [ha]
    exact (canonical10210 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1265 + difference 5 0) (sourceB1265 + difference 0 5) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4181) := by
    have ha : (tripleCharges (sourceA1265 + difference 5 0) (sourceB1265 + difference 0 5) sourceC1265) = raw19719 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw19719; decide +kernel
    rw [ha]
    exact (canonical19719 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1265 + difference 5 1) (sourceB1265 + difference 1 5) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA1265 + difference 5 1) (sourceB1265 + difference 1 5) sourceC1265) = raw19720 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw19720; decide +kernel
    rw [ha]
    exact (canonical19720 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1265 + difference 5 2) (sourceB1265 + difference 2 5) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA1265 + difference 5 2) (sourceB1265 + difference 2 5) sourceC1265) = raw19721 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw19721; decide +kernel
    rw [ha]
    exact (canonical19721 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1265 + difference 5 3) (sourceB1265 + difference 3 5) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA1265 + difference 5 3) (sourceB1265 + difference 3 5) sourceC1265) = raw19722 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw19722; decide +kernel
    rw [ha]
    exact (canonical19722 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1265 + difference 5 4) (sourceB1265 + difference 4 5) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1265 + difference 5 4) (sourceB1265 + difference 4 5) sourceC1265) = raw4307 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw4307; decide +kernel
    rw [ha]
    exact (canonical4307 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1265 sourceB1265 sourceC1265
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1265, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1095 : Integer.Sparse.reindex keyMap MixedData.row1095 = numericRow1095 := by decide +kernel

theorem numericCheck1095 (x : Master → ℝ) : Integer.Sparse.eval numericRow1095 x =
    (288 : ℝ) * reducedSource1095 x := by
  norm_num [numericRow1095, reducedSource1095, Integer.Sparse.eval, Sparse.eval, nodeValue4177, nodeValue4181, nodeValue4191, nodeValue4356, nodeValue4468, nodeValue4546, nodeValue4558, nodeValue4608, nodeValue4624, nodeValue4628, nodeValue5174, nodeValue5296, nodeValue5309]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1095 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1095 (mixedVector B) = 0 := by
  have h4177 : mixedVector B (Sum.inr 4177) = Sparse.eval nodeValue4177 (mixedVector B) := by
    change mixedMoment B node4177 node4177Labels = _
    exact sound4177 B hB hF
  have h4181 : mixedVector B (Sum.inr 4181) = Sparse.eval nodeValue4181 (mixedVector B) := by
    change mixedMoment B node4181 node4181Labels = _
    exact sound4181 B hB hF
  have h4191 : mixedVector B (Sum.inr 4191) = Sparse.eval nodeValue4191 (mixedVector B) := by
    change mixedMoment B node4191 node4191Labels = _
    exact sound4191 B hB hF
  have h4356 : mixedVector B (Sum.inr 4356) = Sparse.eval nodeValue4356 (mixedVector B) := by
    change mixedMoment B node4356 node4356Labels = _
    exact sound4356 B hB hF
  have h4468 : mixedVector B (Sum.inr 4468) = Sparse.eval nodeValue4468 (mixedVector B) := by
    change mixedMoment B node4468 node4468Labels = _
    exact sound4468 B hB hF
  have h4546 : mixedVector B (Sum.inr 4546) = Sparse.eval nodeValue4546 (mixedVector B) := by
    change mixedMoment B node4546 node4546Labels = _
    exact sound4546 B hB hF
  have h4558 : mixedVector B (Sum.inr 4558) = Sparse.eval nodeValue4558 (mixedVector B) := by
    change mixedMoment B node4558 node4558Labels = _
    exact sound4558 B hB hF
  have h4608 : mixedVector B (Sum.inr 4608) = Sparse.eval nodeValue4608 (mixedVector B) := by
    change mixedMoment B node4608 node4608Labels = _
    exact sound4608 B hB hF
  have h4624 : mixedVector B (Sum.inr 4624) = Sparse.eval nodeValue4624 (mixedVector B) := by
    change mixedMoment B node4624 node4624Labels = _
    exact sound4624 B hB hF
  have h4628 : mixedVector B (Sum.inr 4628) = Sparse.eval nodeValue4628 (mixedVector B) := by
    change mixedMoment B node4628 node4628Labels = _
    exact sound4628 B hB hF
  have h5174 : mixedVector B (Sum.inr 5174) = Sparse.eval nodeValue5174 (mixedVector B) := by
    change mixedMoment B node5174 node5174Labels = _
    exact sound5174_e B hB hF
  have h5296 : mixedVector B (Sum.inr 5296) = Sparse.eval nodeValue5296 (mixedVector B) := by
    change mixedMoment B node5296 node5296Labels = _
    exact sound5296 B hB hF
  have h5309 : mixedVector B (Sum.inr 5309) = Sparse.eval nodeValue5309 (mixedVector B) := by
    change mixedMoment B node5309 node5309Labels = _
    exact sound5309 B hB hF
  simpa only [sourceForm1265, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4177, h4181, h4191, h4356, h4468, h4546, h4558, h4608, h4624, h4628, h5174, h5296, h5309, reducedSource1095] using sourceEq1265 B hB

theorem rowSound1095_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1095 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1095, numericCheck1095, reducedZero1095 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095_e_oai
