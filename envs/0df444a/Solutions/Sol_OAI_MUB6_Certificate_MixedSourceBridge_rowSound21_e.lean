-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound21_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T23:07:20.969165+00:00
-- url     : https://prove2.me/submissions/bba76f84-12e3-4503-bb87-a67b13e443b9

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E115
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5492_e

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

theorem canonical2319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2319 raw2319Labels = mixedMoment B node5305 node5305Labels := by
  calc
    mixedMoment B raw2319 raw2319Labels = mixedMoment B raw2319step0 raw2319step0Labels := by
      have ha : raw2319step0 = (fun i j => raw2319 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2319step0 raw2319; decide +kernel
      have hl : raw2319step0Labels = raw2319Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2319 raw2319Labels permutation2 permutation4
    mixedMoment B raw2319step0 raw2319step0Labels = mixedMoment B raw2319step1 raw2319step1Labels := by
      have ha : raw2319step1 = raw2319step0 := by apply Matrix.ext; unfold raw2319step1 raw2319step0; decide +kernel
      have hl : raw2319step0Labels = labelEmbedding7 ∘ raw2319step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2319step0 raw2319step0Labels raw2319step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5305 node5305Labels := by rfl

theorem canonical2320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2320 raw2320Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw2320 raw2320Labels = mixedMoment B raw2320step0 raw2320step0Labels := by
      have ha : raw2320step0 = (fun i j => raw2320 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2320step0 raw2320; decide +kernel
      have hl : raw2320step0Labels = raw2320Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2320 raw2320Labels permutation2 permutation4
    _ = mixedMoment B node2783 node2783Labels := by rfl

theorem canonical2321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2321 raw2321Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw2321 raw2321Labels = mixedMoment B raw2321step0 raw2321step0Labels := by
      have ha : raw2321step0 = (fun i j => raw2321 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2321step0 raw2321; decide +kernel
      have hl : raw2321step0Labels = raw2321Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2321 raw2321Labels permutation7 permutation6
    mixedMoment B raw2321step0 raw2321step0Labels = mixedMoment B raw2321step1 raw2321step1Labels := by
      have ha : raw2321step1 = raw2321step0 := by apply Matrix.ext; unfold raw2321step1 raw2321step0; decide +kernel
      have hl : raw2321step0Labels = labelEmbedding1 ∘ raw2321step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2321step0 raw2321step0Labels raw2321step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2783 node2783Labels := by rfl

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

theorem canonical2559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2559 raw2559Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw2559 raw2559Labels = mixedMoment B raw2559step0 raw2559step0Labels := by
      have ha : raw2559step0 = (fun i j => raw2559 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2559step0 raw2559; decide +kernel
      have hl : raw2559step0Labels = raw2559Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2559 raw2559Labels permutation8 permutation4
    mixedMoment B raw2559step0 raw2559step0Labels = mixedMoment B raw2559step1 raw2559step1Labels := by
      have ha : raw2559step1 = raw2559step0 := by apply Matrix.ext; unfold raw2559step1 raw2559step0; decide +kernel
      have hl : raw2559step0Labels = labelEmbedding7 ∘ raw2559step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2559step0 raw2559step0Labels raw2559step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

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

theorem canonical2560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2560 raw2560Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw2560 raw2560Labels = mixedMoment B raw2560step0 raw2560step0Labels := by
      have ha : raw2560step0 = (fun i j => raw2560 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2560step0 raw2560; decide +kernel
      have hl : raw2560step0Labels = raw2560Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2560 raw2560Labels permutation8 permutation4
    _ = mixedMoment B node3888 node3888Labels := by rfl

theorem canonical2561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2561 raw2561Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw2561 raw2561Labels = mixedMoment B raw2561step0 raw2561step0Labels := by
      have ha : raw2561step0 = (fun i j => raw2561 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2561step0 raw2561; decide +kernel
      have hl : raw2561step0Labels = raw2561Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2561 raw2561Labels permutation10 permutation6
    mixedMoment B raw2561step0 raw2561step0Labels = mixedMoment B raw2561step1 raw2561step1Labels := by
      have ha : raw2561step1 = -raw2561step0 := by apply Matrix.ext; change ∀ i j, raw2561step1 i j = -(raw2561step0 i j); unfold raw2561step1 raw2561step0; decide +kernel
      have hl : raw2561step1Labels = raw2561step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2561step1 raw2561step1Labels = mixedMoment B raw2561step2 raw2561step2Labels := by
      have ha : raw2561step2 = raw2561step1 := by apply Matrix.ext; unfold raw2561step2 raw2561step1; decide +kernel
      have hl : raw2561step1Labels = labelEmbedding1 ∘ raw2561step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2561step1 raw2561step1Labels raw2561step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3913 node3913Labels := by rfl

theorem canonical2607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2607 raw2607Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw2607 raw2607Labels = mixedMoment B raw2607step0 raw2607step0Labels := by
      have ha : raw2607step0 = (fun i j => raw2607 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2607step0 raw2607; decide +kernel
      have hl : raw2607step0Labels = raw2607Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2607 raw2607Labels permutation32 permutation4
    mixedMoment B raw2607step0 raw2607step0Labels = mixedMoment B raw2607step1 raw2607step1Labels := by
      have ha : raw2607step1 = raw2607step0 := by apply Matrix.ext; unfold raw2607step1 raw2607step0; decide +kernel
      have hl : raw2607step0Labels = labelEmbedding7 ∘ raw2607step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2607step0 raw2607step0Labels raw2607step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

theorem canonical2608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2608 raw2608Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw2608 raw2608Labels = mixedMoment B raw2608step0 raw2608step0Labels := by
      have ha : raw2608step0 = (fun i j => raw2608 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2608step0 raw2608; decide +kernel
      have hl : raw2608step0Labels = raw2608Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2608 raw2608Labels permutation32 permutation4
    _ = mixedMoment B node3983 node3983Labels := by rfl

theorem canonical2609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2609 raw2609Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw2609 raw2609Labels = mixedMoment B raw2609step0 raw2609step0Labels := by
      have ha : raw2609step0 = (fun i j => raw2609 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2609step0 raw2609; decide +kernel
      have hl : raw2609step0Labels = raw2609Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2609 raw2609Labels permutation151 permutation6
    mixedMoment B raw2609step0 raw2609step0Labels = mixedMoment B raw2609step1 raw2609step1Labels := by
      have ha : raw2609step1 = raw2609step0 := by apply Matrix.ext; unfold raw2609step1 raw2609step0; decide +kernel
      have hl : raw2609step0Labels = labelEmbedding1 ∘ raw2609step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2609step0 raw2609step0Labels raw2609step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3983 node3983Labels := by rfl

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

theorem canonical2855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2855 raw2855Labels = mixedMoment B node5495 node5495Labels := by
  calc
    mixedMoment B raw2855 raw2855Labels = mixedMoment B raw2855step0 raw2855step0Labels := by
      have hz : ∀ j, raw2855 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2855step0 = (fun i j => raw2855 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2855step0 raw2855; decide +kernel
      have hl : raw2855step0Labels = raw2855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2855 raw2855Labels permutation434 hz
    mixedMoment B raw2855step0 raw2855step0Labels = mixedMoment B raw2855step1 raw2855step1Labels := by
      have hz : ∀ j, raw2855step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2855step1 = (fun i j => raw2855step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2855step1 raw2855step0; decide +kernel
      have hl : raw2855step1Labels = raw2855step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2855step0 raw2855step0Labels permutation80 hz
    mixedMoment B raw2855step1 raw2855step1Labels = mixedMoment B raw2855step2 raw2855step2Labels := by
      have hz : ∀ j, raw2855step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2855step2 = (fun i j => raw2855step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2855step2 raw2855step1; decide +kernel
      have hl : raw2855step2Labels = raw2855step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2855step1 raw2855step1Labels permutation14 hz
    mixedMoment B raw2855step2 raw2855step2Labels = mixedMoment B raw2855step3 raw2855step3Labels := by
      have ha : raw2855step3 = (fun i j => raw2855step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2855step3 raw2855step2; decide +kernel
      have hl : raw2855step3Labels = raw2855step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2855step2 raw2855step2Labels permutation6 permutation6
    mixedMoment B raw2855step3 raw2855step3Labels = mixedMoment B raw2855step4 raw2855step4Labels := by
      have ha : raw2855step4 = raw2855step3 := by apply Matrix.ext; unfold raw2855step4 raw2855step3; decide +kernel
      have hl : raw2855step3Labels = labelEmbedding9 ∘ raw2855step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2855step3 raw2855step3Labels raw2855step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5495 node5495Labels := by rfl

theorem canonical2860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2860 raw2860Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw2860 raw2860Labels = mixedMoment B raw2860step0 raw2860step0Labels := by
      have hz : ∀ j, raw2860 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2860step0 = (fun i j => raw2860 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2860step0 raw2860; decide +kernel
      have hl : raw2860step0Labels = raw2860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2860 raw2860Labels permutation434 hz
    mixedMoment B raw2860step0 raw2860step0Labels = mixedMoment B raw2860step1 raw2860step1Labels := by
      have hz : ∀ j, raw2860step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2860step1 = (fun i j => raw2860step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2860step1 raw2860step0; decide +kernel
      have hl : raw2860step1Labels = raw2860step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2860step0 raw2860step0Labels permutation80 hz
    mixedMoment B raw2860step1 raw2860step1Labels = mixedMoment B raw2860step2 raw2860step2Labels := by
      have ha : raw2860step2 = (fun i j => raw2860step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2860step2 raw2860step1; decide +kernel
      have hl : raw2860step2Labels = raw2860step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2860step1 raw2860step1Labels permutation10 permutation2
    _ = mixedMoment B node5492 node5492Labels := by rfl

theorem canonical2865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2865 raw2865Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw2865 raw2865Labels = mixedMoment B raw2865step0 raw2865step0Labels := by
      have hz : ∀ j, raw2865 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2865step0 = (fun i j => raw2865 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2865step0 raw2865; decide +kernel
      have hl : raw2865step0Labels = raw2865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2865 raw2865Labels permutation434 hz
    mixedMoment B raw2865step0 raw2865step0Labels = mixedMoment B raw2865step1 raw2865step1Labels := by
      have hz : ∀ j, raw2865step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2865step1 = (fun i j => raw2865step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2865step1 raw2865step0; decide +kernel
      have hl : raw2865step1Labels = raw2865step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2865step0 raw2865step0Labels permutation56 hz
    mixedMoment B raw2865step1 raw2865step1Labels = mixedMoment B raw2865step2 raw2865step2Labels := by
      have ha : raw2865step2 = (fun i j => raw2865step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2865step2 raw2865step1; decide +kernel
      have hl : raw2865step2Labels = raw2865step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2865step1 raw2865step1Labels permutation10 permutation2
    _ = mixedMoment B node5492 node5492Labels := by rfl

theorem canonical2870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2870 raw2870Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw2870 raw2870Labels = mixedMoment B raw2870step0 raw2870step0Labels := by
      have hz : ∀ j, raw2870 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2870step0 = (fun i j => raw2870 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2870step0 raw2870; decide +kernel
      have hl : raw2870step0Labels = raw2870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2870 raw2870Labels permutation346 hz
    mixedMoment B raw2870step0 raw2870step0Labels = mixedMoment B raw2870step1 raw2870step1Labels := by
      have hz : ∀ j, raw2870step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2870step1 = (fun i j => raw2870step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2870step1 raw2870step0; decide +kernel
      have hl : raw2870step1Labels = raw2870step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2870step0 raw2870step0Labels permutation56 hz
    mixedMoment B raw2870step1 raw2870step1Labels = mixedMoment B raw2870step2 raw2870step2Labels := by
      have ha : raw2870step2 = (fun i j => raw2870step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2870step2 raw2870step1; decide +kernel
      have hl : raw2870step2Labels = raw2870step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2870step1 raw2870step1Labels permutation10 permutation2
    _ = mixedMoment B node5492 node5492Labels := by rfl

theorem canonical2871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2871 raw2871Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw2871 raw2871Labels = mixedMoment B raw2871step0 raw2871step0Labels := by
      have hz : ∀ j, raw2871 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2871step0 = (fun i j => raw2871 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2871step0 raw2871; decide +kernel
      have hl : raw2871step0Labels = raw2871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2871 raw2871Labels permutation434 hz
    mixedMoment B raw2871step0 raw2871step0Labels = mixedMoment B raw2871step1 raw2871step1Labels := by
      have hz : ∀ j, raw2871step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2871step1 = (fun i j => raw2871step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2871step1 raw2871step0; decide +kernel
      have hl : raw2871step1Labels = raw2871step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2871step0 raw2871step0Labels permutation80 hz
    mixedMoment B raw2871step1 raw2871step1Labels = mixedMoment B raw2871step2 raw2871step2Labels := by
      have hz : ∀ j, raw2871step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2871step2 = (fun i j => raw2871step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2871step2 raw2871step1; decide +kernel
      have hl : raw2871step2Labels = raw2871step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2871step1 raw2871step1Labels permutation14 hz
    mixedMoment B raw2871step2 raw2871step2Labels = mixedMoment B raw2871step3 raw2871step3Labels := by
      have ha : raw2871step3 = (fun i j => raw2871step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2871step3 raw2871step2; decide +kernel
      have hl : raw2871step3Labels = raw2871step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2871step2 raw2871step2Labels permutation2 permutation3
    mixedMoment B raw2871step3 raw2871step3Labels = mixedMoment B raw2871step4 raw2871step4Labels := by
      have ha : raw2871step4 = raw2871step3 := by apply Matrix.ext; unfold raw2871step4 raw2871step3; decide +kernel
      have hl : raw2871step3Labels = labelEmbedding6 ∘ raw2871step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2871step3 raw2871step3Labels raw2871step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

theorem canonical2872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2872 raw2872Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw2872 raw2872Labels = mixedMoment B raw2872step0 raw2872step0Labels := by
      have hz : ∀ j, raw2872 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2872step0 = (fun i j => raw2872 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2872step0 raw2872; decide +kernel
      have hl : raw2872step0Labels = raw2872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2872 raw2872Labels permutation434 hz
    mixedMoment B raw2872step0 raw2872step0Labels = mixedMoment B raw2872step1 raw2872step1Labels := by
      have hz : ∀ j, raw2872step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2872step1 = (fun i j => raw2872step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2872step1 raw2872step0; decide +kernel
      have hl : raw2872step1Labels = raw2872step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2872step0 raw2872step0Labels permutation80 hz
    mixedMoment B raw2872step1 raw2872step1Labels = mixedMoment B raw2872step2 raw2872step2Labels := by
      have ha : raw2872step2 = (fun i j => raw2872step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2872step2 raw2872step1; decide +kernel
      have hl : raw2872step2Labels = raw2872step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2872step1 raw2872step1Labels permutation31 permutation2
    mixedMoment B raw2872step2 raw2872step2Labels = mixedMoment B raw2872step3 raw2872step3Labels := by
      have ha : raw2872step3 = -raw2872step2 := by apply Matrix.ext; change ∀ i j, raw2872step3 i j = -(raw2872step2 i j); unfold raw2872step3 raw2872step2; decide +kernel
      have hl : raw2872step3Labels = raw2872step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5451 node5451Labels := by rfl

theorem canonical2873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2873 raw2873Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw2873 raw2873Labels = mixedMoment B raw2873step0 raw2873step0Labels := by
      have hz : ∀ j, raw2873 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2873step0 = (fun i j => raw2873 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2873step0 raw2873; decide +kernel
      have hl : raw2873step0Labels = raw2873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2873 raw2873Labels permutation434 hz
    mixedMoment B raw2873step0 raw2873step0Labels = mixedMoment B raw2873step1 raw2873step1Labels := by
      have hz : ∀ j, raw2873step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2873step1 = (fun i j => raw2873step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2873step1 raw2873step0; decide +kernel
      have hl : raw2873step1Labels = raw2873step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2873step0 raw2873step0Labels permutation56 hz
    mixedMoment B raw2873step1 raw2873step1Labels = mixedMoment B raw2873step2 raw2873step2Labels := by
      have ha : raw2873step2 = (fun i j => raw2873step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2873step2 raw2873step1; decide +kernel
      have hl : raw2873step2Labels = raw2873step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2873step1 raw2873step1Labels permutation31 permutation2
    mixedMoment B raw2873step2 raw2873step2Labels = mixedMoment B raw2873step3 raw2873step3Labels := by
      have ha : raw2873step3 = -raw2873step2 := by apply Matrix.ext; change ∀ i j, raw2873step3 i j = -(raw2873step2 i j); unfold raw2873step3 raw2873step2; decide +kernel
      have hl : raw2873step3Labels = raw2873step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5451 node5451Labels := by rfl

theorem canonical2874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2874 raw2874Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw2874 raw2874Labels = mixedMoment B raw2874step0 raw2874step0Labels := by
      have hz : ∀ j, raw2874 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2874step0 = (fun i j => raw2874 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2874step0 raw2874; decide +kernel
      have hl : raw2874step0Labels = raw2874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2874 raw2874Labels permutation346 hz
    mixedMoment B raw2874step0 raw2874step0Labels = mixedMoment B raw2874step1 raw2874step1Labels := by
      have hz : ∀ j, raw2874step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2874step1 = (fun i j => raw2874step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2874step1 raw2874step0; decide +kernel
      have hl : raw2874step1Labels = raw2874step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2874step0 raw2874step0Labels permutation56 hz
    mixedMoment B raw2874step1 raw2874step1Labels = mixedMoment B raw2874step2 raw2874step2Labels := by
      have ha : raw2874step2 = (fun i j => raw2874step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2874step2 raw2874step1; decide +kernel
      have hl : raw2874step2Labels = raw2874step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2874step1 raw2874step1Labels permutation31 permutation2
    mixedMoment B raw2874step2 raw2874step2Labels = mixedMoment B raw2874step3 raw2874step3Labels := by
      have ha : raw2874step3 = -raw2874step2 := by apply Matrix.ext; change ∀ i j, raw2874step3 i j = -(raw2874step2 i j); unfold raw2874step3 raw2874step2; decide +kernel
      have hl : raw2874step3Labels = raw2874step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5451 node5451Labels := by rfl

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

theorem canonical3209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3209 raw3209Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw3209 raw3209Labels = mixedMoment B raw3209step0 raw3209step0Labels := by
      have hz : ∀ j, raw3209 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3209step0 = (fun i j => raw3209 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3209step0 raw3209; decide +kernel
      have hl : raw3209step0Labels = raw3209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3209 raw3209Labels permutation434 hz
    mixedMoment B raw3209step0 raw3209step0Labels = mixedMoment B raw3209step1 raw3209step1Labels := by
      have hz : ∀ j, raw3209step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3209step1 = (fun i j => raw3209step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3209step1 raw3209step0; decide +kernel
      have hl : raw3209step1Labels = raw3209step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3209step0 raw3209step0Labels permutation80 hz
    mixedMoment B raw3209step1 raw3209step1Labels = mixedMoment B raw3209step2 raw3209step2Labels := by
      have ha : raw3209step2 = (fun i j => raw3209step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3209step2 raw3209step1; decide +kernel
      have hl : raw3209step2Labels = raw3209step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3209step1 raw3209step1Labels permutation20 permutation4
    mixedMoment B raw3209step2 raw3209step2Labels = mixedMoment B raw3209step3 raw3209step3Labels := by
      have ha : raw3209step3 = raw3209step2 := by apply Matrix.ext; unfold raw3209step3 raw3209step2; decide +kernel
      have hl : raw3209step2Labels = labelEmbedding7 ∘ raw3209step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3209step2 raw3209step2Labels raw3209step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

theorem canonical3210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3210 raw3210Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw3210 raw3210Labels = mixedMoment B raw3210step0 raw3210step0Labels := by
      have hz : ∀ j, raw3210 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3210step0 = (fun i j => raw3210 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3210step0 raw3210; decide +kernel
      have hl : raw3210step0Labels = raw3210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3210 raw3210Labels permutation434 hz
    mixedMoment B raw3210step0 raw3210step0Labels = mixedMoment B raw3210step1 raw3210step1Labels := by
      have hz : ∀ j, raw3210step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3210step1 = (fun i j => raw3210step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3210step1 raw3210step0; decide +kernel
      have hl : raw3210step1Labels = raw3210step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3210step0 raw3210step0Labels permutation56 hz
    mixedMoment B raw3210step1 raw3210step1Labels = mixedMoment B raw3210step2 raw3210step2Labels := by
      have ha : raw3210step2 = (fun i j => raw3210step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3210step2 raw3210step1; decide +kernel
      have hl : raw3210step2Labels = raw3210step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3210step1 raw3210step1Labels permutation20 permutation4
    mixedMoment B raw3210step2 raw3210step2Labels = mixedMoment B raw3210step3 raw3210step3Labels := by
      have ha : raw3210step3 = raw3210step2 := by apply Matrix.ext; unfold raw3210step3 raw3210step2; decide +kernel
      have hl : raw3210step2Labels = labelEmbedding7 ∘ raw3210step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3210step2 raw3210step2Labels raw3210step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

theorem canonical3211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3211 raw3211Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw3211 raw3211Labels = mixedMoment B raw3211step0 raw3211step0Labels := by
      have hz : ∀ j, raw3211 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3211step0 = (fun i j => raw3211 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3211step0 raw3211; decide +kernel
      have hl : raw3211step0Labels = raw3211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3211 raw3211Labels permutation346 hz
    mixedMoment B raw3211step0 raw3211step0Labels = mixedMoment B raw3211step1 raw3211step1Labels := by
      have hz : ∀ j, raw3211step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3211step1 = (fun i j => raw3211step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3211step1 raw3211step0; decide +kernel
      have hl : raw3211step1Labels = raw3211step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3211step0 raw3211step0Labels permutation56 hz
    mixedMoment B raw3211step1 raw3211step1Labels = mixedMoment B raw3211step2 raw3211step2Labels := by
      have ha : raw3211step2 = (fun i j => raw3211step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3211step2 raw3211step1; decide +kernel
      have hl : raw3211step2Labels = raw3211step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3211step1 raw3211step1Labels permutation20 permutation4
    mixedMoment B raw3211step2 raw3211step2Labels = mixedMoment B raw3211step3 raw3211step3Labels := by
      have ha : raw3211step3 = raw3211step2 := by apply Matrix.ext; unfold raw3211step3 raw3211step2; decide +kernel
      have hl : raw3211step2Labels = labelEmbedding7 ∘ raw3211step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3211step2 raw3211step2Labels raw3211step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

theorem canonical3212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3212 raw3212Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw3212 raw3212Labels = mixedMoment B raw3212step0 raw3212step0Labels := by
      have hz : ∀ j, raw3212 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3212step0 = (fun i j => raw3212 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3212step0 raw3212; decide +kernel
      have hl : raw3212step0Labels = raw3212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3212 raw3212Labels permutation434 hz
    mixedMoment B raw3212step0 raw3212step0Labels = mixedMoment B raw3212step1 raw3212step1Labels := by
      have hz : ∀ j, raw3212step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3212step1 = (fun i j => raw3212step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3212step1 raw3212step0; decide +kernel
      have hl : raw3212step1Labels = raw3212step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3212step0 raw3212step0Labels permutation80 hz
    mixedMoment B raw3212step1 raw3212step1Labels = mixedMoment B raw3212step2 raw3212step2Labels := by
      have hz : ∀ j, raw3212step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3212step2 = (fun i j => raw3212step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3212step2 raw3212step1; decide +kernel
      have hl : raw3212step2Labels = raw3212step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3212step1 raw3212step1Labels permutation14 hz
    mixedMoment B raw3212step2 raw3212step2Labels = mixedMoment B raw3212step3 raw3212step3Labels := by
      have ha : raw3212step3 = (fun i j => raw3212step2 (permutation6 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3212step3 raw3212step2; decide +kernel
      have hl : raw3212step3Labels = raw3212step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3212step2 raw3212step2Labels permutation6 permutation4
    mixedMoment B raw3212step3 raw3212step3Labels = mixedMoment B raw3212step4 raw3212step4Labels := by
      have ha : raw3212step4 = -raw3212step3 := by apply Matrix.ext; change ∀ i j, raw3212step4 i j = -(raw3212step3 i j); unfold raw3212step4 raw3212step3; decide +kernel
      have hl : raw3212step4Labels = raw3212step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3212step4 raw3212step4Labels = mixedMoment B raw3212step5 raw3212step5Labels := by
      have ha : raw3212step5 = raw3212step4 := by apply Matrix.ext; unfold raw3212step5 raw3212step4; decide +kernel
      have hl : raw3212step4Labels = labelEmbedding7 ∘ raw3212step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3212step4 raw3212step4Labels raw3212step5Labels labelEmbedding7 hl
    _ = mixedMoment B node5455 node5455Labels := by rfl

theorem canonical3213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3213 raw3213Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw3213 raw3213Labels = mixedMoment B raw3213step0 raw3213step0Labels := by
      have hz : ∀ j, raw3213 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3213step0 = (fun i j => raw3213 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3213step0 raw3213; decide +kernel
      have hl : raw3213step0Labels = raw3213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3213 raw3213Labels permutation434 hz
    mixedMoment B raw3213step0 raw3213step0Labels = mixedMoment B raw3213step1 raw3213step1Labels := by
      have hz : ∀ j, raw3213step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3213step1 = (fun i j => raw3213step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3213step1 raw3213step0; decide +kernel
      have hl : raw3213step1Labels = raw3213step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3213step0 raw3213step0Labels permutation80 hz
    mixedMoment B raw3213step1 raw3213step1Labels = mixedMoment B raw3213step2 raw3213step2Labels := by
      have ha : raw3213step2 = (fun i j => raw3213step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3213step2 raw3213step1; decide +kernel
      have hl : raw3213step2Labels = raw3213step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3213step1 raw3213step1Labels permutation12 permutation3
    mixedMoment B raw3213step2 raw3213step2Labels = mixedMoment B raw3213step3 raw3213step3Labels := by
      have ha : raw3213step3 = raw3213step2 := by apply Matrix.ext; unfold raw3213step3 raw3213step2; decide +kernel
      have hl : raw3213step2Labels = labelEmbedding6 ∘ raw3213step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3213step2 raw3213step2Labels raw3213step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

theorem canonical3214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3214 raw3214Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw3214 raw3214Labels = mixedMoment B raw3214step0 raw3214step0Labels := by
      have hz : ∀ j, raw3214 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3214step0 = (fun i j => raw3214 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3214step0 raw3214; decide +kernel
      have hl : raw3214step0Labels = raw3214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3214 raw3214Labels permutation434 hz
    mixedMoment B raw3214step0 raw3214step0Labels = mixedMoment B raw3214step1 raw3214step1Labels := by
      have ha : raw3214step1 = (fun i j => raw3214step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3214step1 raw3214step0; decide +kernel
      have hl : raw3214step1Labels = raw3214step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3214step0 raw3214step0Labels permutation42 permutation3
    mixedMoment B raw3214step1 raw3214step1Labels = mixedMoment B raw3214step2 raw3214step2Labels := by
      have ha : raw3214step2 = raw3214step1 := by apply Matrix.ext; unfold raw3214step2 raw3214step1; decide +kernel
      have hl : raw3214step1Labels = labelEmbedding6 ∘ raw3214step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3214step1 raw3214step1Labels raw3214step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

theorem canonical3215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3215 raw3215Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw3215 raw3215Labels = mixedMoment B raw3215step0 raw3215step0Labels := by
      have hz : ∀ j, raw3215 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3215step0 = (fun i j => raw3215 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3215step0 raw3215; decide +kernel
      have hl : raw3215step0Labels = raw3215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3215 raw3215Labels permutation346 hz
    mixedMoment B raw3215step0 raw3215step0Labels = mixedMoment B raw3215step1 raw3215step1Labels := by
      have ha : raw3215step1 = (fun i j => raw3215step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3215step1 raw3215step0; decide +kernel
      have hl : raw3215step1Labels = raw3215step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3215step0 raw3215step0Labels permutation42 permutation3
    mixedMoment B raw3215step1 raw3215step1Labels = mixedMoment B raw3215step2 raw3215step2Labels := by
      have ha : raw3215step2 = raw3215step1 := by apply Matrix.ext; unfold raw3215step2 raw3215step1; decide +kernel
      have hl : raw3215step1Labels = labelEmbedding6 ∘ raw3215step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3215step1 raw3215step1Labels raw3215step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

theorem canonical3216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3216 raw3216Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw3216 raw3216Labels = mixedMoment B raw3216step0 raw3216step0Labels := by
      have hz : ∀ j, raw3216 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3216step0 = (fun i j => raw3216 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3216step0 raw3216; decide +kernel
      have hl : raw3216step0Labels = raw3216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3216 raw3216Labels permutation434 hz
    mixedMoment B raw3216step0 raw3216step0Labels = mixedMoment B raw3216step1 raw3216step1Labels := by
      have hz : ∀ j, raw3216step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3216step1 = (fun i j => raw3216step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3216step1 raw3216step0; decide +kernel
      have hl : raw3216step1Labels = raw3216step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3216step0 raw3216step0Labels permutation80 hz
    mixedMoment B raw3216step1 raw3216step1Labels = mixedMoment B raw3216step2 raw3216step2Labels := by
      have ha : raw3216step2 = (fun i j => raw3216step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3216step2 raw3216step1; decide +kernel
      have hl : raw3216step2Labels = raw3216step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3216step1 raw3216step1Labels permutation26 permutation4
    mixedMoment B raw3216step2 raw3216step2Labels = mixedMoment B raw3216step3 raw3216step3Labels := by
      have ha : raw3216step3 = -raw3216step2 := by apply Matrix.ext; change ∀ i j, raw3216step3 i j = -(raw3216step2 i j); unfold raw3216step3 raw3216step2; decide +kernel
      have hl : raw3216step3Labels = raw3216step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3216step3 raw3216step3Labels = mixedMoment B raw3216step4 raw3216step4Labels := by
      have ha : raw3216step4 = raw3216step3 := by apply Matrix.ext; unfold raw3216step4 raw3216step3; decide +kernel
      have hl : raw3216step3Labels = labelEmbedding7 ∘ raw3216step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3216step3 raw3216step3Labels raw3216step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

theorem canonical3217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3217 raw3217Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw3217 raw3217Labels = mixedMoment B raw3217step0 raw3217step0Labels := by
      have hz : ∀ j, raw3217 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3217step0 = (fun i j => raw3217 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3217step0 raw3217; decide +kernel
      have hl : raw3217step0Labels = raw3217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3217 raw3217Labels permutation434 hz
    mixedMoment B raw3217step0 raw3217step0Labels = mixedMoment B raw3217step1 raw3217step1Labels := by
      have hz : ∀ j, raw3217step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3217step1 = (fun i j => raw3217step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3217step1 raw3217step0; decide +kernel
      have hl : raw3217step1Labels = raw3217step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3217step0 raw3217step0Labels permutation56 hz
    mixedMoment B raw3217step1 raw3217step1Labels = mixedMoment B raw3217step2 raw3217step2Labels := by
      have ha : raw3217step2 = (fun i j => raw3217step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3217step2 raw3217step1; decide +kernel
      have hl : raw3217step2Labels = raw3217step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3217step1 raw3217step1Labels permutation12 permutation3
    mixedMoment B raw3217step2 raw3217step2Labels = mixedMoment B raw3217step3 raw3217step3Labels := by
      have ha : raw3217step3 = raw3217step2 := by apply Matrix.ext; unfold raw3217step3 raw3217step2; decide +kernel
      have hl : raw3217step2Labels = labelEmbedding6 ∘ raw3217step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3217step2 raw3217step2Labels raw3217step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

theorem canonical3218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3218 raw3218Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw3218 raw3218Labels = mixedMoment B raw3218step0 raw3218step0Labels := by
      have hz : ∀ j, raw3218 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3218step0 = (fun i j => raw3218 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3218step0 raw3218; decide +kernel
      have hl : raw3218step0Labels = raw3218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3218 raw3218Labels permutation434 hz
    mixedMoment B raw3218step0 raw3218step0Labels = mixedMoment B raw3218step1 raw3218step1Labels := by
      have ha : raw3218step1 = (fun i j => raw3218step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3218step1 raw3218step0; decide +kernel
      have hl : raw3218step1Labels = raw3218step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3218step0 raw3218step0Labels permutation36 permutation3
    mixedMoment B raw3218step1 raw3218step1Labels = mixedMoment B raw3218step2 raw3218step2Labels := by
      have ha : raw3218step2 = raw3218step1 := by apply Matrix.ext; unfold raw3218step2 raw3218step1; decide +kernel
      have hl : raw3218step1Labels = labelEmbedding6 ∘ raw3218step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3218step1 raw3218step1Labels raw3218step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

theorem canonical3219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3219 raw3219Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw3219 raw3219Labels = mixedMoment B raw3219step0 raw3219step0Labels := by
      have hz : ∀ j, raw3219 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3219step0 = (fun i j => raw3219 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3219step0 raw3219; decide +kernel
      have hl : raw3219step0Labels = raw3219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3219 raw3219Labels permutation265 hz
    mixedMoment B raw3219step0 raw3219step0Labels = mixedMoment B raw3219step1 raw3219step1Labels := by
      have ha : raw3219step1 = (fun i j => raw3219step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3219step1 raw3219step0; decide +kernel
      have hl : raw3219step1Labels = raw3219step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3219step0 raw3219step0Labels permutation42 permutation3
    mixedMoment B raw3219step1 raw3219step1Labels = mixedMoment B raw3219step2 raw3219step2Labels := by
      have ha : raw3219step2 = raw3219step1 := by apply Matrix.ext; unfold raw3219step2 raw3219step1; decide +kernel
      have hl : raw3219step1Labels = labelEmbedding6 ∘ raw3219step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3219step1 raw3219step1Labels raw3219step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

theorem canonical3220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3220 raw3220Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw3220 raw3220Labels = mixedMoment B raw3220step0 raw3220step0Labels := by
      have hz : ∀ j, raw3220 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3220step0 = (fun i j => raw3220 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3220step0 raw3220; decide +kernel
      have hl : raw3220step0Labels = raw3220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3220 raw3220Labels permutation434 hz
    mixedMoment B raw3220step0 raw3220step0Labels = mixedMoment B raw3220step1 raw3220step1Labels := by
      have hz : ∀ j, raw3220step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3220step1 = (fun i j => raw3220step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3220step1 raw3220step0; decide +kernel
      have hl : raw3220step1Labels = raw3220step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3220step0 raw3220step0Labels permutation56 hz
    mixedMoment B raw3220step1 raw3220step1Labels = mixedMoment B raw3220step2 raw3220step2Labels := by
      have ha : raw3220step2 = (fun i j => raw3220step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3220step2 raw3220step1; decide +kernel
      have hl : raw3220step2Labels = raw3220step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3220step1 raw3220step1Labels permutation26 permutation4
    mixedMoment B raw3220step2 raw3220step2Labels = mixedMoment B raw3220step3 raw3220step3Labels := by
      have ha : raw3220step3 = -raw3220step2 := by apply Matrix.ext; change ∀ i j, raw3220step3 i j = -(raw3220step2 i j); unfold raw3220step3 raw3220step2; decide +kernel
      have hl : raw3220step3Labels = raw3220step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3220step3 raw3220step3Labels = mixedMoment B raw3220step4 raw3220step4Labels := by
      have ha : raw3220step4 = raw3220step3 := by apply Matrix.ext; unfold raw3220step4 raw3220step3; decide +kernel
      have hl : raw3220step3Labels = labelEmbedding7 ∘ raw3220step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3220step3 raw3220step3Labels raw3220step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

theorem canonical3221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3221 raw3221Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw3221 raw3221Labels = mixedMoment B raw3221step0 raw3221step0Labels := by
      have hz : ∀ j, raw3221 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3221step0 = (fun i j => raw3221 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3221step0 raw3221; decide +kernel
      have hl : raw3221step0Labels = raw3221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3221 raw3221Labels permutation346 hz
    mixedMoment B raw3221step0 raw3221step0Labels = mixedMoment B raw3221step1 raw3221step1Labels := by
      have hz : ∀ j, raw3221step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3221step1 = (fun i j => raw3221step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3221step1 raw3221step0; decide +kernel
      have hl : raw3221step1Labels = raw3221step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3221step0 raw3221step0Labels permutation56 hz
    mixedMoment B raw3221step1 raw3221step1Labels = mixedMoment B raw3221step2 raw3221step2Labels := by
      have ha : raw3221step2 = (fun i j => raw3221step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3221step2 raw3221step1; decide +kernel
      have hl : raw3221step2Labels = raw3221step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3221step1 raw3221step1Labels permutation12 permutation3
    mixedMoment B raw3221step2 raw3221step2Labels = mixedMoment B raw3221step3 raw3221step3Labels := by
      have ha : raw3221step3 = raw3221step2 := by apply Matrix.ext; unfold raw3221step3 raw3221step2; decide +kernel
      have hl : raw3221step2Labels = labelEmbedding6 ∘ raw3221step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3221step2 raw3221step2Labels raw3221step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

theorem canonical3222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3222 raw3222Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw3222 raw3222Labels = mixedMoment B raw3222step0 raw3222step0Labels := by
      have hz : ∀ j, raw3222 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3222step0 = (fun i j => raw3222 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3222step0 raw3222; decide +kernel
      have hl : raw3222step0Labels = raw3222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3222 raw3222Labels permutation346 hz
    mixedMoment B raw3222step0 raw3222step0Labels = mixedMoment B raw3222step1 raw3222step1Labels := by
      have ha : raw3222step1 = (fun i j => raw3222step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3222step1 raw3222step0; decide +kernel
      have hl : raw3222step1Labels = raw3222step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3222step0 raw3222step0Labels permutation36 permutation3
    mixedMoment B raw3222step1 raw3222step1Labels = mixedMoment B raw3222step2 raw3222step2Labels := by
      have ha : raw3222step2 = raw3222step1 := by apply Matrix.ext; unfold raw3222step2 raw3222step1; decide +kernel
      have hl : raw3222step1Labels = labelEmbedding6 ∘ raw3222step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3222step1 raw3222step1Labels raw3222step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

theorem canonical3223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3223 raw3223Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw3223 raw3223Labels = mixedMoment B raw3223step0 raw3223step0Labels := by
      have hz : ∀ j, raw3223 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3223step0 = (fun i j => raw3223 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3223step0 raw3223; decide +kernel
      have hl : raw3223step0Labels = raw3223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3223 raw3223Labels permutation265 hz
    mixedMoment B raw3223step0 raw3223step0Labels = mixedMoment B raw3223step1 raw3223step1Labels := by
      have ha : raw3223step1 = (fun i j => raw3223step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3223step1 raw3223step0; decide +kernel
      have hl : raw3223step1Labels = raw3223step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3223step0 raw3223step0Labels permutation36 permutation3
    mixedMoment B raw3223step1 raw3223step1Labels = mixedMoment B raw3223step2 raw3223step2Labels := by
      have ha : raw3223step2 = raw3223step1 := by apply Matrix.ext; unfold raw3223step2 raw3223step1; decide +kernel
      have hl : raw3223step1Labels = labelEmbedding6 ∘ raw3223step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3223step1 raw3223step1Labels raw3223step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

theorem canonical3224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3224 raw3224Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw3224 raw3224Labels = mixedMoment B raw3224step0 raw3224step0Labels := by
      have hz : ∀ j, raw3224 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3224step0 = (fun i j => raw3224 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3224step0 raw3224; decide +kernel
      have hl : raw3224step0Labels = raw3224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3224 raw3224Labels permutation346 hz
    mixedMoment B raw3224step0 raw3224step0Labels = mixedMoment B raw3224step1 raw3224step1Labels := by
      have hz : ∀ j, raw3224step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3224step1 = (fun i j => raw3224step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3224step1 raw3224step0; decide +kernel
      have hl : raw3224step1Labels = raw3224step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3224step0 raw3224step0Labels permutation56 hz
    mixedMoment B raw3224step1 raw3224step1Labels = mixedMoment B raw3224step2 raw3224step2Labels := by
      have ha : raw3224step2 = (fun i j => raw3224step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3224step2 raw3224step1; decide +kernel
      have hl : raw3224step2Labels = raw3224step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3224step1 raw3224step1Labels permutation26 permutation4
    mixedMoment B raw3224step2 raw3224step2Labels = mixedMoment B raw3224step3 raw3224step3Labels := by
      have ha : raw3224step3 = -raw3224step2 := by apply Matrix.ext; change ∀ i j, raw3224step3 i j = -(raw3224step2 i j); unfold raw3224step3 raw3224step2; decide +kernel
      have hl : raw3224step3Labels = raw3224step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3224step3 raw3224step3Labels = mixedMoment B raw3224step4 raw3224step4Labels := by
      have ha : raw3224step4 = raw3224step3 := by apply Matrix.ext; unfold raw3224step4 raw3224step3; decide +kernel
      have hl : raw3224step3Labels = labelEmbedding7 ∘ raw3224step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3224step3 raw3224step3Labels raw3224step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

theorem canonical3225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3225 raw3225Labels = mixedMoment B node5305 node5305Labels := by
  calc
    mixedMoment B raw3225 raw3225Labels = mixedMoment B raw3225step0 raw3225step0Labels := by
      have hz : ∀ j, raw3225 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3225step0 = (fun i j => raw3225 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3225step0 raw3225; decide +kernel
      have hl : raw3225step0Labels = raw3225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3225 raw3225Labels permutation434 hz
    mixedMoment B raw3225step0 raw3225step0Labels = mixedMoment B raw3225step1 raw3225step1Labels := by
      have hz : ∀ j, raw3225step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3225step1 = (fun i j => raw3225step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3225step1 raw3225step0; decide +kernel
      have hl : raw3225step1Labels = raw3225step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3225step0 raw3225step0Labels permutation80 hz
    mixedMoment B raw3225step1 raw3225step1Labels = mixedMoment B raw3225step2 raw3225step2Labels := by
      have hz : ∀ j, raw3225step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3225step2 = (fun i j => raw3225step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3225step2 raw3225step1; decide +kernel
      have hl : raw3225step2Labels = raw3225step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3225step1 raw3225step1Labels permutation14 hz
    mixedMoment B raw3225step2 raw3225step2Labels = mixedMoment B raw3225step3 raw3225step3Labels := by
      have ha : raw3225step3 = (fun i j => raw3225step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3225step3 raw3225step2; decide +kernel
      have hl : raw3225step3Labels = raw3225step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3225step2 raw3225step2Labels permutation3 permutation3
    mixedMoment B raw3225step3 raw3225step3Labels = mixedMoment B raw3225step4 raw3225step4Labels := by
      have ha : raw3225step4 = raw3225step3 := by apply Matrix.ext; unfold raw3225step4 raw3225step3; decide +kernel
      have hl : raw3225step3Labels = labelEmbedding6 ∘ raw3225step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3225step3 raw3225step3Labels raw3225step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5305 node5305Labels := by rfl

theorem canonical3226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3226 raw3226Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw3226 raw3226Labels = mixedMoment B raw3226step0 raw3226step0Labels := by
      have hz : ∀ j, raw3226 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3226step0 = (fun i j => raw3226 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3226step0 raw3226; decide +kernel
      have hl : raw3226step0Labels = raw3226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3226 raw3226Labels permutation434 hz
    mixedMoment B raw3226step0 raw3226step0Labels = mixedMoment B raw3226step1 raw3226step1Labels := by
      have hz : ∀ j, raw3226step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3226step1 = (fun i j => raw3226step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3226step1 raw3226step0; decide +kernel
      have hl : raw3226step1Labels = raw3226step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3226step0 raw3226step0Labels permutation80 hz
    mixedMoment B raw3226step1 raw3226step1Labels = mixedMoment B raw3226step2 raw3226step2Labels := by
      have ha : raw3226step2 = (fun i j => raw3226step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3226step2 raw3226step1; decide +kernel
      have hl : raw3226step2Labels = raw3226step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3226step1 raw3226step1Labels permutation25 permutation5
    mixedMoment B raw3226step2 raw3226step2Labels = mixedMoment B raw3226step3 raw3226step3Labels := by
      have ha : raw3226step3 = raw3226step2 := by apply Matrix.ext; unfold raw3226step3 raw3226step2; decide +kernel
      have hl : raw3226step2Labels = labelEmbedding8 ∘ raw3226step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3226step2 raw3226step2Labels raw3226step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

theorem canonical3227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3227 raw3227Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw3227 raw3227Labels = mixedMoment B raw3227step0 raw3227step0Labels := by
      have hz : ∀ j, raw3227 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3227step0 = (fun i j => raw3227 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3227step0 raw3227; decide +kernel
      have hl : raw3227step0Labels = raw3227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3227 raw3227Labels permutation434 hz
    mixedMoment B raw3227step0 raw3227step0Labels = mixedMoment B raw3227step1 raw3227step1Labels := by
      have hz : ∀ j, raw3227step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3227step1 = (fun i j => raw3227step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3227step1 raw3227step0; decide +kernel
      have hl : raw3227step1Labels = raw3227step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3227step0 raw3227step0Labels permutation56 hz
    mixedMoment B raw3227step1 raw3227step1Labels = mixedMoment B raw3227step2 raw3227step2Labels := by
      have ha : raw3227step2 = (fun i j => raw3227step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3227step2 raw3227step1; decide +kernel
      have hl : raw3227step2Labels = raw3227step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3227step1 raw3227step1Labels permutation25 permutation5
    mixedMoment B raw3227step2 raw3227step2Labels = mixedMoment B raw3227step3 raw3227step3Labels := by
      have ha : raw3227step3 = raw3227step2 := by apply Matrix.ext; unfold raw3227step3 raw3227step2; decide +kernel
      have hl : raw3227step2Labels = labelEmbedding8 ∘ raw3227step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3227step2 raw3227step2Labels raw3227step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

theorem canonical3228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3228 raw3228Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw3228 raw3228Labels = mixedMoment B raw3228step0 raw3228step0Labels := by
      have hz : ∀ j, raw3228 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3228step0 = (fun i j => raw3228 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3228step0 raw3228; decide +kernel
      have hl : raw3228step0Labels = raw3228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3228 raw3228Labels permutation346 hz
    mixedMoment B raw3228step0 raw3228step0Labels = mixedMoment B raw3228step1 raw3228step1Labels := by
      have hz : ∀ j, raw3228step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3228step1 = (fun i j => raw3228step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3228step1 raw3228step0; decide +kernel
      have hl : raw3228step1Labels = raw3228step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3228step0 raw3228step0Labels permutation56 hz
    mixedMoment B raw3228step1 raw3228step1Labels = mixedMoment B raw3228step2 raw3228step2Labels := by
      have ha : raw3228step2 = (fun i j => raw3228step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3228step2 raw3228step1; decide +kernel
      have hl : raw3228step2Labels = raw3228step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3228step1 raw3228step1Labels permutation25 permutation5
    mixedMoment B raw3228step2 raw3228step2Labels = mixedMoment B raw3228step3 raw3228step3Labels := by
      have ha : raw3228step3 = raw3228step2 := by apply Matrix.ext; unfold raw3228step3 raw3228step2; decide +kernel
      have hl : raw3228step2Labels = labelEmbedding8 ∘ raw3228step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3228step2 raw3228step2Labels raw3228step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

theorem canonical3229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3229 raw3229Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw3229 raw3229Labels = mixedMoment B raw3229step0 raw3229step0Labels := by
      have hz : ∀ j, raw3229 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3229step0 = (fun i j => raw3229 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3229step0 raw3229; decide +kernel
      have hl : raw3229step0Labels = raw3229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3229 raw3229Labels permutation434 hz
    mixedMoment B raw3229step0 raw3229step0Labels = mixedMoment B raw3229step1 raw3229step1Labels := by
      have hz : ∀ j, raw3229step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3229step1 = (fun i j => raw3229step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3229step1 raw3229step0; decide +kernel
      have hl : raw3229step1Labels = raw3229step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3229step0 raw3229step0Labels permutation80 hz
    mixedMoment B raw3229step1 raw3229step1Labels = mixedMoment B raw3229step2 raw3229step2Labels := by
      have hz : ∀ j, raw3229step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3229step2 = (fun i j => raw3229step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3229step2 raw3229step1; decide +kernel
      have hl : raw3229step2Labels = raw3229step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3229step1 raw3229step1Labels permutation14 hz
    mixedMoment B raw3229step2 raw3229step2Labels = mixedMoment B raw3229step3 raw3229step3Labels := by
      have ha : raw3229step3 = (fun i j => raw3229step2 (permutation4 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3229step3 raw3229step2; decide +kernel
      have hl : raw3229step3Labels = raw3229step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3229step2 raw3229step2Labels permutation4 permutation5
    mixedMoment B raw3229step3 raw3229step3Labels = mixedMoment B raw3229step4 raw3229step4Labels := by
      have ha : raw3229step4 = raw3229step3 := by apply Matrix.ext; unfold raw3229step4 raw3229step3; decide +kernel
      have hl : raw3229step3Labels = labelEmbedding8 ∘ raw3229step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3229step3 raw3229step3Labels raw3229step4Labels labelEmbedding8 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

theorem canonical3230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3230 raw3230Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw3230 raw3230Labels = mixedMoment B raw3230step0 raw3230step0Labels := by
      have hz : ∀ j, raw3230 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3230step0 = (fun i j => raw3230 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3230step0 raw3230; decide +kernel
      have hl : raw3230step0Labels = raw3230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3230 raw3230Labels permutation434 hz
    mixedMoment B raw3230step0 raw3230step0Labels = mixedMoment B raw3230step1 raw3230step1Labels := by
      have hz : ∀ j, raw3230step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3230step1 = (fun i j => raw3230step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3230step1 raw3230step0; decide +kernel
      have hl : raw3230step1Labels = raw3230step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3230step0 raw3230step0Labels permutation80 hz
    mixedMoment B raw3230step1 raw3230step1Labels = mixedMoment B raw3230step2 raw3230step2Labels := by
      have hz : ∀ j, raw3230step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3230step2 = (fun i j => raw3230step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3230step2 raw3230step1; decide +kernel
      have hl : raw3230step2Labels = raw3230step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3230step1 raw3230step1Labels permutation14 hz
    mixedMoment B raw3230step2 raw3230step2Labels = mixedMoment B raw3230step3 raw3230step3Labels := by
      have ha : raw3230step3 = (fun i j => raw3230step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3230step3 raw3230step2; decide +kernel
      have hl : raw3230step3Labels = raw3230step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3230step2 raw3230step2Labels permutation7 permutation2
    mixedMoment B raw3230step3 raw3230step3Labels = mixedMoment B raw3230step4 raw3230step4Labels := by
      have ha : raw3230step4 = -raw3230step3 := by apply Matrix.ext; change ∀ i j, raw3230step4 i j = -(raw3230step3 i j); unfold raw3230step4 raw3230step3; decide +kernel
      have hl : raw3230step4Labels = raw3230step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5455 node5455Labels := by rfl

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

theorem canonical544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw544 raw544Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw544 raw544Labels = mixedMoment B raw544step0 raw544step0Labels := by
      have ha : raw544step0 = (fun i j => raw544 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw544step0 raw544; decide +kernel
      have hl : raw544step0Labels = raw544Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw544 raw544Labels permutation8 permutation5
    mixedMoment B raw544step0 raw544step0Labels = mixedMoment B raw544step1 raw544step1Labels := by
      have ha : raw544step1 = raw544step0 := by apply Matrix.ext; unfold raw544step1 raw544step0; decide +kernel
      have hl : raw544step0Labels = labelEmbedding1 ∘ raw544step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw544step0 raw544step0Labels raw544step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3888 node3888Labels := by rfl

theorem canonical545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw545 raw545Labels = mixedMoment B node503 node503Labels := by
  calc
    mixedMoment B raw545 raw545Labels = mixedMoment B raw545step0 raw545step0Labels := by
      have ha : raw545step0 = (fun i j => raw545 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw545step0 raw545; decide +kernel
      have hl : raw545step0Labels = raw545Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw545 raw545Labels permutation8 permutation5
    _ = mixedMoment B node503 node503Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical124
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3978 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3978 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw3978 = injectiveMoment H raw3978step0 := by
      have heq : raw3978step0 = -raw3978 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3978).symm
    injectiveMoment H raw3978step0 = injectiveMoment H raw3978step1 := by
      have heq : raw3978step1 = (fun i j => raw3978step0 (permutation11 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3978step0 permutation11 permutation8
    _ = injectiveMoment H node210 := by rfl

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

theorem canonical4159 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4159 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw4159 = injectiveMoment H raw4159step0 := by
      have heq : raw4159step0 = -raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4159).symm
    injectiveMoment H raw4159step0 = injectiveMoment H raw4159step1 := by
      have heq : raw4159step1 = (fun i j => raw4159step0 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4159step0 permutation7 permutation5
    _ = injectiveMoment H node36 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical280
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8979 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw8979 = injectiveMoment H raw8979step0 := by
      have hz : ∀ j, raw8979 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8979step0 = (fun i j => raw8979 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8979 permutation9 hz
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

theorem sound44 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node44 = Sparse.eval value44 (momentVector H) := by
  have hc : momentVector H 4 = injectiveMoment H node44 := rfl
  simp [value44, Sparse.eval, hc]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4966 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4966 = injectiveMoment H node44 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4160 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4160 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4160 = injectiveMoment H raw4160step0 := by
      have heq : raw4160step0 = -raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4160).symm
    injectiveMoment H raw4160step0 = injectiveMoment H raw4160step1 := by
      have heq : raw4160step1 = (fun i j => raw4160step0 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4160step0 permutation7 permutation5
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

theorem sound210 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node210 = Sparse.eval value210 (momentVector H) := by
  have heq : pivotMatrix210 = (fun u v => node210 (pivotPermutation210 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node210 = injectiveMoment H pivotMatrix210 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix210 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix210 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix210 (0 : Fin 3)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix210 (0 : Fin 3) = raw4966 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4966 hH).trans (sound44 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix210 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix210 (1 : Fin 3) = raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4160 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix210 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix210 (2 : Fin 3) = raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4159 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node210 + (injectiveMoment H (mergeFirst pivotMatrix210 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix210 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix210 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value210, value36, value44, value62, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair503 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node503 node503Labels = Sparse.eval singlePairValue503 (familyPairVector B) := by
  have hp := single_label_three B hB node503
  have hl : node503Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node503 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node503 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node503 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node503 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node503 (EqualityPatterns.family3.label 1) = PairSemantics.raw5197 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node503 PairSemantics.raw5197; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5197 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node503 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node503 (EqualityPatterns.family3.label 2) = PairSemantics.raw8979 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node503 PairSemantics.raw8979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8979 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node503 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node503 (EqualityPatterns.family3.label 3) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node503 PairSemantics.raw5141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node503 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value210 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node503 (EqualityPatterns.family3.label 4) = PairSemantics.raw3978 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node503 PairSemantics.raw3978; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3978 hH).trans (PairSemantics.sound210 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue503, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value210, Sparse.eval] at hp ⊢
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

theorem singleton3888 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3888 node3888Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node503 node503Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw544 singletonSmall3888
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3888) = raw544Labels := by decide +kernel
  rw [hl, canonical544 B hB] at h
  have hc0 : mixedMoment B raw544 (Fin.cases (0 : Fin 1) singletonSmall3888) =
      mixedMoment B node503 node503Labels := by
    have ha : raw544 = raw545 := by apply Matrix.ext; unfold raw544 raw545; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3888 = raw545Labels := by decide +kernel
    rw [ha, hj, canonical545 B hB]
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

theorem singleton5305 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5305 node5305Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2783 node2783Labels + mixedMoment B node2783 node2783Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2319 singletonSmall5305
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5305) = raw2319Labels := by decide +kernel
  rw [hl, canonical2319 B hB] at h
  have hc0 : mixedMoment B raw2319 (Fin.cases (0 : Fin 2) singletonSmall5305) =
      mixedMoment B node2783 node2783Labels := by
    have ha : raw2319 = raw2320 := by apply Matrix.ext; unfold raw2319 raw2320; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5305 = raw2320Labels := by decide +kernel
    rw [ha, hj, canonical2320 B hB]
  have hc1 : mixedMoment B raw2319 (Fin.cases (1 : Fin 2) singletonSmall5305) =
      mixedMoment B node2783 node2783Labels := by
    have ha : raw2319 = raw2321 := by apply Matrix.ext; unfold raw2319 raw2321; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5305 = raw2321Labels := by decide +kernel
    rw [ha, hj, canonical2321 B hB]
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

theorem singleton5451 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5451 node5451Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3888 node3888Labels + mixedMoment B node3913 node3913Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2559 singletonSmall5451
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5451) = raw2559Labels := by decide +kernel
  rw [hl, canonical2559 B hB] at h
  have hc0 : mixedMoment B raw2559 (Fin.cases (0 : Fin 2) singletonSmall5451) =
      mixedMoment B node3888 node3888Labels := by
    have ha : raw2559 = raw2560 := by apply Matrix.ext; unfold raw2559 raw2560; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5451 = raw2560Labels := by decide +kernel
    rw [ha, hj, canonical2560 B hB]
  have hc1 : mixedMoment B raw2559 (Fin.cases (1 : Fin 2) singletonSmall5451) =
      mixedMoment B node3913 node3913Labels := by
    have ha : raw2559 = raw2561 := by apply Matrix.ext; unfold raw2559 raw2561; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5451 = raw2561Labels := by decide +kernel
    rw [ha, hj, canonical2561 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5484 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5484 node5484Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3983 node3983Labels + mixedMoment B node3983 node3983Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2607 singletonSmall5484
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5484) = raw2607Labels := by decide +kernel
  rw [hl, canonical2607 B hB] at h
  have hc0 : mixedMoment B raw2607 (Fin.cases (0 : Fin 2) singletonSmall5484) =
      mixedMoment B node3983 node3983Labels := by
    have ha : raw2607 = raw2608 := by apply Matrix.ext; unfold raw2607 raw2608; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5484 = raw2608Labels := by decide +kernel
    rw [ha, hj, canonical2608 B hB]
  have hc1 : mixedMoment B raw2607 (Fin.cases (1 : Fin 2) singletonSmall5484) =
      mixedMoment B node3983 node3983Labels := by
    have ha : raw2607 = raw2609 := by apply Matrix.ext; unfold raw2607 raw2609; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5484 = raw2609Labels := by decide +kernel
    rw [ha, hj, canonical2609 B hB]
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

theorem zero5455 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5455 node5455Labels = 0 := by
  exact mixedMoment_order_one B hB node5455 node5455Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5495 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5495 node5495Labels = 0 := by
  exact mixedMoment_order_one B hB node5495 node5495Labels 1
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

theorem sound5310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5310 node5310Labels = Sparse.eval nodeValue5310 (mixedVector B) := by
  have h := singleton5310 B _hB
  rw [sound2788 B _hB _hF, sound3633 B _hB _hF] at h
  norm_num [nodeValue5310, nodeValue2788, nodeValue3633, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5455 node5455Labels = Sparse.eval nodeValue5455 (mixedVector B) := by
  simpa only [nodeValue5455, Sparse.eval_nil] using zero5455 B _hB _hF

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

theorem sound2782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2782 node2782Labels = Sparse.eval nodeValue2782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2782) = mixedMoment B node2782 node2782Labels := rfl
  simpa [nodeValue2782, Sparse.eval] using hc.symm

theorem sound2783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2783 node2783Labels = Sparse.eval nodeValue2783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2783) = mixedMoment B node2783 node2783Labels := rfl
  simpa [nodeValue2783, Sparse.eval] using hc.symm

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

theorem sound3583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3583 node3583Labels = Sparse.eval nodeValue3583 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3583) = mixedMoment B node3583 node3583Labels := rfl
  simpa [nodeValue3583, Sparse.eval] using hc.symm

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

theorem sound503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node503 node503Labels = Sparse.eval nodeValue503 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue503 (familyPairVector B) := singlePair503 B _hB
    _ = _ := by norm_num [singlePairValue503, nodeValue503, Sparse.eval, mixedVector] <;> ring

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

theorem sound3888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3888 node3888Labels = Sparse.eval nodeValue3888 (mixedVector B) := by
  have h := singleton3888 B _hB
  rw [sound503 B _hB _hF] at h
  norm_num [nodeValue3888, nodeValue503, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound3913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3913 node3913Labels = Sparse.eval nodeValue3913 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3913) = mixedMoment B node3913 node3913Labels := rfl
  simpa [nodeValue3913, Sparse.eval] using hc.symm

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

theorem sound3983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3983 node3983Labels = Sparse.eval nodeValue3983 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3983) = mixedMoment B node3983 node3983Labels := rfl
  simpa [nodeValue3983, Sparse.eval] using hc.symm

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

theorem sound5304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5304 node5304Labels = Sparse.eval nodeValue5304 (mixedVector B) := by
  have h := singleton5304 B _hB
  rw [sound2782 B _hB _hF, sound3583 B _hB _hF] at h
  norm_num [nodeValue5304, nodeValue2782, nodeValue3583, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5305 node5305Labels = Sparse.eval nodeValue5305 (mixedVector B) := by
  have h := singleton5305 B _hB
  rw [sound2783 B _hB _hF] at h
  norm_num [nodeValue5305, nodeValue2783, Sparse.eval] at h ⊢
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

theorem sound5451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5451 node5451Labels = Sparse.eval nodeValue5451 (mixedVector B) := by
  have h := singleton5451 B _hB
  rw [sound3888 B _hB _hF, sound3913 B _hB _hF] at h
  norm_num [nodeValue5451, nodeValue3888, nodeValue3913, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5484 node5484Labels = Sparse.eval nodeValue5484 (mixedVector B) := by
  have h := singleton5484 B _hB
  rw [sound3983 B _hB _hF] at h
  norm_num [nodeValue5484, nodeValue3983, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5495 node5495Labels = Sparse.eval nodeValue5495 (mixedVector B) := by
  simpa only [nodeValue5495, Sparse.eval_nil] using zero5495 B _hB _hF

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

theorem sourceEq21 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm21 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA21 + difference 0 1) (sourceB21 + difference 1 0) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA21 + difference 0 1) (sourceB21 + difference 1 0) sourceC21) = raw3209 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3209; decide +kernel
    rw [ha]
    exact (canonical3209 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA21 + difference 0 2) (sourceB21 + difference 2 0) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA21 + difference 0 2) (sourceB21 + difference 2 0) sourceC21) = raw3210 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3210; decide +kernel
    rw [ha]
    exact (canonical3210 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA21 + difference 0 3) (sourceB21 + difference 3 0) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA21 + difference 0 3) (sourceB21 + difference 3 0) sourceC21) = raw3211 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3211; decide +kernel
    rw [ha]
    exact (canonical3211 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA21 + difference 0 4) (sourceB21 + difference 4 0) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5495) := by
    have ha : (tripleCharges (sourceA21 + difference 0 4) (sourceB21 + difference 4 0) sourceC21) = raw2855 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw2855; decide +kernel
    rw [ha]
    exact (canonical2855 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA21 + difference 0 5) (sourceB21 + difference 5 0) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA21 + difference 0 5) (sourceB21 + difference 5 0) sourceC21) = raw3212 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3212; decide +kernel
    rw [ha]
    exact (canonical3212 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA21 + difference 1 0) (sourceB21 + difference 0 1) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA21 + difference 1 0) (sourceB21 + difference 0 1) sourceC21) = raw3213 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3213; decide +kernel
    rw [ha]
    exact (canonical3213 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA21 + difference 1 2) (sourceB21 + difference 2 1) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA21 + difference 1 2) (sourceB21 + difference 2 1) sourceC21) = raw3214 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3214; decide +kernel
    rw [ha]
    exact (canonical3214 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA21 + difference 1 3) (sourceB21 + difference 3 1) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA21 + difference 1 3) (sourceB21 + difference 3 1) sourceC21) = raw3215 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3215; decide +kernel
    rw [ha]
    exact (canonical3215 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA21 + difference 1 4) (sourceB21 + difference 4 1) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA21 + difference 1 4) (sourceB21 + difference 4 1) sourceC21) = raw2860 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw2860; decide +kernel
    rw [ha]
    exact (canonical2860 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA21 + difference 1 5) (sourceB21 + difference 5 1) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA21 + difference 1 5) (sourceB21 + difference 5 1) sourceC21) = raw3216 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3216; decide +kernel
    rw [ha]
    exact (canonical3216 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA21 + difference 2 0) (sourceB21 + difference 0 2) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA21 + difference 2 0) (sourceB21 + difference 0 2) sourceC21) = raw3217 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3217; decide +kernel
    rw [ha]
    exact (canonical3217 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA21 + difference 2 1) (sourceB21 + difference 1 2) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA21 + difference 2 1) (sourceB21 + difference 1 2) sourceC21) = raw3218 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3218; decide +kernel
    rw [ha]
    exact (canonical3218 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA21 + difference 2 3) (sourceB21 + difference 3 2) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA21 + difference 2 3) (sourceB21 + difference 3 2) sourceC21) = raw3219 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3219; decide +kernel
    rw [ha]
    exact (canonical3219 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA21 + difference 2 4) (sourceB21 + difference 4 2) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA21 + difference 2 4) (sourceB21 + difference 4 2) sourceC21) = raw2865 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw2865; decide +kernel
    rw [ha]
    exact (canonical2865 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA21 + difference 2 5) (sourceB21 + difference 5 2) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA21 + difference 2 5) (sourceB21 + difference 5 2) sourceC21) = raw3220 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3220; decide +kernel
    rw [ha]
    exact (canonical3220 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA21 + difference 3 0) (sourceB21 + difference 0 3) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA21 + difference 3 0) (sourceB21 + difference 0 3) sourceC21) = raw3221 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3221; decide +kernel
    rw [ha]
    exact (canonical3221 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA21 + difference 3 1) (sourceB21 + difference 1 3) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA21 + difference 3 1) (sourceB21 + difference 1 3) sourceC21) = raw3222 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3222; decide +kernel
    rw [ha]
    exact (canonical3222 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA21 + difference 3 2) (sourceB21 + difference 2 3) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA21 + difference 3 2) (sourceB21 + difference 2 3) sourceC21) = raw3223 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3223; decide +kernel
    rw [ha]
    exact (canonical3223 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA21 + difference 3 4) (sourceB21 + difference 4 3) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA21 + difference 3 4) (sourceB21 + difference 4 3) sourceC21) = raw2870 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw2870; decide +kernel
    rw [ha]
    exact (canonical2870 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA21 + difference 3 5) (sourceB21 + difference 5 3) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA21 + difference 3 5) (sourceB21 + difference 5 3) sourceC21) = raw3224 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3224; decide +kernel
    rw [ha]
    exact (canonical3224 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA21 + difference 4 0) (sourceB21 + difference 0 4) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5305) := by
    have ha : (tripleCharges (sourceA21 + difference 4 0) (sourceB21 + difference 0 4) sourceC21) = raw3225 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3225; decide +kernel
    rw [ha]
    exact (canonical3225 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA21 + difference 4 1) (sourceB21 + difference 1 4) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA21 + difference 4 1) (sourceB21 + difference 1 4) sourceC21) = raw3226 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3226; decide +kernel
    rw [ha]
    exact (canonical3226 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA21 + difference 4 2) (sourceB21 + difference 2 4) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA21 + difference 4 2) (sourceB21 + difference 2 4) sourceC21) = raw3227 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3227; decide +kernel
    rw [ha]
    exact (canonical3227 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA21 + difference 4 3) (sourceB21 + difference 3 4) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA21 + difference 4 3) (sourceB21 + difference 3 4) sourceC21) = raw3228 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3228; decide +kernel
    rw [ha]
    exact (canonical3228 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA21 + difference 4 5) (sourceB21 + difference 5 4) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA21 + difference 4 5) (sourceB21 + difference 5 4) sourceC21) = raw3229 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3229; decide +kernel
    rw [ha]
    exact (canonical3229 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA21 + difference 5 0) (sourceB21 + difference 0 5) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA21 + difference 5 0) (sourceB21 + difference 0 5) sourceC21) = raw2871 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw2871; decide +kernel
    rw [ha]
    exact (canonical2871 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA21 + difference 5 1) (sourceB21 + difference 1 5) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA21 + difference 5 1) (sourceB21 + difference 1 5) sourceC21) = raw2872 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw2872; decide +kernel
    rw [ha]
    exact (canonical2872 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA21 + difference 5 2) (sourceB21 + difference 2 5) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA21 + difference 5 2) (sourceB21 + difference 2 5) sourceC21) = raw2873 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw2873; decide +kernel
    rw [ha]
    exact (canonical2873 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA21 + difference 5 3) (sourceB21 + difference 3 5) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA21 + difference 5 3) (sourceB21 + difference 3 5) sourceC21) = raw2874 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw2874; decide +kernel
    rw [ha]
    exact (canonical2874 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA21 + difference 5 4) (sourceB21 + difference 4 5) sourceC21) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA21 + difference 5 4) (sourceB21 + difference 4 5) sourceC21) = raw3230 := by
      apply Matrix.ext; unfold tripleCharges sourceA21 sourceB21 sourceC21 difference raw3230; decide +kernel
    rw [ha]
    exact (canonical3230 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA21 sourceB21 sourceC21
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm21, Integer.Sparse.eval]
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

theorem reindexCheck21 : Integer.Sparse.reindex keyMap MixedData.row21 = numericRow21 := by decide +kernel

theorem numericCheck21 (x : Master → ℝ) : Integer.Sparse.eval numericRow21 x =
    (480 : ℝ) * reducedSource21 x := by
  norm_num [numericRow21, reducedSource21, Integer.Sparse.eval, Sparse.eval, nodeValue5304, nodeValue5305, nodeValue5310, nodeValue5451, nodeValue5455, nodeValue5484, nodeValue5492, nodeValue5495]
  ring

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

theorem reducedZero21 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource21 (mixedVector B) = 0 := by
  have h5304 : mixedVector B (Sum.inr 5304) = Sparse.eval nodeValue5304 (mixedVector B) := by
    change mixedMoment B node5304 node5304Labels = _
    exact sound5304 B hB hF
  have h5305 : mixedVector B (Sum.inr 5305) = Sparse.eval nodeValue5305 (mixedVector B) := by
    change mixedMoment B node5305 node5305Labels = _
    exact sound5305 B hB hF
  have h5310 : mixedVector B (Sum.inr 5310) = Sparse.eval nodeValue5310 (mixedVector B) := by
    change mixedMoment B node5310 node5310Labels = _
    exact sound5310 B hB hF
  have h5451 : mixedVector B (Sum.inr 5451) = Sparse.eval nodeValue5451 (mixedVector B) := by
    change mixedMoment B node5451 node5451Labels = _
    exact sound5451 B hB hF
  have h5455 : mixedVector B (Sum.inr 5455) = Sparse.eval nodeValue5455 (mixedVector B) := by
    change mixedMoment B node5455 node5455Labels = _
    exact sound5455 B hB hF
  have h5484 : mixedVector B (Sum.inr 5484) = Sparse.eval nodeValue5484 (mixedVector B) := by
    change mixedMoment B node5484 node5484Labels = _
    exact sound5484 B hB hF
  have h5492 : mixedVector B (Sum.inr 5492) = Sparse.eval nodeValue5492 (mixedVector B) := by
    change mixedMoment B node5492 node5492Labels = _
    exact sound5492_e B hB hF
  have h5495 : mixedVector B (Sum.inr 5495) = Sparse.eval nodeValue5495 (mixedVector B) := by
    change mixedMoment B node5495 node5495Labels = _
    exact sound5495 B hB hF
  simpa only [sourceForm21, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5304, h5305, h5310, h5451, h5455, h5484, h5492, h5495, reducedSource21] using sourceEq21 B hB

theorem rowSound21_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row21 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck21, numericCheck21, reducedZero21 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound21_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound21_e_oai
